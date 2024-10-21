import rlp
from google.cloud import bigtable
from typing import Any, List
from google.cloud.bigtable.batcher import MutationsBatcher

from util import *

COLUMN_FAMILY_ID = "data"

"""
Create tables and column families if they don't exist before
Right now we fix each table to have one column family called "data"
"""
def create_tables(project_id: str, instance_id: str, table_ids: List[str]):
    client = bigtable.Client(project=project_id, admin=True)
    instance = client.instance(instance_id)
    tables = []

    for table_id in table_ids:
        table = instance.table(table_id)
        if not table.exists():
            logging.warning(f"Table '{table_id}' does not exist. Creating table...")
            table.create()

        existing_cfs = table.list_column_families().keys()

        if COLUMN_FAMILY_ID not in existing_cfs:
            logging.warning(
                f"Column family '{COLUMN_FAMILY_ID}' does not exist in table '{table_id}'. Creating..."
            )
            cf_obj = table.column_family(COLUMN_FAMILY_ID)
            cf_obj.create()

        tables.append(table)

    return tables


def insert_block_into_tx_tables(
    transactions: List[Any],
    block_number: int,
    tx_hash_table: bigtable.table,
    tx_index_table: bigtable.table,
) -> None:
    tx_datas = []
    tx_hashes = []
    tx_indexes = []

    for tx_num, tx in enumerate(transactions):
        # re-encoding because individual fields are decoded
        tx_data = rlp.encode(tx)
        tx_hash = compute_hash(tx_data)

        """generate joint index <block_number>_<tx_number>"""
        block_padded = pad_number(block_number, BLOCK_NUM_PAD)
        tx_padded = pad_number(tx_num, TX_NUM_PAD)
        tx_index = f"{block_padded}_{tx_padded}"

        tx_datas.append(tx_data)
        tx_hashes.append(tx_hash)
        tx_indexes.append(tx_index)

    logging.info(f"Inserting block {block_number} into 'tx_hash' table")
    with MutationsBatcher(table=tx_hash_table) as batcher:
        hash_table_rows = []
        for i in range(len(transactions)):
            hash_table_tx_row_key = tx_hashes[i]
            hash_table_tx_row = tx_hash_table.row(hash_table_tx_row_key)
            hash_table_tx_row.set_cell(COLUMN_FAMILY_ID, "tx_index", tx_indexes[i])
            hash_table_tx_row.set_cell(COLUMN_FAMILY_ID, "tx_data", tx_datas[i])

            hash_table_rows.append(hash_table_tx_row)

            logging.debug(
                f"Adding tx {tx_num} of block {block_number} hash={tx_hash} into 'tx_hash' table"
            )

        batcher.mutate_rows(hash_table_rows)
        logging.info(
            f"Successfully wrote {str(len(transactions))} rows for block {block_number} into 'tx_hash' table"
        )

    logging.info(f"Inserting block {block_number} into 'tx_index' table")
    with MutationsBatcher(table=tx_index_table) as batcher:
        index_table_rows = []
        for i in range(len(transactions)):
            index_table_tx_row_key = tx_indexes[i]
            index_table_tx_row = tx_index_table.row(index_table_tx_row_key)
            index_table_tx_row.set_cell(COLUMN_FAMILY_ID, "tx_hash", tx_hashes[i])

            index_table_rows.append(index_table_tx_row)

            logging.debug(
                f"Adding tx {tx_num} of block {block_number} hash={tx_hash} into 'tx_index' table"
            )

        batcher.mutate_rows(index_table_rows)
        logging.info(
            f"Successfully wrote {str(len(transactions))} rows for block {block_number} into 'tx_index' table"
        )


def insert_block_into_block_tables(
    block_header: Any,
    block: bytes,
    block_number: int,
    block_hash_table: bigtable.table,
    block_index_table: bigtable.table,
) -> None:

    block_hash = compute_hash(block)

    """Block Hash Table"""
    logging.info(f"Inserting block {block_number} into 'block_hash' table")

    hash_table_row_key = block_hash
    hash_table_row_mutation = block_hash_table.row(hash_table_row_key)
    hash_table_row_mutation.set_cell(
        COLUMN_FAMILY_ID, "header", rlp.encode(block_header)
    )
    hash_table_row_mutation.set_cell(COLUMN_FAMILY_ID, "number", str(block_number))
    hash_table_row_mutation.commit()

    logging.info(
        f"Successfully wrote header and number of block {block_number} into 'block_hash' table"
    )

    """Block Index Table"""
    logging.info(f"Inserting block {block_number} into 'block_index' table")

    index_table_row_key = pad_number(block_number, BLOCK_NUM_PAD)
    index_table_row_mutation = block_index_table.row(index_table_row_key)
    index_table_row_mutation.set_cell(COLUMN_FAMILY_ID, "hash", block_hash)
    index_table_row_mutation.commit()

    logging.info(
        f"Successfully wrote header of block {block_number} into 'block_index' table"
    )
