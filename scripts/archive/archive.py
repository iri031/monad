#!/usr/bin/env python3

import os
import sys
import brotli
import rlp
import time
import logging
from google.cloud import bigtable
from google.cloud.bigtable.batcher import MutationsBatcher
from web3 import Web3
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler
from concurrent.futures import ThreadPoolExecutor

# Configuration Constants
BLOCK_NUM_PAD = 10
TX_NUM_PAD = 5
MAX_WORKERS = 5
COLUMN_FAMILY_ID = "data"

logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)


def pad_number(number, width):
    return str(number).zfill(width)


def compute_tx_hash(tx_bytes):
    return Web3.keccak(tx_bytes).hex()


def decode_block(block_dir, block_number):
    file_path = os.path.join(block_dir, str(block_number))
    if not os.path.isfile(file_path):
        logging.error(f"File for block {block_number} does not exist at '{file_path}'.")
        sys.exit(1)

    transactions = []
    block_header = []

    try:
        with open(file_path, "rb") as f:
            compressed_block_data = f.read()
            block_data = brotli.decompress(compressed_block_data)

            decoded_block = rlp.decode(block_data)
            block_header = decoded_block[0]
            transactions = decoded_block[1]

    except brotli.error as e:
        logging.error(f"Failed to decompress block {block_number}: {e}")
        sys.exit(1)
    except rlp.DecodingError as e:
        logging.error(f"Failed to decode block {block_number}: {e}")
        sys.exit(1)

    return block_header, transactions


"""Handler for new block files."""
class NewBlockHandler(FileSystemEventHandler):
    def __init__(self, block_dir, tables, executor):
        super().__init__()
        self.block_dir = block_dir
        self.tables = tables
        self.executor = executor

    """Called when a file is created."""
    def on_created(self, event):
        if event.is_directory:
            logging.error("Unexpected directory created!")
            sys.exit(1)

        file_name = os.path.basename(event.src_path)
        if not file_name.isdigit():
            logging.error(f"Unexpected non-digit filename created: {file_name}")
            sys.exit(1)

        block_number = int(file_name)
        logging.info(f"Detected new block file: {file_name}")

        header, transactions = decode_block(self.block_dir, block_number)

        self.executor.submit(
            insert_block_into_tx_tables,
            transactions,
            block_number,
            self.tables[0],
            self.tables[1],
        )


"""
Create tables and column families if they don't exist before
Right now we fix each table to have one column family called "data"
"""
def create_tables(project_id, instance_id, table_ids):
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


def insert_block_into_tx_tables(transactions, block_number, tx_hash_table, tx_index_table):
    tx_datas = []
    tx_hashes = []
    tx_indexes = []

    for tx_num, tx in enumerate(transactions):
        # re-encoding because individual fields are decoded
        tx_data = rlp.encode(tx)
        tx_hash = compute_tx_hash(tx_data)

        """generate joint index <block_number>_<tx_number>"""
        block_padded = pad_number(block_number, BLOCK_NUM_PAD)
        tx_padded = pad_number(tx_num, TX_NUM_PAD)
        tx_index = f"{block_padded}_{tx_padded}"

        tx_datas.append(tx_data)
        tx_hashes.append(tx_hash)
        tx_indexes.append(tx_index)

    logging.info(f"Inserting block {block_number} into 'tx_hash_table'")
    with MutationsBatcher(table=tx_hash_table) as batcher:
        hash_table_rows = []
        for i in range(len(transactions)):
            hash_table_tx_row_key = tx_hashes[i]
            hash_table_tx_row = tx_hash_table.row(hash_table_tx_row_key)
            hash_table_tx_row.set_cell(COLUMN_FAMILY_ID, "tx_index", tx_indexes[i])
            hash_table_tx_row.set_cell(COLUMN_FAMILY_ID, "tx_data", tx_datas[i])

            hash_table_rows.append(hash_table_tx_row)

            logging.debug(
                f"Adding tx {tx_num} of block {block_number} hash={tx_hash} into 'tx_hash_table'"
            )

        batcher.mutate_rows(hash_table_rows)
        logging.info(f"Successfully wrote {str(len(transactions))} rows for block {block_number} into 'tx_hash_table'")
    
    logging.info(f"Inserting block {block_number} into 'tx_index_table'")
    with MutationsBatcher(table=tx_index_table) as batcher:
        index_table_rows = []
        for i in range(len(transactions)):
            index_table_tx_row_key = tx_indexes[i]
            index_table_tx_row = tx_index_table.row(index_table_tx_row_key)
            index_table_tx_row.set_cell(COLUMN_FAMILY_ID, "tx_hash", tx_hashes[i])

            index_table_rows.append(index_table_tx_row)

            logging.debug(
                f"Adding tx {tx_num} of block {block_number} hash={tx_hash} into 'tx_index_table'"
            )

        batcher.mutate_rows(index_table_rows)
        logging.info(f"Successfully wrote {str(len(transactions))} rows for block {block_number} into 'tx_index_table'")


def main():
    if len(sys.argv) != 4:
        logging.error(
            "Usage: python3 process_and_store_blocks.py <project_id> <instance_id> <block_dir>"
        )
        sys.exit(1)

    project_id = sys.argv[1]
    instance_id = sys.argv[2]
    block_dir = sys.argv[3]
    if not os.path.isdir(block_dir):
        logging.error(f"{block_dir} is not a valid directory")
        sys.exit(1)

    # TODO: hard-coded table ids
    table_ids = ["tx_hash", "tx_index"]

    tables = create_tables(project_id, instance_id, table_ids)

    # Process existing block files in the directory
    existing_files = os.listdir(block_dir)
    existing_blocks = [int(f) for f in existing_files if f.isdigit()]
    logging.info(f"Found {len(existing_blocks)} existing block files. Processing...")

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        for block_num in existing_blocks:
            header, transactions = decode_block(block_dir, block_num)
            executor.submit(
                insert_block_into_tx_tables,
                transactions,
                block_num,
                tables[0],
                tables[1],
            )

        # Set up directory monitoring
        event_handler = NewBlockHandler(block_dir, tables, executor)
        observer = Observer()
        observer.schedule(event_handler, path=block_dir, recursive=False)
        observer.start()
        logging.info(f"Started monitoring directory: {block_dir} for new block files.")

        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            logging.warning("Stopping directory monitoring.")
            observer.stop()
        observer.join()

    logging.info("All blocks have been processed.")


if __name__ == "__main__":
    main()
