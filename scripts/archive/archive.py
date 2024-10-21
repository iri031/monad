#!/usr/bin/env python3

import os
import sys
import time
from watchdog.observers import Observer
from concurrent.futures import ThreadPoolExecutor

from util import *
from monitor import NewBlockHandler
from table import (
    create_tables,
    insert_block_into_block_tables,
    insert_block_into_tx_tables,
)

# Configuration Constants
MAX_WORKERS = 5


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
    table_ids = ["tx_hash", "tx_index", "block_hash", "block_index"]

    tables = create_tables(project_id, instance_id, table_ids)

    # Process existing block files in the directory
    existing_files = os.listdir(block_dir)
    existing_blocks = [int(f) for f in existing_files if f.isdigit()]
    logging.info(f"Found {len(existing_blocks)} existing block files. Processing...")

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        for block_num in existing_blocks:
            decompressed_block = decompress_block(block_dir, block_num)
            header, transactions = decode_block(decompressed_block, block_num)
            executor.submit(
                insert_block_into_tx_tables,
                transactions,
                block_num,
                tables[0],
                tables[1],
            )

            executor.submit(
                insert_block_into_block_tables,
                header,
                decompressed_block,
                block_num,
                tables[2],
                tables[3],
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
