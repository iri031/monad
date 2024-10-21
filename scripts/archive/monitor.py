import os
import sys
from typing import List
from watchdog.events import FileSystemEvent, FileSystemEventHandler
from google.cloud import bigtable
from concurrent.futures import ThreadPoolExecutor

from util import logging, decompress_block, decode_block
from table import insert_block_into_tx_tables, insert_block_into_block_tables

"""Handler for new block files."""
class NewBlockHandler(FileSystemEventHandler):
    def __init__(
        self, block_dir: str, tables: List[bigtable.table], executor: ThreadPoolExecutor
    ) -> None:
        super().__init__()
        self.block_dir = block_dir
        self.tables = tables
        self.executor = executor

    """Called when a file is created."""
    def on_created(self, event: FileSystemEvent) -> None:
        if event.is_directory:
            logging.error("Unexpected directory created!")
            sys.exit(1)

        file_name = os.path.basename(event.src_path)
        if not file_name.isdigit():
            logging.error(f"Unexpected non-digit filename created: {file_name}")
            sys.exit(1)

        block_number = int(file_name)
        logging.info(f"Detected new block file: {file_name}")

        decompressed_block = decompress_block(self.block_dir, block_number)
        header, transactions = decode_block(decompressed_block, block_number)

        self.executor.submit(
            insert_block_into_tx_tables,
            transactions,
            block_number,
            self.tables[0],
            self.tables[1],
        )

        self.executor.submit(
            insert_block_into_block_tables,
            header,
            decompressed_block,
            block_number,
            self.tables[2],
            self.tables[3],
        )
