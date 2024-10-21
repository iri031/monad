import os
import sys
import brotli
import rlp
import logging
from web3 import Web3
from typing import Any, Tuple

logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)

BLOCK_NUM_PAD = 10
TX_NUM_PAD = 5


def pad_number(number: int, width: int) -> str:
    return str(number).zfill(width)


def compute_hash(data: bytes) -> str:
    return Web3.keccak(data).hex()


def decompress_block(block_dir: str, block_number: int) -> bytes:
    file_path = os.path.join(block_dir, str(block_number))
    if not os.path.isfile(file_path):
        logging.error(f"File for block {block_number} does not exist at '{file_path}'.")
        sys.exit(1)

    try:
        with open(file_path, "rb") as f:
            compressed_block_data = f.read()
            block_data = brotli.decompress(compressed_block_data)

    except brotli.error as e:
        logging.error(f"Failed to decompress block {block_number}: {e}")
        sys.exit(1)

    return block_data


def decode_block(decompressed_block: bytes, block_number: int) -> Tuple[Any, Any]:

    transactions = []
    block_header = []

    try:
        decoded_block = rlp.decode(decompressed_block)
        block_header = decoded_block[0]
        transactions = decoded_block[1]
    except rlp.DecodingError as e:
        logging.error(f"Failed to decode block {block_number}: {e}")
        sys.exit(1)

    return block_header, transactions
