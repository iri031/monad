from typing import List

class ArchiveInterface:

    '''
        ******Writer Methods******
    '''
    def archive_block(self, raw_block: bytes, block_num: int) -> None:
        '''
            1) Block Data Indexing:
                Table 1: key = block_number, value = [rlp(Block), txs_cnt]
                Table 2: key = block_hash, value = block_number
            2) Tx Data Indexing (archive_block implicitly calls 'archive_tx' inside):
                Table 1: key = tx_hash, value = [block_number, start_byte, end_byte]
                Table 2: key = (block_number, tx_number), value = [start_byte, end_byte]
        '''
        raise NotImplementedError("'archive_block' not implemented")


    def archive_receipts(self, receipts: bytes, block_num: int, tx_hashes: List[bytes]) -> None:
        '''
            Table 1: key = block_number, value = rlp(vector<Receipt>)
            Table 2: key = tx_hash, value = [block_number, start_byte, end_byte]
        '''
        raise NotImplementedError("'archive_receipts' not implemented")
    

    def archive_traces(self, traces: bytes, block_num: int, tx_hashes: List[bytes]) -> None:
        '''
            We need different tables for different type of traces. For each type:
                Table 1: key = block_number, value = rlp(vector<TraceType>)
                Table 2: key = tx_hash, value = [block_number, start_bytes, end_bytes]
        '''
        raise NotImplementedError("'archive_traces' not implemented")
    

    '''
        ******Reader Methods******
    '''

    '''
        ***Block Methods***
    '''

    '''eth_getBlockByHash'''
    def get_block_by_hash(self, block_hash: bytes) -> bytes:
        '''
            1) block_hash -> block_number
            2) block_number -> rlp(block)
        '''
        raise NotImplementedError("'get_block_by_hash' not implemented")


    '''eth_getBlockByNumber'''
    def get_block_by_number(self, block_num: int) -> bytes:
        '''
            1) block_number -> rlp(block)
        '''
        raise NotImplementedError("'get_block_by_number' not implemented")
    

    '''eth_getBlockTransactionCountByHash'''
    def get_block_transaction_count_by_hash(self, hash: bytes) -> int:
        '''
            1) block_hash -> block_number
            2) block_number -> tx_cnt
        '''
        raise NotImplementedError("'get_block_transaction_count_by_hash' not implemented") 


    '''eth_getBlockTransactionCountByNumber'''
    def get_block_transaction_count_by_number(self, block_num: int) -> int:
        '''
            1) block_number -> tx_cnt
        '''
        raise NotImplementedError("'get_block_transaction_count_by_number' not implemented")
    

    '''
        ***Transaction Methods***
    '''
    
    '''eth_getTransactionByBlockHashAndIndex'''
    def get_transaction_by_block_hash_and_index(self, block_hash: bytes, tx_index: int) -> bytes:
        '''
            1) block_hash -> block_number
            2) (block_number, tx_index) -> (start_byte, end_byte)
            3) (block_number, [start_byte:end_byte]) -> transaction_byte
        '''
        raise NotImplementedError("'get_transaction_by_block_hash_and_index' not implemented")


    '''eth_getTransactionByBlockNumberAndIndex'''
    def get_transaction_by_block_number_and_index(self, block_number: int, tx_index: int) -> bytes:
        '''
            1) (block_number, tx_index) -> (start_byte, end_byte)
            2) (block_number, [start_byte:end_byte]) -> transaction_byte
        '''
        raise NotImplementedError("'get_transaction_by_block_number_and_index' not implemented")


    '''eth_getTransactionByHash'''
    def get_transaction_by_hash(self, tx_hash: bytes) -> bytes:
        '''
            1) tx_hash -> (block_number, start_byte, end_byte)
            2) (block_number, [start_byte:end_byte]) -> transaction
        '''
        raise NotImplementedError("'get_transaction_by_hash' not implemented")


    '''
        ***Receipt Methods***
    '''

    '''eth_getBlockReceipts'''
    def get_block_receipts(self, block_number: int) -> bytes:
        '''
            1) block_number -> receipts
        '''
        raise NotImplementedError("'get_block_receipts' not implemented")
    
    
    '''eth_getTransactionReceipt'''
    def get_transaction_receipt(self, tx_hash: bytes) -> bytes:
        '''
            1) tx_hash -> (block_number, start_byte, end_byte)
            2) (block_number, [start_byte:end_byte]) -> receipt
        '''
        raise NotImplementedError("'get_transaction_receipt' not implemented")
    

    '''
        ***Trace Methods***
    '''

    '''debug_traceBlockByHash'''
    def get_block_trace_by_hash(self, block_hash: bytes) -> bytes:
        '''
            1) block_hash -> block_number
            2) block_number -> traces
        '''
        raise NotImplementedError("'get_block_trace_by_hash' not implemented")


    '''debug_traceBlockByNumber'''
    def get_block_trace_by_number(self, block_number: int) -> bytes:
        '''
            1) block_number -> traces
        '''
        raise NotImplementedError("'get_block_trace_by_number' not implemented")


    '''debug_traceTransaction'''
    def get_transaction_trace(self, tx_hash: bytes) -> bytes:
        '''
            1) tx_hash -> (block_number, start_byte, end_byte)
            2) (block_number, [start_byte:end_byte]) -> trace
        '''
        raise NotImplementedError("'get_transaction_trace' not implemented")
