import json
import ast
import requests
import argparse

parser = argparse.ArgumentParser(description='Parse RPC log file and resubmit requests.')
parser.add_argument('--log-path', nargs='?', default='rpc.log', help='Path to the log file (default: rpc.log)')
parser.add_argument('--rpc-url', dest='eth_rpc_url', help='RPC endpoint URL')
args = parser.parse_args()

log_path = args.log_path
ETH_RPC_URL = args.eth_rpc_url

def parse_rust_bytes_debug(s):
    assert s.startswith('b"') and s.endswith('"')
    s = s[2:-1]
    out = bytearray()
    i = 0
    while i < len(s):
        if s[i] == '\\':
            i += 1
            if s[i] == 'n':
                out.append(0x0A)
            elif s[i] == 'r':
                out.append(0x0D)
            elif s[i] == 't':
                out.append(0x09)
            elif s[i] == '0':
                out.append(0x00)
            elif s[i] == '"':
                out.append(ord('"'))
            elif s[i] == '\\':
                out.append(ord('\\'))
            elif s[i] == 'x':
                out.append(int(s[i+1:i+3], 16))
                i += 2
            else:
                raise ValueError(f"Unknown escape: \\{s[i]}")
        else:
            out.append(ord(s[i]))
        i += 1
    return bytes(out)

with open(log_path, 'r') as f:
    for line in f:
        line = line.strip()
        if not line:
            continue
        # Find the first '{' to skip syslog prefix
        json_start = line.find('{')
        if json_start == -1:
            continue
        try:
            log_obj = json.loads(line[json_start:])
            # Try to parse the 'body' field if present
            fields = log_obj.get('fields', {})
            body = fields.get('body')
            if body:
                body_bytes = parse_rust_bytes_debug(body)
                if body_bytes is not None:
                    try:
                        body_str = body_bytes.decode('utf-8')
                        log_obj['body_json'] = json.loads(body_str)
                        # Replace explicit block number with 'finalized' in params if present
                        params = log_obj['body_json'].get('params')
                        if (
                            isinstance(params, list)
                            and len(params) > 1
                        ):
                            log_obj['body_json']['params'][1] = 'finalized'
                        print(f'Executing as Ethereum RPC call: {log_obj["body_json"]}')
                        try:
                            resp = requests.post(ETH_RPC_URL, json=log_obj['body_json'])
                            print('RPC response:', resp.status_code, resp.text)
                        except Exception as e:
                            print('RPC call failed:', e)
                    except Exception:
                        log_obj['body_json'] = None
        except json.JSONDecodeError:
            continue        
