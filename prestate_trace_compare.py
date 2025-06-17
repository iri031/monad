import json
import requests
import argparse
import sys

from typing import Any, Dict, List

quicknode_url = "https://still-palpable-putty.quiknode.pro/cf8d42f6a44191341443b48a385e8fb965dda149/"
headers = {"Content-Type": "application/json"}


def _normalize(v: Any) -> Any:
    if isinstance(v, str):
        if v.lower().startswith("0x"):
            try:
                return int(v, 16)
            except ValueError:
                pass  # keep as‑is if it isn’t valid hex
        if v.isdigit():  # decimal in string form
            return int(v)
    return v


def compare_dicts(actual: Dict, expected: Dict, path: str = "") -> List[str]:
    diffs: List[str] = []
    k1, k2 = set(actual), set(expected)

    for k in sorted(k1 - k2):
        diffs.append(f"{path}/{k if path else k} - only in actual")

    for k in sorted(k2 - k1):
        diffs.append(f"{path}/{k if path else k} - only in expected (quicknode)")

    for k in sorted(k1 & k2):
        v1, v2 = actual[k], expected[k]
        sub = f"{path}/{k}" if path else k
        if isinstance(v1, dict) and isinstance(v2, dict):
            diffs.extend(compare_dicts(v1, v2, sub))
        else:
            if _normalize(v1) != _normalize(v2):
                diffs.append(f"{sub} - {v1!r} != {v2!r}")
    return diffs


def main():
    parser = argparse.ArgumentParser(
        description="Compare on-chain debug_traceTransaction output against a log file"
    )
    parser.add_argument(
        "trace",
        help="path to your trace file (must contain 'prestate' or 'statediff' in its name)",
    )
    parser.add_argument(
        "--url",
        default="https://still-palpable-putty.quiknode.pro/cf8d42f6a44191341443b48a385e8fb965dda149/",
        help="QuickNode RPC endpoint",
    )
    args = parser.parse_args()

    filename = args.trace

    if "prestate" in filename:
        tracer_config = {"tracer": "prestateTracer"}
    elif "statediff" in filename:
        tracer_config = {
            "tracer": "prestateTracer",
            "tracerConfig": {"diffMode": True},
        }
    else:
        parser.error("filename must contain either 'prestate' or 'statediff'")

    cnt = 0
    with open(filename, "r") as fin:
        for line in fin:
            line = line.strip()

            j = json.loads(line)

            tx_hash = list(j.keys())[0]

            payload = {
                "jsonrpc": "2.0",
                "method": "debug_traceTransaction",
                "params": [tx_hash, tracer_config],
                "id": 1,
            }

            # print(json.dumps((payload)))

            response = requests.post(
                quicknode_url, headers=headers, data=json.dumps(payload)
            )
            # print(response)
            assert response.status_code == 200, "Non valid response from rpc"

            expected = response.json()["result"]
            actual = j[tx_hash]

            # print("Actual: ", actual)
            # print("Expected: ", expected)

            mismatches = compare_dicts(actual, expected)

            if mismatches:
                print(f"Mismatch happened for tx {cnt + 1} with hash {tx_hash}")
                print(mismatches)
                print()
                sys.exit(1)

            cnt += 1

            print(cnt, tx_hash)


if __name__ == "__main__":
    main()