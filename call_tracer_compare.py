import json
import requests

filename = "build/call_trace.txt"
quicknode_url = "https://still-palpable-putty.quiknode.pro/cf8d42f6a44191341443b48a385e8fb965dda149/"
headers = {
    "Content-Type": "application/json"
}

def clean_json(data):
    if isinstance(data, dict):
        cleaned_dict = {}
        for key, value in data.items():
            if key == "depth" or (key == "output" and value == "0x") or (key == "value" and value == "0x0" and data["type"] == "STATICCALL"):
                continue  # Skip this key-value pair
            cleaned_value = clean_json(value)
            if key == "calls" and isinstance(cleaned_value, list):
                cleaned_value = [item for item in cleaned_value if item]  # Remove empty dictionaries
            if not (key == "calls" and cleaned_value == []):
                cleaned_dict[key] = cleaned_value
        return cleaned_dict
    elif isinstance(data, list):
        return [clean_json(item) for item in data if item != []]
    return data

def compare_nested_dicts(result, actual, path=""):
    mismatches = []

    # Set of all keys in both dictionaries
    all_keys = set(result.keys()).union(set(actual.keys()))

    for key in all_keys:
        # Generate the current path for detailed logging
        current_path = f"{path}.{key}" if path else key

        expected_value = result.get(key, None)
        actual_value = actual.get(key, None)

        if isinstance(expected_value, dict) and isinstance(actual_value, dict):
            # Recursively compare nested dictionaries
            mismatches.extend(compare_nested_dicts(expected_value, actual_value, current_path))
        elif isinstance(expected_value, list) and isinstance(actual_value, list):
            # Compare lists by index
            for index, (exp_item, act_item) in enumerate(zip(expected_value, actual_value)):
                mismatches.extend(compare_nested_dicts(exp_item, act_item, f"{current_path}[{index}]"))
            # Check if the lists are of different lengths
            if len(expected_value) != len(actual_value):
                mismatches.append(f"Mismatch at {current_path}: List lengths differ (Expected: {len(expected_value)}, Actual: {len(actual_value)})")
        else:
            # Direct comparison for non-dict, non-list values
            if expected_value != actual_value:
                mismatches.append(f"Mismatch at {current_path}: Expected: {expected_value}, Actual: {actual_value}")

    return mismatches

cnt = 0

with open(filename, "r") as fin:
    for line in fin:
        line = line.strip()
        j = json.loads(line)
        # print(j)

        tx_hash = list(j.keys())[0]
        # print(tx_hash)

        payload = {
            "jsonrpc": "2.0",
            "method": "debug_traceTransaction",
            "params": [tx_hash, {"tracer" : "callTracer"}],
            "id": 1
        }

        response = requests.post(quicknode_url, headers=headers, data=json.dumps(payload))
        assert response.status_code == 200, "Non valid response from rpc"

        result = response.json()["result"]

        actual = j[tx_hash]

        actual = clean_json(dict(actual))

        mismatches = compare_nested_dicts(result, actual)
        if mismatches:
            print()
            print(tx_hash, mismatches)
            print()

        cnt += 1
        print(cnt, tx_hash)
