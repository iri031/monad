#!/bin/bash

SLEEP_INTERVAL=2

usage() {
    echo "Usage: $0 <source_dir> <destination_dir>"
    exit 1
}

if [ "$#" -ne 2 ]; then
    echo "Error: Invalid number of arguments."
    usage
fi

SOURCE_DIR="$1"
DEST_DIR="$2"

if [ ! -d "$SOURCE_DIR" ]; then
    echo "Error: Source directory '$SOURCE_DIR' does not exist."
    exit 1
fi

if [ ! -d "$DEST_DIR" ]; then
    echo "Destination directory '$DEST_DIR' does not exist. Creating it..."
    mkdir -p "$DEST_DIR"
    if [ $? -ne 0 ]; then
        echo "Error: Failed to create destination directory '$DEST_DIR'."
        exit 1
    fi
fi

echo "Starting to move block files from '$SOURCE_DIR' to '$DEST_DIR' every $SLEEP_INTERVAL second(s)..."

FILES=$(ls "$SOURCE_DIR" | grep -E '^[0-9]+$' | sort -n)

TOTAL_FILES=$(echo "$FILES" | wc -l)
echo "Found $TOTAL_FILES block file(s) to move."

COUNTER=0

for FILE in $FILES; do
    COUNTER=$((COUNTER + 1))
    echo "[$COUNTER/$TOTAL_FILES] Copying file '$FILE'..."
    
    cp "$SOURCE_DIR/$FILE" "$DEST_DIR/"
    
    if [ $? -eq 0 ]; then
        echo "Successfully copied '$FILE'."
    else
        echo "Error: Failed to copy '$FILE'."
        exit 1
    fi
    
    sleep "$SLEEP_INTERVAL"
done

echo "Done."
