## Monad BigTable Archive Script

- Run 'pip install -r requirements.txt' to install all required packages
- Install 'gcloud' related cli packages, and then run 'gcloud init' to setup a project and an instance
- Run 'python3 archive.py <project_id> <instance_id> <block_dir>' to insert data into google bigtable

To simulate real-time block processing:
- Run 'bash file_mover.sh <source_dir> <dest_dir>' and then set <block_dir> = <dest_dir> when running archive.py