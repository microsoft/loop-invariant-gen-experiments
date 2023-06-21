#!/bin/bash

# Directory paths
src_dir="seahorn/seahorn_benchmark"
dest_dir="seahorn/seahorn_sygus_benchmark"

# File containing list of filenames
file_list="nums.txt"

# Check if destination directory exists, if not create it
if [ ! -d "$dest_dir" ]; then
  mkdir -p "$dest_dir"
fi

# Loop over each file in the file list
while IFS= read -r file
do
  # Check if file exists in the source directory
  if [ -e "$src_dir/$file" ]; then
    cp "$src_dir/$file" "$dest_dir"
    echo "Copied $file to $dest_dir"
  else
    echo "File $file does not exist in $src_dir"
  fi
done < "$file_list"

