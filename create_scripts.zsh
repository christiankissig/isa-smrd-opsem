#!/usr/bin/bash

# Read the input file
input_file="RCU_wm_proofs_old.thy"

# Iterate over each line in the file
while IFS= read -r line; do
    # Check if the line matches the pattern "lemma somelemma:"
    if [[ $line =~ ^lemma\ ([^:]+): ]]; then
        echo $line
        # Extract the lemma name
        lemma_name="${BASH_REMATCH[1]}"
        # Create the new filename
        new_file="RCU_wm_proofs_old_${lemma_name}.thy"
        # Create the new file
        touch "$new_file"
        # Optionally, you can copy the line to the new file
        echo "$line" > "$new_file"
    fi
done < "$input_file"

