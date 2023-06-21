import os
import subprocess

# Replace 'your_command' with the desired command and 'source_directory' with the path to the directory containing the files
timeout = 300
# timeout = 150 # 2.5 min
source_directory = './xujie_code2inv'
tot = len(list(os.listdir(source_directory)))
# Iterate through all the files in the source_directory
for i, filename in enumerate(os.listdir(source_directory)):
    file_path = os.path.join(source_directory, filename)

    # Check if the current path is a file
    if os.path.isfile(file_path):
        # Construct the output file name and path
        output_filename = f"{filename[:-3]}.out"
        output_file_path = os.path.join("cvc_output", output_filename)

        # Run the command on the file and pipe the output to the output file
        try:
            command = command = f"cvc5 --tlimit={timeout*1000} {file_path}"
            result = subprocess.run(command, shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            # print("Z3 output:", result.stdout)
            output = f"STDOUT:\n{result.stdout}"
            # return True
        except subprocess.CalledProcessError as e:
            # print("Error occurred:", e.stdout + "\n" + e.stderr)
            output = f"STDERR:\n{e.stderr}"
            # return False
        finally:
            with open(output_file_path, 'w') as output_file:
                output_file.write(output)
        print(f"{i}/{tot} - {filename}")
        # breakpoint()

