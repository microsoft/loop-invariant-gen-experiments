import os

def main():
    directories = ["original_benchmarks"]
    files = []
    
    files = []
    for directory in directories:
        if not os.path.isdir(directory):
            print(f"Invalid input directory: {directory}")
            exit(1)
        files.extend([str(x) for x in list(Path(directory).rglob("*.[c|cpp]"))])