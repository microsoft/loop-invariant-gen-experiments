from datetime import datetime
import os


class Benchmark:
    def __init__(self, llm_input_dir="", llm_input_file="", features=None):
        self.llm_input_path = llm_input_dir
        self.llm_input_file = llm_input_file
        self.features = features
        self.input_file_paths = []

    def preprocess(self, code):
        raise NotImplementedError

    def check_input(self):
        if self.llm_input_file != "":
            with open(self.llm_input_file) as f:
                files = f.read().splitlines()
                for file in files:
                    if not os.path.exists(file):
                        raise InvalidBenchmarkException(f"File {file} not found")
                    try:
                        code = None
                        with open(file) as f:
                            code = f.read()
                        self.preprocess(code, self.features)
                        self.input_file_paths.append(file)
                    except InvalidBenchmarkException as e:
                        print(f"Error: {e.message}. File: {file}.")

            with open(
                datetime.now().strftime("benchmark_input_%Y_%m_%d_%H_%M_%S") + ".txt",
                "w",
            ) as f:
                f.write("\n".join(self.input_file_paths))
            return

        elif os.path.exists(self.llm_input_path):
            raise Exception("LLM input directory path not found")

        if not os.path.exists(
            os.path.join(os.path.dirname(__file__), self.llm_input_path)
        ):
            raise Exception("LLM input directory path not found")

        llm_input_files = os.listdir(
            os.path.join(os.path.dirname(__file__), self.llm_input_path)
        )

        for file in llm_input_files:
            if not os.path.exists(os.path.join(self.llm_input_path, file)):
                raise InvalidBenchmarkException(f"File {file} not found")
            try:
                code = None
                with open(os.path.join(self.llm_input_path, file)) as f:
                    code = f.read()
                self.preprocess(
                    code,
                    self.features,
                )
                self.input_file_paths.append(os.path.join(self.llm_input_path, file))
            except InvalidBenchmarkException as e:
                print(f"Error: {e.message}. File: {file}. ")
            self.input_file_paths.append(os.path.join(self.llm_input_path, file))

    def get_code(self, file_path):
        code = None
        with open(file_path) as f:
            code = f.read()
            try:
                code = self.preprocess(code, self.features)
            except InvalidBenchmarkException as e:
                print(f"Error: {e.message}. File: {file_path}.")
        return code

    def combine_llm_outputs(self, checker_input, llm_outputs, features=None):
        """
        WARNING: Combines invariants from all completions.
        Takes an un-annotated checker input (processed-benchmarks)
        and annotated llm outputs, takes the annotation from llm outputs
        and adds it to the checker input them.
        """
        if not any("insert invariant" in line for line in checker_input.splitlines()):
            print(f"Ignoring since no insert invariant keyword")
            return ""

        invariants = []
        for llm_output in llm_outputs:
            lines = llm_output.splitlines()
            for line in lines:
                if "invariant" in line and "insert invariants" not in line:
                    invariants.append(line.strip())

        lines = checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            if "insert invariant" in line:
                loc = index
                break
        if loc is not None:
            lines = lines[: loc + 1] + invariants + lines[loc + 1 :]
        else:
            raise Exception("No 'insert invariant' found")
        output = "\n".join(lines)

        return output


class InvalidBenchmarkException(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)
