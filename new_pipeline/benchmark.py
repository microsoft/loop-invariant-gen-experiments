import os


class BenchmarkInstance:
    def __init__(
        self,
        llm_input=None,
        checker_input=None,
        llm_input_path=None,
        checker_input_path=None,
    ):
        self.llm_input = llm_input
        self.checker_input = checker_input
        self.llm_input_path = llm_input_path
        self.checker_input_path = checker_input_path

    def __repr__(self) -> str:
        return f"BenchmarkInstance(data={self.llm_input}, checker_input={self.checker_input})"

    def __str__(self) -> str:
        return self.__repr__()


class Benchmark:
    def __init__(self, llm_input_dir="", checker_input_dir="", llm_input_file=""):
        self.llm_input_path = llm_input_dir
        self.checker_input_path = checker_input_dir
        self.llm_input_file = ""
        self.instances: list[BenchmarkInstance] = []

    def preprocess(self, code):
        raise NotImplementedError

    def load_instances(self):
        if self.llm_input_file != "":
            with open(self.llm_input_file) as f:
                files = f.read().splitlines()
                for file in files:
                    with open(os.path.join("../new_benchmarks/", file)) as code_file:
                        code = code_file.read()
                        try:
                            self.instances.append(
                                BenchmarkInstance(
                                    llm_input=self.preprocess(code),
                                    llm_input_path=os.path.join("../new_benchmarks/", file),
                                    checker_input=self.preprocess(code),
                                )
                            )
                        except Exception as e:
                            if e.args[0] == "Interprocedural analysis not supported":
                                continue
                            else:
                                raise e
            return

        if self.llm_input_path == "" or not os.path.exists(self.llm_input_path):
            raise Exception("LLM input directory path not found")
        llm_input_files = os.listdir(
            os.path.join(os.path.dirname(__file__), self.llm_input_path)
        )
        llm_input_files = sorted(llm_input_files, key=lambda x: int(x.split(".")[0]))

        if self.checker_input_path != "" and os.path.exists(self.checker_input_path):
            checker_input_files = os.listdir(
                os.path.join(os.path.dirname(__file__), self.checker_input_path)
            )
            checker_input_files = sorted(
                sorted(checker_input_files), key=lambda x: int(x.split(".")[0])
            )

            if len(llm_input_files) != len(checker_input_files):
                raise Exception(
                    "Number of LLM input files and checker input files do not match"
                )
            for x, y in zip(llm_input_files, checker_input_files):
                llm_input = None
                checker_input = None
                with open(os.path.join(self.llm_input_path, x)) as f:
                    llm_input = f.read()
                with open(os.path.join(self.checker_input_path, y)) as f:
                    checker_input = f.read()
                self.instances.append(
                    BenchmarkInstance(
                        llm_input=llm_input,
                        checker_input=checker_input,
                        llm_input_path=os.path.join(self.llm_input_path, x),
                        checker_input_path=os.path.join(self.checker_input_path, y),
                    )
                )

        else:
            try:
                for file in llm_input_files:
                    with open(os.path.join(self.llm_input_path, file)) as f:
                        llm_input = f.read()
                        checker_input = self.raw_input_to_checker_input(llm_input)
                        self.instances.append(
                            BenchmarkInstance(
                                llm_input=llm_input,
                                checker_input=checker_input,
                                llm_input_path=os.path.join(self.llm_input_path, file),
                                checker_input_path=None,
                            )
                        )
            except Exception as e:
                print(e)
                raise Exception(
                    "Error loading instances. Neither checker_input dir nor raw_input_to_checker_input function provided."
                )

    def combine_llm_outputs(self, checker_input, llm_outputs):
        """
        Takes in un-annotated checker input (processed-benchmarks) 
        and annotated llm outputs and combines them.
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

    def raw_input_to_checker_input(self, code):
        raise NotImplementedError
