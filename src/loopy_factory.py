from benchmark import Benchmark
from checker import Checker
from boogie import BoogieBenchmark, BoogieChecker
from frama_c import FramaCBenchmark, FramaCChecker


class LoopyFactory:
    def __init__(self, name="frama-c"):
        self.name = name

    def get_benchmark(self, benchmarks_file="", features=None) -> Benchmark:
        if self.name == "frama-c":
            return FramaCBenchmark(benchmarks_file, features)
        elif self.name == "boogie":
            return BoogieBenchmark(benchmarks_file, features)
        else:
            raise Exception("Unsupported checker")

    def get_checker(self) -> Checker:
        if self.name == "frama-c":
            return FramaCChecker()
        elif self.name == "boogie":
            return BoogieChecker()
        else:
            raise Exception("Unsupported checker")
