from abc import ABC, abstractmethod


class Checker(ABC):
    @abstractmethod
    def __init__(self, name):
        self.name = name
        self.timeout = 10

    @abstractmethod
    def check(self, code, features):
        raise NotImplementedError

    @abstractmethod
    def has_invariant(self, line):
        raise NotImplementedError

    @abstractmethod
    def has_variant(self, line):
        raise NotImplementedError

    @abstractmethod
    def has_function_contract(self, lines):
        raise NotImplementedError

    @abstractmethod
    def houdini(self, input_code, features):
        raise NotImplementedError
