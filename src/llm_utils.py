import os


ACTION = "\033[95m"
INFO = "\033[94m"
SUCCESS = "\033[92m"
WARNING = "\033[93m"
FAIL = "\033[91m"
BOLD = "\033[1m"
UNDERLINE = "\033[4m"
END = "\033[0m"


class Logger:
    """A helper class for logging messages to std output."""

    verbose = False
    debug = False

    @staticmethod
    def log_action(action: str, msg: str):
        Logger.log(
            f"{ACTION}{BOLD}[>]{END} {INFO}{BOLD}{action}{END}:{os.linesep}{msg}"
        )

    @staticmethod
    def log_info(msg: str):
        Logger.log(f"{ACTION}{BOLD}[>]{END} {INFO}{BOLD}{msg}{END}")

    @staticmethod
    def log_debug(msg: str):
        if Logger.debug:
            Logger.log(f"{WARNING}{BOLD}[Debug]{END} {msg}")

    @staticmethod
    def log_success(msg: str):
        Logger.log(f"{SUCCESS}{BOLD}[Success]{END} {msg}")

    @staticmethod
    def log_warning(msg: str):
        Logger.log(f"{WARNING}{BOLD}[Warning]{END} {msg}")

    @staticmethod
    def log_error(msg: str):
        Logger.log(f"{FAIL}{BOLD}[Error]{END} {msg}")

    @staticmethod
    def log_model_request(model: str, messages: list[dict[str, str]]):
        if Logger.debug:
            msg = (
                "\n".join(
                    [
                        f"{BOLD}{UNDERLINE}{SUCCESS}"
                        + message["role"]
                        + f":{END} "
                        + message["content"]
                        for message in messages
                    ]
                )
                + f"\n{INFO}"
                + ("==" * 30)
                + f"{END}"
            )
            Logger.log(
                f"{INFO}{BOLD}Sending prompt to the '{model}' model:{END}\n{msg}"
            )

    @staticmethod
    def log_model_response(model: str, completions: [str]):
        if Logger.debug:
            msg = "\n".join(
                [
                    f"{BOLD}{UNDERLINE}{SUCCESS}Completion "
                    + str(i + 1)
                    + f":{END}\n"
                    + str(completion)
                    for i, completion in enumerate(completions)
                ]
            )
            Logger.log(
                f"{SUCCESS}{BOLD}Received response from the '{model}' model:{END}\n{msg}"
            )

    @staticmethod
    def log(msg: str):
        print(msg)


class Settings:
    def __init__(
        self,
        provider: str = "azure-openai",
        api_key: str | None = None,
        api_base: str | None = None,
        api_version: str | None = None,
        model: str = "gpt-4",
        max_tokens: int = 1000,
        temperature: float = 0.7,
        top_p: float = 0.95,
        frequency_penalty: float = 0.0,
        presence_penalty: float = 0.0,
        stop: str | None = None,
        num_completions: int = 1,
        max_retries: int = 10,
        prompts_per_minute: int = 2,
        max_batch_size: int = 5,
        verbose: bool = False,
        debug: bool = False,
    ):
        """Initializes a new 'Settings' instance from the specified parameters."""
        self.provider = provider
        self.api_key = api_key
        self.api_base = api_base
        self.api_version = api_version
        self.model = model
        self.max_tokens = max_tokens
        self.temperature = temperature
        self.top_p = top_p
        self.frequency_penalty = frequency_penalty
        self.presence_penalty = presence_penalty
        self.stop = stop
        self.num_completions = num_completions
        self.max_retries = max_retries
        self.prompts_per_minute = prompts_per_minute
        self.max_batch_size = max_batch_size
        self.verbose = verbose
        self.debug = debug

    def get_api_key(self) -> str:
        """Returns the API key."""
        if self.api_key is None or len(self.api_key) == 0:
            self.api_key = os.environ.get("OPENAI_API_KEY")
            if self.api_key is None or len(self.api_key) == 0:
                raise ValueError("No API key provided.")
            return self.api_key
        return self.api_key

    def get_api_base(self) -> str:
        """Returns the API base."""
        if self.api_base is None or len(self.api_base) == 0:
            self.api_base = os.environ.get("OPENAI_API_BASE")
            if self.api_base is None or len(self.api_base) == 0:
                raise ValueError("No API endpoint provided.")
            return self.api_base
        return self.api_base

    def get_api_version(self) -> str:
        """Returns the API version."""
        if self.api_version is None or len(self.api_version) == 0:
            self.api_version = os.environ.get("OPENAI_API_VERSION")
            if self.api_version is None or len(self.api_version) == 0:
                raise ValueError("No API version provided.")
            return self.api_version
        return self.api_version
