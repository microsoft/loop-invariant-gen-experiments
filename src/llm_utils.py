import os


class Settings:
    def __init__(
        self,
        provider: str = "azure-openai",
        api_key: str = "",
        model: str = "gpt-4",
        max_tokens: int = 1000,
        temperature: float = 0.7,
        top_p: float = 0.95,
        frequency_penalty: float = 0.0,
        presence_penalty: float = 0.0,
        stop: str = None,
        num_completions: int = 1,
        max_retries: int = 10,
        prompts_per_minute: int = 2,
        verbose: bool = False,
        debug: bool = False,
    ):
        """Initializes a new 'Settings' instance from the specified parameters."""
        self.provider = provider
        self.api_key = api_key
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
        self.verbose = verbose
        self.debug = debug

    def get_api_key(self) -> str:
        """Returns the API key."""
        if len(self.api_key) == 0:
            self.api_key = os.environ.get("OPENAI_API_KEY")
            if self.api_key is None or len(self.api_key) == 0:
                raise ValueError("No API key provided.")
            return self.api_key
        return self.api_key


ACTION = "\033[95m"
INFO = "\033[94m"
SUCCESS = "\033[92m"
WARNING = "\033[93m"
FAIL = "\033[91m"
BOLD = "\033[1m"
UNDERLINE = "\033[4m"
END = "\033[0m"


class Logger:
    """A helper class for logging messages."""

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
    def log_model_request(model: str, msg: str):
        if Logger.debug:
            Logger.log(
                f"{INFO}{BOLD}Sending prompt to the '{model}' model:{END}\n{msg}"
            )

    @staticmethod
    def log_model_response(model: str, msg):
        if Logger.debug:
            Logger.log(
                f"{SUCCESS}{BOLD}Received response from the '{model}' model:{END}\n{msg}"
            )

    @staticmethod
    def log(msg: str):
        print(msg)
