# Usage

The driver is main.py in the pipeline directory.

```bash
cd pipeline/
python3 main.py --help
```

The above should output the detailed usage:

```bash

usage: main.py [-h] --checker {boogie,frama-c} [--log-file LOG_FILE]
               [--config-file CONFIG_FILE]
               [--model {gpt-4,gpt-3.5-turbo,gpt-4-32k}] [-d] [--heal-errors]
               [--heal-errors-input HEAL_ERRORS_INPUT]
               [--max-benchmarks MAX_BENCHMARKS] [--start-index START_INDEX]
               [--healing-iterations HEALING_ITERATIONS]
               [--provider {azure-open-ai,huggingface}]
               [--problem-ids PROBLEM_IDS [PROBLEM_IDS ...]]
               [--recheck-logs RECHECK_LOGS] [--nudge]
               [--mode {variant,invariant}] [--multiple-loops]

options:
  -h, --help            show this help message and exit
  --checker {boogie,frama-c}
                        Checker to use [Required]
  --log-file LOG_FILE   File to write logs to
  --config-file CONFIG_FILE
                        File to read prompt configs from
  --model {gpt-4,gpt-3.5-turbo,gpt-4-32k}
                        Model to use
  -d, --debug           Debug mode
  --heal-errors         Heal incorrect invariants from a previous run
  --heal-errors-input HEAL_ERRORS_INPUT
                        Input file to heal errors from
  --max-benchmarks MAX_BENCHMARKS
                        Maximum number of benchmarks to run
  --start-index START_INDEX
                        Start the run from a given benchmark index
  --healing-iterations HEALING_ITERATIONS
                        Number of retries for each healing run
  --provider {azure-open-ai,huggingface}
                        Provider to fetch the model from
  --problem-ids PROBLEM_IDS [PROBLEM_IDS ...]
                        Problem IDs to run
  --recheck-logs RECHECK_LOGS
                        Recheck logs for errors
  --nudge               Nudge the model to generate better code
  --mode {variant,invariant}
                        Mode to run in
  --multiple-loops      Run benchmarks with multiple loops
```

#### NOTE: The CLI options may not be complete/accurate.
