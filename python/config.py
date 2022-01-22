from pyswip import Prolog
from enum import Enum
from pathlib import Path

# Starts prolog interpreter swi-prolog
PL = Prolog()

# Conventions of Table headlines
ASSUMPTION = "Assumption"
CONCLUSION = "Conclusion"

# Conventions of Filenames
ROOT_DIR = Path(__file__).parent.parent
CSV_THEOREMS = f"{ROOT_DIR}/data/theorems.csv"
CSV_PROBLEMS = f"{ROOT_DIR}/data/problems.csv"

class Definition(Enum):
	ASSUMPTION = 0
	PREMISS = 1
	CONCLUSION = 2
