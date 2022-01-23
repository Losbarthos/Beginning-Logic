from pyswip import Prolog
from enum import Enum
from pathlib import Path


# Conventions of Table headlines
ASSUMPTION = "Assumption"
CONCLUSION = "Conclusion"

# Conventions of Filenames
ROOT_DIR = Path(__file__).parent.parent
CSV_THEOREMS = f"{ROOT_DIR}/data/theorems.csv"
CSV_PROBLEMS = f"{ROOT_DIR}/data/problems.csv"
PL_LOGIC = f"{ROOT_DIR}/prolog/logic.pl"

# Stores meaningfull names in further programms in some enum.
class Definition(Enum):
	ASSUMPTION = 0
	PREMISS = 1
	CONCLUSION = 2


# Starts and gets basic config of prolog interpreter swi-prolog
PL = Prolog()
PL.consult(PL_LOGIC)