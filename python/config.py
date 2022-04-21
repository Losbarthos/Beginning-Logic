#  Configuration file
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze

from enum import Enum
from pathlib import Path


GET_PROTOCOLL = False

# Conventions of Table headlines
ASSUMPTION = "Assumption"
CONCLUSION = "Conclusion"

# Conventions of logical operators
NEG = '¬'
AND = '∧'
OR = '∨'
IMP = '→'
EQV = '↔'
DERIVATION = '⊦'
BINARY_CONNECTIVES = [AND, OR, IMP, EQV]

# Conventions of Filenames
ROOT_DIR = Path(__file__).parent.parent
CSV_THEOREMS = f"{ROOT_DIR}/data/theorems.csv"
CSV_PROBLEMS = f"{ROOT_DIR}/data/problems.csv"
PL_LOGIC = f"{ROOT_DIR}/prolog/logic.pl"

I_GRAPH = f"{ROOT_DIR}/icons/graph.png"
I_QED = f"{ROOT_DIR}/icons/qed.png"
I_TBL = f"{ROOT_DIR}/icons/table.png"
I_RESET = f"{ROOT_DIR}/icons/reset.png"

# Stores meaningfull names in further programms in some enum.
class Definition(Enum):
	ASSUMPTION = 0
	PREMISS = 1
	CONCLUSION = 2

BASIC_RULES = {
		'↓∧': '∧E',
		'↓→': '→E', 
		'↓∨': '∨E', 
		'↑∧': '∧I',
		'↑→': '→I', 
		'↑∨': '∨I', 
		'↓¬¬': '¬E', 
		'↓¬': '¬I'}


# Starts and gets basic config of prolog interpreter swiprologserver
ARGS = 'args'
FUNCTOR = 'functor'