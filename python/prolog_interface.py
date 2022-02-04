#  Library for converting swiplserver result dictionaries into python results
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze


from config  import *
import json


class PL_Interface:

	# Defines operators
	@staticmethod
	def get_operators(type):
		"""
			The variable type as the same meaning as the variable ?Type 
			in function current_op from swi-prolog, 
			see https://www.swi-prolog.org/pldoc/man?section=operators 
		"""
		operator_map = PL.query(f"current_op(X,{type},Y).")
		result = [var['Y'] for var in operator_map]
		return result
	@staticmethod
	def dict_to_datastring(dict_data):
		'''
			Converts some dictionary into a string which represents 
			the dictionary itself. The values of that string are not
			strings anymore.
			:param dict_data: dictionary to be converted 
		'''
		return "{" + ", ".join([f"'{k}': {v}" for k, v in dict_data.items()]) + "}"
	@staticmethod
	def list_to_datastring(list_data):
		'''
			Converts some list into a string which represents 
			the list itself. The values of that list are not
			strings anymore.
			:param list_data: list to be converted 
		'''
		return f"[{', '.join(list_data)}]"

	@staticmethod
	def swipl_to_formula(data):
		"""
			Converts some prolog formular predicate (see logic.pl) 
			from swiplserver format into natural format, wich results
			from prolog output.
		"""
		if isinstance(data, str):
			return data 

		functor = data[FUNCTOR]
		args = data[ARGS]
		
		case_bin = (functor in BINARY_CONNECTIVES)
		case_neg = (functor == '¬')

		if not (case_bin or case_neg):
			raise (ValueError(f'Problem with get_formula, '
								   f'the functor {functor} is in {BINARY_CONNECTIVES}.'))
		if case_bin:
			left = PL_Interface().swipl_to_formula(args[0])
			right = PL_Interface().swipl_to_formula(args[1])
			data = [left, right]

			return f"({functor.join(data)})"
		else: # is case_neg
			data = PL_Interface().swipl_to_formula(args[0])
			return f"({functor}{data})"

	@staticmethod
	def swipl_to_formula_list(data):
		return [PL_Interface().swipl_to_formula(x) for x in data]
	
	@staticmethod
	def swipl_to_rules(data):
		"""
			This method converts prolog outputs from swiplserver of that kind:
			       {'rule': {derivation}} 
			into some pair {rule: new_derivation}- 
			whereby new_derivation uses operators of kind xfy in the right way prolog
			would naturally descripe. In our example we would get the output:
			
			(e.g. 
			{'→E': {'args': [['p', {'args': ['p', 'q'], 'functor': '→'}], 'q'], 'functor': '⊦'}
			gets into
			{'→E': '[p, (p → q)] ⊦ q'})
		"""

		def swipl_to_derivation(args, functor):
			"""
				Converts some dictionary of type 
				{'args': [[Assumptions], Conclusion], 'functor': '⊦'}
				(e.g. {'args': [['p', {'args': ['p', 'q'], 'functor': '→'}], 'q'], 'functor': '⊦'})
				into some derivation '[Assumptions] ⊦ Conclusion'. In our example
				'[p, (p → q)] ⊦ q'
			"""
			if functor != DERIVATION:
				raise (ValueError(f'Problem with get_derivation, '
								   'the functor "{functor}" is not equal to "f{DERIVATION}".'))

			conclusion = PL_Interface().swipl_to_formula(args[1])
			assumptions = PL_Interface().list_to_datastring([PL_Interface().swipl_to_formula(x) for x in args[0]])
			data = [assumptions, conclusion]

			return f"{functor.join(data)}"

		def main(data):
			'''
				Called from get_rule(data)
			'''
			result = {}

			for key in data:
				derivation = data[key]
				args = derivation[ARGS]
				functor = derivation[FUNCTOR]

				result[key] = swipl_to_derivation(args, functor)

			return result
		
		# implementation of get_rule(data)
		return main(data)