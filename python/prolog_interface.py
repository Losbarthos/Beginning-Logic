#  Library for converting swiplserver result dictionaries into python results
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze


import json
from swiplserver import PrologMQI, json_to_prolog


class PL_Interface:

	def __init__(self, consult_file):
		self.file = consult_file
		MQI = PrologMQI()
		MQI.start()

		self.PL = MQI.create_thread()
		self.PL.start()
		self.PL.query(f"consult('{self.file}').")

	def query(self, prolog_function):
		return self.PL.query(f"{prolog_function}")

		#with PrologMQI() as mqi:
		#	with mqi.create_thread() as prolog_thread:
		#		prolog_thread.query(f"consult('{self.file}').")
		#		result = prolog_thread.query(f"{prolog_function}.")
		#return result
