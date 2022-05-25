from swiplserver import PrologMQI, PrologThread

with PrologMQI() as mqi:
    with mqi.create_thread() as prolog_thread:
        result = prolog_thread.query("dict_create(Dict, Tag, [1-""a"", 2-""b""]).")
        print(result)