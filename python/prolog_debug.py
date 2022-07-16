from config import *

def rreplace(s, old, new, occurrence):
    '''
        Way in Python to replace strings but, instead of starting from the beginning as replace does, starting from the end.
        https://stackoverflow.com/questions/2556108/rreplace-how-to-replace-the-last-occurrence-of-an-expression-in-a-string
    '''
    li = s.rsplit(old, occurrence)
    return new.join(li)


def remove_substrings_from_file(file_read, file_write, start, end, ss):
    '''
        Remove substrings with fixed 'start' and 'end' from .txt file 'file_read' and saves it into 'file_write'.
        more details see:
         https://stackoverflow.com/questions/72931747/python-remove-substrings-with-fixed-start-and-end-from-txt-file 
    '''
    def remove_inner_entry(s, append_to_file):
        '''
            Removes entry starts with start and ends with end from dict.
        '''
        if s.find(start) != -1 and s.find(end) == -1:
            if append_to_file == False:
                raise Exception("Term 'proof' in 'proof' at line " + s)
            append_to_file = False
            i = s.index(start)
            return [s[0:i - 1], append_to_file]
        elif s.find(end) != -1 and s.find(start) == -1:
            if append_to_file == True:
                raise Exception("Term '}' outside of 'proof' at line " + s)

            append_to_file = True
            i = s.index(end)
            return [s[i + 1 : -1] + "\n", append_to_file]
        elif s.find(end) != -1 and s.find(start) != -1:
            if append_to_file == True:
                raise Exception("Term '}? proof{' should not have append_to_file = True, more details see: " + s)
            return [None, append_to_file]

        else:
            if append_to_file == True:
                return [s, append_to_file]
        return [None, append_to_file]

    def remove_prefix_function(s, name):
        '''
            remove some prefix function of form "name(" inner ")", the result is inner
        '''
        s = s.replace(name + "(", "", 1)
        return s

    def remove_trivial_variables(s):
        '''
            Removes substring septerated by , which dont have symbol 'ss'
        '''
        idx = s.rfind(ss)
        if idx != -1:
            val1 = s[0:idx + 1]
            val2 = s[idx+1:-1]
            values = val2.split(", ")

            return val1 + values[0]
        return None


    with open(file_read) as f_read:
        with open(file_write, "w") as f_write:
            append_to_file = True
            
            for s in f_read:
                [s_new, append_to_file] = remove_inner_entry(s, append_to_file)

                if (s_new != None):
                    s_new = remove_prefix_function(s_new, start[0:-1])
                    s_new = remove_trivial_variables(s_new)#, "_")
                    if (s_new !=None):
                        f_write.write(s_new + "\n")


start = "proof{"
end = "}"

file_read = f"{PL_DIR}/p.txt"
file_write = f"{PL_DIR}/p_red.txt"
symbol_needed = '⊢'


remove_substrings_from_file(file_read, file_write, start, end, symbol_needed)