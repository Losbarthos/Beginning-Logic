
import pandas as pd
import numpy as np

import json

from ast import literal_eval


s = '[[[1],1,p,"A",[]],[[2],2,¬q,"A",[]],[[3],3,p→q,"A",[]],[[1,3],4,q,"→E",[1,3]],[[1,2,3],5,q∧ ¬q,"∧I",[2,4]],[[2,3],6,¬p,"¬I",[1,5]]]'



print(s)