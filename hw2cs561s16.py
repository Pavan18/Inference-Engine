import re
import copy
import sys

output_file_handle = open('output.txt', 'w')
gResult=""
rResult=""
multiple=-2
retFlag=-1
filestr =""
counter = 0
globalFlag=0
visited_facts = list()


def outLog(goal,theta):
    global filestr
    if is_fact(goal):
        # filestr+="Ask:"+goal.op+"("+str(goal.terms)+")/n"
        filestr+= "Ask: "+goal.op+"("+", ".join((goal.terms))+")\n"
    else:
        count=0
        filestr+= "Ask: "+goal.op+"("
        for i in goal.terms:
            if is_variable(i) and theta.has_key(i)==False:
                if count==0:
                    filestr+= "_"
                else:
                    filestr+= ", _"
            elif is_variable(i) and theta.has_key(i)==True:
                if count==0:
                    filestr+= theta[i]
                else:
                    filestr+= ", "+theta[i]
            else:
                if(len(str(i).replace(" ",""))>1):
                    if count==0:
                        filestr+= str(i)
                    else:
                        filestr+= ", "+str(i)
            count+=1
        filestr+= ")"
        filestr+= "\n"

def printTrueLog(goal,theta):
    global filestr
    if is_fact(goal):
        # filestr+="Ask:"+goal.op+"("+str(goal.terms)+")/n"
         filestr+= "True: "+goal.op+"("+", ".join((goal.terms))+")\n"
    else:
        count=0
        filestr+= "True: "+goal.op+"("
        for i in goal.terms:
            if is_variable(i) and theta.has_key(i)==False and is_variable(theta[i]):
                if count==0:
                    filestr+= "_"
                else:
                    filestr+= ", _"
            elif is_variable(i) and theta.has_key(i)==True and is_variable(theta[i])==False:
                if count==0:
                    filestr+= theta[i]
                else:
                    filestr+= ", "+theta[i]
            else:
                if(len(str(i).replace(" ",""))>1):
                    if count==0:
                        filestr+= str(i)
                    else:
                        filestr+= ", "+str(i)
            count+=1
        filestr+= ")"
        filestr+= "\n"
    pass

def printFalseLog(goal,theta):
    global filestr
    if is_fact(goal):
        # filestr+="Ask:"+goal.op+"("+str(goal.terms)+")/n
        filestr+= "False: "+goal.op+"("+", ".join((goal.terms))+")\n"
    else:
        count=0
        filestr+= "False: "+goal.op+"("
        for i in goal.terms:
            if is_variable(i) and theta.has_key(i)==False:
                if count==0:
                    filestr+= "_"
                else:
                    filestr+= ", _"
            elif is_variable(i) and theta.has_key(i)==True:
                if i==0:
                    filestr+= theta[i]
                else:
                    filestr+= ", "+theta[i]
            else:
                if i==0:
                    filestr+= str(i)
                else:
                    filestr+= ", "+str(i)
        filestr+= ")"
        filestr+= "\n"

def extend(var, val, theta):
    _theta = theta.copy()
    _theta[var] = val
    return _theta

def unify_var(x, y, theta):
    if x in theta:
        return unify(theta[x], y, theta)
    elif y in theta:
        return unify(x, theta[y], theta)
    else:
        return extend(x, y, theta)

def is_list(x):
    return hasattr(x, '__len__')

def is_variable(x):
    return x == x.lower()

def unify (x, y, theta = {}):

    if theta == None:
        return None
    elif x == y:
        return theta

    elif isinstance(x, str) and is_variable(x):
        return unify_var(x, y, theta)
    elif isinstance(y, str) and is_variable(y):
        return unify_var(y, x, theta)
    elif isinstance(x, str) or isinstance(y, str) or not x or not y:
        return theta if x == y else None
    elif is_list(x) and is_list(y) and len(x) == len(y):
        return unify(x[1:], y[1:], unify(x[0], y[0], theta))
    else:
        return None

def subst_in_list(theta, x):
    _x = list(x)
    for var in theta:
        if var in x:
            indices = [ i for (i,j) in enumerate(x) if j == var ]
            for k in indices:
                _x[k] = theta[var]
    return _x


class Atomic():
    def __copy__(self):
        return Atomic(self.op, self.terms)

    def __hash__(self):
        return hash((self.op, tuple(self.terms)))

    def __eq__(self, other):
        return self.op == other.op and self.terms == other.terms

    def __init__(self, op, terms):
        self.op = op
        self.terms = terms


def atomify(x):
    op = ''.join(re.findall(r'(\W?\w+)\(',x))
    op=op.replace(" ","")
    terms = ''.join(re.findall(r'\(([\w+]|[\w+, \w+]*)\)',x)).replace(" ","").split(',')
    return Atomic(op,terms)

def atomify_conjuncts(x):
    return [ atomify(y) for y in x.split(' && ')] if x else []

def get_lhs(x):
    return x.split(" => ")[0] if "=>" in x else None

def get_rhs(x):
    return x.split(" => ")[-1]

def standardize(lhs, rhs, theta = None):
    global counter
    if theta is None: theta = {}
    args = []
    for x in lhs:
        for y in x.terms:
            args.append(y)

    args = args + rhs.terms


    for term in args:
        if is_variable(term):
            if term not in theta:

                counter = counter + 1
                theta[term] = "v_%d" % counter

    for x in lhs:
        x.terms = subst_in_list(theta, x.terms)
    rhs.terms = subst_in_list(theta, rhs.terms)

    return lhs, rhs

def is_fact(x):
    for i in x.terms:
        if is_variable(i):
            return False
    return True

def subst_in_predicate(theta, x):
    _x = copy.deepcopy(x)
    for var in theta:
        if var in x.terms:
            _x.terms[_x.terms.index(var)] = theta[var]

    return _x


def bc_and(KB, goals, theta, and_visited_facts):
    global retFlag

    if theta == None:
        return


    elif len(goals) == 0:
        yield theta
    else:
        first, rest = goals[0], goals[1:]

        for subst_in_or_subtree in bc_or(KB, subst_in_predicate(theta, first),and_visited_facts, theta):
            for subst_in_and_subtree in bc_and(KB, rest, subst_in_or_subtree, and_visited_facts):
                yield subst_in_and_subtree


def bc_or(KB, goal, visited_facts, theta = {}):

    global gResult
    global globalFlag
    global rResult
    global retFlag
    if not isinstance(goal, Atomic):
        goal = atomify(goal)
        gResult = atomify(gResult)
        visited_facts.append(goal)


    flag=-1

    lengthKB = len(KB)
    retFlag=0
    for i in range( 0, lengthKB):

        lhs = atomify_conjuncts(get_lhs(KB[i]))
        rhs = atomify(get_rhs(KB[i]))


        if rhs.op == goal.op:
            if flag==-1  or( retFlag==1  and unify(rhs.terms, goal.terms, theta)):
                outLog(goal,theta)
            if is_fact(rhs):

                if rhs not in visited_facts:
                    visited_facts.append(rhs)

            lhs, rhs = standardize(lhs, rhs)

            for subst_in_and_subtree in bc_and(KB, lhs, unify(rhs.terms, goal.terms, theta), visited_facts):
                if (unify(rhs.terms, goal.terms, theta)) :
                    printTrueLog(goal,unify(rhs.terms, goal.terms, subst_in_and_subtree))
                    flag=1
                yield subst_in_and_subtree
                if(goal == gResult):
                    return
            if(unify(rhs.terms, goal.terms, theta))== None and flag==-1 :
                flag=0
    globalFlag = flag;
    if flag==0:

        retFlag=1
        printFalseLog(goal,theta)


def bc_ask(KB, query):
    list = bc_or(KB, query, [], {})
    return list


def read_data(file_handle):
    no_of_queries = 1
    queries = [ str(file_handle.readline().rstrip('\r\n'))\
                for _ in xrange(no_of_queries)]
    no_of_facts = int(file_handle.readline().rstrip('\r\n'))
    KB = [ str(file_handle.readline().rstrip('\r\n'))\
            for _ in xrange(no_of_facts) ]
    return queries, KB

def main():
    global visited_facts
    global filestr
    global counter
    global gResult
    global globalFlag
    InputFileName = str(sys.argv[2])
    OutputFileName = "output.txt"
    input_file_handle = open(InputFileName, 'r')
    # output_file_handle = open(OutputFileName, 'w')
    #output_file_handle = open('output.txt','w')
    queries, KB = read_data(input_file_handle)
    queryList = queries[0].replace(" ","").split("&&")
    i=0

    for query in queryList:
        try:
            gResult = query
            tempgResult=gResult
            lists = bc_ask(KB, query)
            val = len(list(lists))
            if (val > 0):
                i=i+1
            else:
                break
        except RuntimeError:
            #Hack to handle infinite loop in var names alone
            result = "FALSE\n"
        #result = "TRUE\n" if (len(list(bc_ask(KB, query))) > 0)\
        #          else "FALSE\n"
        # output_file_handle.write(filestr)
        visited_facts = list()
        counter = 0


    if(i==len(queryList)):
        filestr+= "True"
    else:
        if(globalFlag!=0):
            filestr+= "False: "+ str(tempgResult.replace(",",", "))+"\n"
        filestr+= "False"
    output_file_handle.write(filestr)


    output_file_handle.close()
    input_file_handle.close()

if __name__ == '__main__':
    main()