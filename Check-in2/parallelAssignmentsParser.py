import sexpParser as sp

test1 = "x,y := (+ x12 y34), x"
#test2 = "x,y := (+ 12 (+ x12 y34)), x"
test2 = "x,y,z := (+ (+ 12 (+ y y34)) (- 12 x3)),  (- z112 (- 12 z)), (* x123  (+ x 12))"
test3 = "x,y := (+ x (min 1 a)), (* x y)"

#test2 = "a, b, c := (ite c b a), (vector-ref ar i), (&& (! (vector-ref ar i) b))"
#test3 = "x,y, z := (+ x12 y34), x, (+(+ x12 y34) (- z1 (+x1+12)))"
alltests = [locals()[t] for t in sorted(locals()) if t.startswith("test")]

class MyTree():

    def __init__(self):
	self.count=-1 
	self.exp0=[]

    def giveNo(self): 
        self.count=self.count+1
        return self.count

    def fff(self, nodeid,pid,  sexp):
        if (isinstance(sexp, list)):
            if(len(sexp)==3):
                i1=self.giveNo()
                i2=self.giveNo()
                y0=[nodeid, pid, sexp[0], i1, i2, [], []]    
                self.exp0.append(y0)
                self.fff(i1, nodeid, sexp[1])
                self.fff(i2, nodeid, sexp[2])
        if (isinstance(sexp, list)):
            if(len(sexp)==2):
                i1=self.giveNo()
                y0=[nodeid, pid, sexp[0], i1,  [],[],[]]    
                self.exp0.append(y0)
                self.fff(i1, nodeid, sexp[1])
        if (isinstance(sexp, list)):
            if(len(sexp)==4):
                i1=self.giveNo()
                i2=self.giveNo()
                i3=self.giveNo()
                y0=[nodeid, pid, sexp[0], i1, i2, i3, []]    
                self.exp0.append(y0)   
                self.fff(i1, nodeid, sexp[1])
                self.fff(i2, nodeid, sexp[2])
                self.fff(i3, nodeid, sexp[3])
        if (not isinstance(sexp, list)):
       	    y0=[nodeid, pid,  [], sexp, [], [], []]  
            self.exp0.append(y0)

        return self.exp0   

    def ppp(self, sexp):
        ss=""
        if (isinstance(sexp, list)):
            if(len(sexp)==3):
                ss=ss+"("+str(sexp[0])+" " +self.ppp(sexp[1])+" "+self.ppp(sexp[2])+")"     
        if (isinstance(sexp, list)):
            if(len(sexp)==2):
                ss=ss+"("+str(sexp[0])+" " +self.ppp(sexp[1])+")"
        if (isinstance(sexp, list)):
            if(len(sexp)==4):
                ss=ss+"("+str(sexp[0])+" " +self.ppp(sexp[1])+" "+self.ppp(sexp[2])+self.ppp(sexp[3])+")"     
        if (not isinstance(sexp, list)):
            if sexp not in tempDic.keys():
                ss= str(sexp)
            else:  
                ss=str(tempDic[sexp])
            
        return ss 
 
        

def parseexpr(s):
    return sp.sexp.parseString(s, parseAll=True).asList()


class ParallelAssignments(object):

    def __init__(self, passgn):
        lh_and_rh = passgn.split(':=')
        assert len(lh_and_rh) == 2
        self.raw_lhs = lh_and_rh[0].split(',')
        self.raw_rhs = map(parseexpr, lh_and_rh[1].split(','))
        assert len(self.raw_lhs) == len(self.raw_rhs)

    def __str__(self):
        return "%s :=== %s" % (", ".join(self.raw_lhs), map(str, self.raw_rhs))
        #return "%s := %s" % (", ".join(self.raw_lhs), ", ".join(map(str, self.raw_rhs)))


for t in alltests:
    print '-' * 50
    print t
    try:
        #print "rh side:   ", ParallelAssignments(t).raw_rhs  
        x= ParallelAssignments(t).raw_rhs
        lhs=ParallelAssignments(t).raw_lhs
        #print lhs  
        for i in range(0, len(lhs)):
            lhs[i]=lhs[i].rstrip()
        # We define a class MyTree instead of AST.
        # The main reason is that in the project we need to handle all sub-exps contained in expressions.
        # we convert each expression into a list of subexpressions, where each subexpression corresponds to a tuple of 7 elements
        # [idNo, parentid, op, operand1, operand2, operand3, share], 
        # idNo is the id number for each sub-expression. 
        # parentid is the id for parent 
        # op is the operator such as +, -, ite, <=, etc
        # There are at most three operands, since "ite" is involved. 
        # each operand could be an sub-exp which is nested and long. Thus, we use an id to replace the operand in the sextuple.
        #
        # We can use the id to directly access the node (subexpression), e.g., exp[id] give us the corresponding tuple (node) 
        #
        # "share" will be a list used to indicate which of the n expressions e1, e2, .., en contains this sub-expression
        # This information is needed for our project to make sure each sub-expression is evaluated once.
        # 
        # Our data structure MyTree is similar to AST, but we give an id to each subexpression. 
        # Using id, we can directly access the corresponding sub-exp by using exp[id], where exp is the list 
        # containing all the 7-tuples of the expression. 
        # Currently each subexpression has a unique id.
        # In the next step, shared subexpressions wil have an unique id so that we know this shared information and
        # can construct the C codes such that  each subexp is evaluated once.      
        # 
        # x[0] is the list for the first expression and there are len(x) expressions in x
        # All the tuples in the same exp are in the same list.
        # The class MyTree has a recursive method fff(nodeid, pid, expi) which will construct
        #  the list of 7-tuples for the expression exp where nodeid is an integer id fo the first root node of exp and pis is the parent of the node. 
        # MyTree allows to visit all nodes in the tree in pre-order, post-order, in-order etc . It is designed to replace AST here.  
        # To print out the tree, each tuple is a node, and the children are the operands (1, 2, or 3).
        
        setV=set()   # holds the set of  variables on RHS of exp  for each LHS variable 
        varMap={} # dic for variables
        tempDic={}  # dic for temperary variables 
        digits=['1', '2', '3', '4', '5', '6', '7' ,'8', '9', '0']  

        tree=MyTree()
        pii=-1
        ii=tree.giveNo()
        for kk in range(0, len(x)):     # for each of the n expressions 
            exp= tree.fff(ii, pii, x[kk][0])
            tree.count=-1
            ii=tree.giveNo()
            ll=len(exp)
            fexp=[[]]*ll
            for i in range(0, ll):
                t=exp[0] # The order of elements in exp is not according to id 
                exp.remove(exp[0])     
                fexp[t[0]]=t  # The order of elements in fexp is according to id
            #print fexp, "  (The ", kk+1, "-th expression)"
            tree.exp0=[]

            #check-in 2 the next for loop build a set of variables contained in the RHS exp
            setV = set()       
            for i in range(0, ll): 
                ss= str(fexp[i][3])
                if fexp[i][2]==[] and ss[0] not in digits: # Have not deal with boolean constant???
                    setV.add(fexp[i][3])
            varMap[lhs[kk]]= setV   # put the pair (variable, set) into the dic
            #print "variable  and its set ", lhs[kk], setV, varMap
        print varMap # the desired output by teacher

        # print out the expression with temp variables                        
 	for kk in range(0, len(x)):          
            print "temp"+lhs[kk],"=",lhs[kk]        
            tempDic[lhs[kk]]= "temp"+lhs[kk]

 	for kk in range(0, len(x)):          
            exp=x[kk][0]
            ss= tree.ppp(exp)
        #    ssexp="" 
        #    for i in range(0, len(x[kk][0])):
        #        print x[kk][0][i], "  the variable"      
        #        if x[kk][0][i] not in tempDic.keys(): 
        #            ssexp=ssexp+str(x[kk][0][i])
        #        else: 
        #            ssexp=ssexp+str(tempDic[x[kk][0][i]])
            print lhs[kk], "=", ss  # The desired output by teacher 

            
    except sp.ParseFatalException, pfe:
        print "Error:", pfe.msg
        print pfe.markInputline('^')
    print


