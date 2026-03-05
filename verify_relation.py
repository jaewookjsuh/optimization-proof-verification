from numbers import Number

def is_number(ob):
    return isinstance(ob, Number)



class Relation():
    relation_str = 'R'
    relation_repr = 'R'
    istrue = 2

    def __init__(self, lhs, rhs):
        self.args = (lhs, rhs)
        self.lhs = lhs
        self.rhs = rhs

    def __str__(self):
        s = str(self.args[0]) + self.relation_str + str(self.args[1])
        return s

    def __repr__(self):
        s = repr(self.args[0]) + self.relation_repr + repr(self.args[1])
        return s

    def _repr_latex_(self):
        return "$\\displaystyle %s$" % repr(self)
    
    def __eq__(self, other):
        if isinstance(other, type(self)):
            return self.lhs == other.lhs and self.rhs == other.rhs

    def __hash__(self):
        return hash((self.lhs, self.relation_str, self.rhs))

    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        result = set()
        for arg in self.args:
            if not is_number( arg ):
                result = result.union( arg.get_inde_Point() )
        return result

    ## Method to get 'free variables' for IP as set
    def get_inde_IP(self):
        result = set()
        for arg in self.args:
            if not is_number( arg ):
                result = result.union( arg.get_inde_IP() )
        return result

    ## Method to get 'free variables' for IP as set
    def get_inde_FV(self):
        result = set()
        for arg in self.args:
            if not is_number( arg ):
                result = result.union( arg.get_inde_FV() )
        return result

    ## Get 'free variable' for scalars
    def get_inde_scalar(self):
        result = set()
        for arg in self.args:
            if not is_number( arg ):
                result = result.union( arg.get_inde_FV() )
        return result

    def substitute(self, sub_dict):
        substituted_rel = type(self)(self.args[0].substitute(sub_dict), self.args[1].substitute(sub_dict) )
        substituted_rel.istrue = self.istrue
        return substituted_rel
    
    def simplify(self):
        try:
            lhs = self.lhs.simplify()
        except:
            lhs = self.lhs
        try:
            rhs = self.rhs.simplify()
        except:
            rhs = self.rhs
        result = type(self)(lhs,rhs)
        result.istrue = self.istrue
        return type(self)(lhs,rhs)


class Equal(Relation):
    relation_str = " = "
    relation_repr = " = "

    def eq_trans(self, eq2):
        if self.args[1] == eq2.args[0]:
            eq = Equal(self.args[0],eq2.args[1])
            eq.istrue = 1
            return eq
        else:
            raise TypeError( "Can't apply transitivity.")

    def eq_sym(self):
        eq = Equal(self.args[1], self.args[0])
        eq.istrue = 1
        return eq

    def typecheck(self):
        if type(self.lhs) is type(self.rhs):
            return type(self.lhs)
        else: raise TypeError( "LHS and RHS have different types" )


class le(Relation):
    relation_str = " <= "
    relation_repr = " \\le "

class lt(Relation):
    relation_str = " < "
    relation_repr = " < "

class ge(Relation):
    relation_str = " >= "
    relation_repr = " \\ge "

class gt(Relation):
    relation_str = " > "
    relation_repr = " > "


# Helper for raw Python number comparisons.
def le_of_numbers(a,b):
    if is_number(a) and is_number(b):
        if a<=b:
            result = le(a,b)
            result.istrue = 1
        else: result = lt(b,a)
        return result
    else: 
        raise TypeError( "Please check the input types")

def lt_of_numbers(a,b):
    if is_number(a) and is_number(b):
        if a<b:
            result = lt(a,b)
            result.istrue = 1
        else: result = le(b,a)
        return result
    else: 
        raise TypeError( "Please check the input types")

