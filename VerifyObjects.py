from VerifyRelation import *

####--------------------------------------------- Ancestor object for verify objects -----------------------------------------------####
class VerifyObject():
    name = ""
    is_scalar = False
    is_vector = False
    is_IP = False
    is_FV = False
    is_Matrix = False

    ###------- Addition and subtraction -------###
    def __add__(self, other):
        if is_vector(self) and is_vector(other):
            return self.vec_vec_add(other)
        elif is_scalar_or_number(self) and is_scalar_or_number(other) :
            return self.scal_scal_add(other)
        if is_matrix(self) and is_matrix(other):
            return self.__add__(other)
        else:
            raise TypeError( "Can't add " +  str(self) + ' of type ' + str(type(self)) + " with " + str(other) + ' of type ' + str(type(other)) )

    __radd__ = __add__

    def __sub__(self, other):
        return self.__add__(-other)

    def __rsub__(self, other):
        return (-self).__add__(other)

    ###------- Multiplication -------###
    def __mul__(self, other):
        ## both are scalars
        if is_scalar_or_number(self) and is_scalar_or_number(other):
            if is_scalar(self):
                return self.scal_scal_mul(other)
            elif is_scalar(other):
                return other.scal_scal_mul(self)
        ## one scalar, one vector
        elif is_vector(self) and is_scalar_or_number(other):
            return self.scal_vec_mul(other)
        elif is_scalar_or_number(self) and is_vector(other):
            return other.scal_vec_mul(self)
        ## both are vectors
        elif is_vector(self) and is_vector(other):
            raise TypeError( "Can't multiply vector with vector" )
        ## When eitherone is matrix
        elif is_matrix(self):
            return self.__mul__(other)
        elif is_matrix(other):
            return other.__mul__(self)


    __rmul__ = __mul__

    def __pos__(self):
        return self

    def __neg__(self):
        return self.__mul__(-1)

    def __truediv__(self, other):
        if is_scalar_or_number(other):
            return self.__mul__( ScalarPow(other, -1) )
        else:
            raise TypeError( "Can't divide with " + str(type(other)) )

    def __rtruediv__(self, other):
        if is_scalar_or_number(self):
            return ScalarPow(self, -1).__mul__( other )
        else:
            raise TypeError( "Can't divide with " + str(type(self)) )

    def __str__(self):
        return self.name

    def __repr__(self):
        s = str(self)
        s = s.replace(PowStr, '^')
        s = s.replace(MulScalVecStr, ' ')
        s = s.replace(MulScalScalStr, ' ')
        return s

    def _repr_latex_(self):
        return "$\\displaystyle %s$" % repr(self)

    ###------- Declaring inequality -------###
    def __ge__(self, other):
        return ge(self, other)

    def __le__(self, other):
        return le(self, other)
    
    # def __lt__(self, other):
    #     return lt(self, other)

    # def __gt__(self, other):
    #     return gt(self, other)

    ## We may want to think objects with same type and expression as same obejct
    def __eq__(self, other):
        if type(self)==type(other):
            return str(self)==str(other)
        else:
            return False

    ## To gather objects in set, __hash__ is required
    def __hash__(self):
        return hash( str(type(self)) + str(self) )

    ## This checks if the obejct is 'zero' for each class
    def is_zero(self):
        if self == 0 or self == ZeroVector:
            return True
        expanded_input = self.expand()
        if is_scalar_or_number(expanded_input):
            return expanded_input == 0
        elif is_vector(expanded_input):
            return expanded_input.equals(ZeroVector)
        elif is_matrix(expanded_input):
            for row_list in expanded_input.mat:
                for entry in row_list:
                    if is_scalar_or_number(entry):
                        if entry!=0:
                            return False
                    elif not entry.is_zero():
                        return False
            return True

    ## When we check if an object is zero, we expand all terms by distribution law
    def expand(self):
        return self

    ## Repeat expand until it stops to change
    def simplify(self):
        result = self
        while True:
            try:
                new_result = result.expand()
                if result != new_result:
                    result = new_result
                else:
                    break
            except:
                break
        return result

    def substitute(self, equality):
        if equality.lhs == self:
            return equality.rhs
          # elif equality.rhs == self: return equality.lhs.  <- First leave this part to prevent unwanted way of substitution
        else:
            return self


MulScalVecStr = " * "
MulScalScalStr = " * "
PowStr = "**"

####-------- Class for sorting and organizing args ------####
class ArgsOrganizer():
    ## Sort args with str of each arg
    def sort_args(self, args):
        str_dict = {}
        list_to_sort = []
        for i in range(len(args)):
            str_dict[str(args[i])] = i
            list_to_sort.append(str(args[i]))
        sorted_list = sorted( list_to_sort )
        for j in range(len(sorted_list)):
            sorted_list[j] = args[ str_dict[ sorted_list[j] ] ]
        return tuple(sorted_list)

###------------------------------------------ Orgnizers for args for each classes ---------------------------------------###

    ## For ScalarMul class, a*a becomes ScalarPow(a,2)
    def organize_ScalarMul_args(self, args):
        inde_scalars = set()
        new_args_dict = {}
        for arg in args:
            inde_scalar = arg.base
            if inde_scalar in inde_scalars:
                new_args_dict[inde_scalar] = new_args_dict[inde_scalar] + arg.exponent
            else:
                inde_scalars.add(inde_scalar)
                new_args_dict[inde_scalar] = arg.exponent
        # gather new_args
        new_args = ()
        for arg in new_args_dict:
            # if new_arg==1, skip it
            if not new_args_dict[arg] == 0:
                new_args += ( ScalarPow( arg, new_args_dict[arg] ), )
        return self.sort_args( new_args )

    ## For ScalarAdd class, a+a becomes ScalarMul(2,a,1,1)
    def organize_ScalarAdd_without_IP_FV(self, constant, args):
        inde_args = set()
        new_args_dict = {}
        for arg in args:
            if arg==0:  ## May not be necessary. Ignore if arg equals zero.
                continue
            if type(arg)==ScalarMul:
                inde_arg = arg.args
            else:
                inde_arg = (arg,)   ## for Scalar, ScalarPow : a should be identified with (a,)
            if inde_arg in inde_args:     # if inde_arg is already in inde_args, add num_coeffi to previous num_coeffi
                new_args_dict[inde_arg] = new_args_dict[inde_arg] + arg.num_coeffi
            else:   # if inde_arg is not in inde_args, add it inde_args and initialize num_coeffi
                inde_args.add( inde_arg )
                new_args_dict[inde_arg] = arg.num_coeffi
        # gather new_constant and new_args
        new_constant = constant
        new_args = ()
        for arg in new_args_dict:
            new_arg_num_coeffi = new_args_dict[arg]
            arg_to_append = ScalarMul( new_arg_num_coeffi, arg, 1, 1 )
            if is_number( arg_to_append ):
                new_constant += arg_to_append
            else:
                new_args += ( arg_to_append, )
        return new_constant, self.sort_args( new_args )

    ## For ScalarAdd class, IP(v,v)+IP(v,v) becomes ScalarMul(2,1,IP(v,v),1)
    def organize_ScalarAdd_with_IP_FV(self, args, inde_IPs, inde_FVs):
        non_IP_FV_terms = 0
        new_IPs_dict = {}
        new_FVs_dict = {}
        for IP in inde_IPs:
            new_IPs_dict[IP] = 0
        for FV in inde_FVs:
            new_FVs_dict[FV] = 0
        for arg in args:
            if arg==0:  ## May not be necessary. Ignore if arg equals zero.
                continue
            if arg.IP_term in inde_IPs:
                if type(arg)==ScalarMul:
                    new_IPs_dict[arg.IP_term] = new_IPs_dict[arg.IP_term] + ScalarMul( arg.num_coeffi,arg.args, 1, 1)
                else:   # if arg contains IP_term but not is ScalarMul type, it is IP
                    new_IPs_dict[arg.IP_term] = new_IPs_dict[arg.IP_term] + 1
            elif arg.FV_term in inde_FVs:
                if type(arg)==ScalarMul:
                    new_FVs_dict[arg.FV_term] = new_FVs_dict[arg.FV_term] + ScalarMul( arg.num_coeffi,arg.args, 1, 1)
                else:   # if arg contains FV_term but not is ScalarMul type, it is FV
                    new_FVs_dict[arg.FV_term] = new_FVs_dict[arg.FV_term] + 1
            else:
                non_IP_FV_terms = non_IP_FV_terms + arg
        # Initiallize new_args with non_IP_FV_terms
        if type(non_IP_FV_terms)==ScalarAdd:
            new_args = non_IP_FV_terms.args
        elif non_IP_FV_terms==0:
            new_args = ()
        else:
            new_args = ( non_IP_FV_terms, )
        # gather IP and FV terms in new_args
        for IP in new_IPs_dict:
            new_args += ( new_IPs_dict[IP] * IP, )
        for FV in new_FVs_dict:
            new_args += ( new_FVs_dict[FV] * FV, )
        return self.sort_args( new_args )

    ## For VectorAdd class, v+v becomes VectorMul(2,v)
    def organize_VectorAdd_args(self, args):
        inde_vecs = set()
        new_args_dict = {}
        for arg in args:
            inde_vec = arg.vector
            if inde_vec in inde_vecs:
                new_args_dict[inde_vec] = new_args_dict[inde_vec] + arg.coeffi
            else:
                inde_vecs.add(inde_vec)
                new_args_dict[inde_vec] = arg.coeffi
        # gather new_args
        new_args = ()
        for arg in new_args_dict:
            # if coefficient is zero, skip it
            if not new_args_dict[arg] == 0:
                new_args += ( VectorMul( new_args_dict[arg], arg ), )
        return self.sort_args( new_args )


####------------- Functions to check types of objects ------------####

## Return True if obejct is python number class
from numbers import Number
def is_number(ob):
    return isinstance(ob, Number)

## Return True if obejct is scalar object in verify or python number class
def is_scalar(ob):
    try:
        return ob.is_scalar
    except:
        return False
def is_scalar_or_number(ob):
    try:
        return ob.is_scalar
    except:
        return isinstance(ob, Number)

## Return True if obejct is vector object in verify
def is_vector(ob):
    try:
        return ob.is_vector
    except:
        return False

## Return True if obejct is VerifyMatrix object in verify
def is_matrix(ob):
    try:
        return ob.is_Matrix
    except:
        return False




####--------------------------------------------- Scalars -----------------------------------------------####

###------- Base scalar -------###
class Scalar(VerifyObject):
    is_scalar = True
    is_real = True
    ## initializing defaul setting
    is_integer = False
    is_positive = False
    is_negative = False
    is_nonnegative = False
    num_coeffi = 1
    exponent = 1
    IP_term = 1
    FV_term = 1

    def __init__(self, name, **kwargs):
        self.name = name
        self.base = self

    def __pow__(self, other):
        return ScalarPow(self, other)


    ## Addition between scalars
    def scal_scal_add(self, other):
        if self==0:
            return other
        if other==0:
            return self
        if type(self)==ScalarAdd and type(other)==ScalarAdd:
            return ScalarAdd( self.constant + other.constant , self.args + other.args )
        elif type(self)==ScalarAdd:
            if is_number(other):
                return ScalarAdd( self.constant + other, self.args )
            else:
                return ScalarAdd( self.constant, self.args + (other,) )
        elif type(other)==ScalarAdd:
            if is_number(self):
                return ScalarAdd( other.constant + self, other.args )
            else:
                return ScalarAdd( other.constant, other.args + (self,) )
        else:
            if is_number(self):
                return ScalarAdd( self, (other,) )
            elif is_number(other):
                return ScalarAdd( other, (self,) )
            else:
                return ScalarAdd( 0, (self , other) )

    ## Multiplication between scalars
    def scal_scal_mul(self, other):
        if self==0 or other==0:
            return 0
        if self==1:
            return other
        if other==1:
            return self
        parsed_self = self.parse_to_tuple(self)
        parsed_other = self.parse_to_tuple(other)
        result = ScalarMul( parsed_self[0] * parsed_other[0] ,
                            parsed_self[1] + parsed_other[1]  ,
                            self.IP_Mul( parsed_self[2], parsed_other[2] ) ,
                            self.FV_Mul( parsed_self[3], parsed_other[3] ) )
        return result

    ## For operations, parse scalar object(including python numbers) to tuple
    def parse_to_tuple(self, ob):
        if type(ob)==ScalarMul:
            return (ob.num_coeffi, ob.args, ob.IP_term, ob.FV_term)
        elif type(ob)==Scalar or type(ob)==ScalarPow:
            return (1, (ob,), 1, 1)
        elif is_number(ob):
            return (ob, (), 1, 1)
        elif type(ob)==IP:
            return (1, (), ob, 1)
        elif type(ob)==FV:
            return (1, (), 1, ob)
        else:
            return (1, (ob,) , 1, 1)

    ## For now, we don't consider IP*IP but later may not
    def IP_Mul(self, IP1, IP2):
        if IP1==1:
            return IP2
        elif IP2==1:
            return IP1
        else:
            raise TypeError( "For now, can't multiply " + str(type(IP1)) + " with " + str(type(IP2)) )

    ## For now, we don't consider FV*FV but later may not
    def FV_Mul(self, FV1, FV2):
        if FV1==1:
            return FV2
        elif FV2==1:
            return FV1
        else:
            raise TypeError( "For now, can't multiply " + str(type(FV1)) + " with " + str(type(FV2)) )

    ## Get 'free variable' for scalars for organization
    def get_inde_scalar(self):
        return { self }

    ## Get 'free variable' of IP terms
    def get_inde_IP(self):
        return set()

    ## Get 'free variable' of FV terms
    def get_inde_FV(self):
        return set()

    ## when self!=ScalarAdd, distribution_law returns basic multiplication
    def distribution_law(self, coeffi):
        return self * coeffi

    
###------- a * b  -------###
class ScalarMul(Scalar):
    def __init__(self, num_coeffi, args, IP_term, FV_term):
        self.num_coeffi = num_coeffi
        self.args = self.organize_args(args)
        self.IP_term = IP_term
        self.FV_term = FV_term

    ## For each cases, other types of objects shoul be returned
    def __new__(cls, num_coeffi, args, IP_term, FV_term):
        organize_args = cls.organize_args(cls, args)
        no_coeffi = num_coeffi==1
        no_args = organize_args==()
        no_IP = IP_term==1
        no_FV = FV_term==1
        if num_coeffi==0:
            return 0
        if (not no_IP) and (not no_FV):
            raise TypeError( "For now, can't multiply" + str(type(IP_term)) + " with " + str(type(FV_term)) )
        if no_args and no_IP and no_FV:
            return num_coeffi             # python number
        elif no_coeffi and no_args and no_IP:
            return FV_term
        elif no_coeffi and no_args and no_FV:
            return IP_term
        elif no_coeffi and no_IP and no_FV:
            if len(organize_args)==1:
                return organize_args[0]
            else:
                return super().__new__(cls)
        else:
            return super().__new__(cls)

    def __str__(self):
        s = ""
        if self.num_coeffi==-1:
            s += "-" #+ MulScalScalStr
        elif not self.num_coeffi==1:
            s += str(self.num_coeffi) + MulScalScalStr
        if not self.args == ():
            for i in range( len(self.args)-1 ):
                if type( self.args[i] ) == ScalarAdd:
                    s += "( " + str( self.args[i] ) + " )" + MulScalScalStr
                else:
                    s += str( self.args[i] ) + MulScalScalStr
            if type( self.args[-1] ) == ScalarAdd:
                s += "( " + str( self.args[-1] ) + " )"
            else:
                s += str( self.args[-1] )
        if not self.FV_term==1:
            s += MulScalScalStr + str(self.FV_term)
        if not self.IP_term==1:
            s += MulScalScalStr + str(self.IP_term)
        return s

    def __pow__(self, other):
        powered_num_coeffi = self.num_coeffi**other # should be changed later
        powered_args_list = []
        for arg in self.args:
            powered_args_list.append(arg**other)
        powered_args = tuple(powered_args_list)
        powered_IP_term = self.IP_term**other
        powered_FV_term = self.FV_term**other
        return ScalarMul(powered_num_coeffi, powered_args, powered_IP_term, powered_FV_term)
    
    ## Get 'free variable' for scalars for organization
    def get_inde_scalar(self):
        inde_scalars = set()
        for arg in self.args:
            inde_scalars.union( arg.get_inde_scalar() )
        return inde_scalars

    ## Organize exponents, ex) if args=(a,a), it becomse args=(ScalarPow(a,2),)
    def organize_args(self, args):
        og = ArgsOrganizer()
        return og.organize_ScalarMul_args(args)

    ## Get 'free variable' of IP terms
    def get_inde_IP(self):
        if self.IP_term==1:
            return set()
        else:
            return { self.IP_term }

    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        if self.IP_term==1:
            return set()
        else:
            return self.IP_term.get_inde_Point()

    ## Get 'free variable' of FV terms
    def get_inde_FV(self):
        if self.FV_term==1:
            return set()
        else:
            return { self.FV_term }

    ## For example, 3a(b+c)d <v,w> = 3abd <v,w> + 3acd <v,w>
    def expand(self):
        result = 0
        if self.IP_term==1: ## May not be necessary. Expanding IP term if it is not 1.
            coeffi_for_args = self.num_coeffi * self.IP_term * self.FV_term
        else:
            coeffi_for_args = self.num_coeffi * self.IP_term.expand() * self.FV_term
        expanded_args = self.args_expansion( self.args )
        if expanded_args==():
            return coeffi_for_args
        else:
            if expanded_args==0:  ## May be changed. Return 0 when args has only 0.
                return 0
            return expanded_args.distribution_law(coeffi_for_args)


    ## For exmaple, a(b+c)d = abd + acd
    def args_expansion(self, args_to_expand):
        if len(args_to_expand)==0:
            return args_to_expand
        if len(args_to_expand)==1:
            return args_to_expand[0].expand()
        else:
            result = 0
            expanded_term = self.args_expansion(args_to_expand[1:])
            if not type(expanded_term)==ScalarAdd:
                return args_to_expand[0].expand().distribution_law(expanded_term)
            for expaned_arg in expanded_term.args:
                result = result + args_to_expand[0].expand().distribution_law(expaned_arg)
            result = result + args_to_expand[0].distribution_law(expanded_term.constant)
            return result.expand()

    ## Recalculate terms with substituted terms
    def substitute(self, sub_dict):
        result = self.num_coeffi
        for arg in self.args:
            result *= arg.substitute(sub_dict)
        try:
            result *= self.IP_term.substitute(sub_dict)
        except:
            result *= self.IP_term
        try:
            result *= self.FV_term.substitute(sub_dict)
        except:
            result *= self.FV_term
        return result

###----- a + b -----###    
class ScalarAdd(Scalar):
    def __init__(self, constant, args):
        self.constant, self.args = self.organize_args(constant, args)
        self.base = self

    ## For each cases, other types of objects shoul be returned
    def __new__(cls, constant, args):
        if args==():
             return constant
        if constant==0 and len(args)==1:
             return args[0]
        new_constant, organized_args = cls.organize_args(cls, constant, args)
        if organized_args==():
            return new_constant
        if new_constant==0 and len(organized_args)==1:
            return organized_args[0]
        return super().__new__(cls)

    def __str__(self):
        s = ""
        if not self.constant==0:
            s += str(self.constant)
            if self.args[0].num_coeffi<0:
                s += str(self.args[0])
            else:
                s += "+" + str(self.args[0])
        else:
             s += str(self.args[0])
        # len(self.args)>0 since if not, it is constant so python number object
        # If num_coeffi<0, erase "+" to avoid representation like a+ -b
        if len(self.args)>1:
            for i in range( 1, len(self.args) ):
                try: # XXX 임시방편
                    if self.args[i].num_coeffi<0:
                        s += str( self.args[i] )
                    else:
                        s += "+" + str( self.args[i] )
                except:
                        s += "+" + str( self.args[i] )
        return s

    ## we dont want to see a-(b+c) as a+(-1)(b+c)
    def __neg__(self):
        new_args = ()
        for arg in self.args:
            new_args += (-arg,)
        return ScalarAdd(-self.constant, new_args)
    
    def __pow__(self, other):
        return ScalarPow(self, other)


    ## Get 'free variable' for scalars for organization
    def get_inde_scalar(self):
        inde_scalars = set()
        for arg in self.args:
            inde_scalars.union( arg.get_inde_scalar() )
        return inde_scalars

    ## Get all 'independent IP' terms exist in Add
    def get_inde_IP(self):
        inde_IPs = set()
        for arg in self.args:
            inde_IPs = inde_IPs.union( arg.get_inde_IP() )
        return inde_IPs


    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        inde_Points = set()
        for arg in self.args:
            inde_Points = inde_Points.union( arg.get_inde_Point() )
        return inde_Points

    ## Get all 'independent FV' terms exist in Add
    def get_inde_FV(self):
        inde_FVs = set()
        for arg in self.args:
            inde_FVs = inde_FVs.union( arg.get_inde_FV() )
        return inde_FVs

    ## Organize as linear combination, ex) change a+a to ScalarMul(2, (a,), 1, 1) = 2a
    def organize_args(self, constant, args):
        og = ArgsOrganizer()

        ## Gather IP and FV terms in args
        inde_IPs, inde_FVs = set(), set()
        for arg in args:
            if arg !=0:  #XXX 임시방편
                inde_IPs = inde_IPs.union( arg.get_inde_IP() )
                inde_FVs = inde_FVs.union( arg.get_inde_FV() )

        ## Treat each cases differently : with/without IP or FV terms
        if inde_IPs==set() and inde_FVs==set():
            return og.organize_ScalarAdd_without_IP_FV(constant, args)
        else:
            return constant, og.organize_ScalarAdd_with_IP_FV(args, inde_IPs, inde_FVs)

    ## ex) 1 + a + (b+c)d = 1 + a + bd + cd
    def expand(self):
        result = 0
        for arg in self.args:
            try: # 임시방편
                result = result + arg.expand()
            except:
                result = result + arg
        result = result + self.constant
        return result

    ## if self = a+b+c, coeffi=d, then return ad + bd + cd
    def distribution_law(self, coeffi):
        result = 0
        result = result + self.constant * coeffi
        for arg in self.args:
            result = result + arg * coeffi
        return result

    def substitute(self, sub_dict):
        result = self.constant
        for arg in self.args:
            result += arg.substitute(sub_dict)
        return result
    
###----- a^2 -----### 
class ScalarPow(Scalar):
    def __init__(self, base, exponent):
        self.base = base
        self.exponent = exponent

    def __new__(cls, base, exponent):
        if exponent==0:
            return 1
        if exponent==1:
            return base
        if is_number(base) and is_number(exponent):
            return base**exponent
        return super().__new__(cls)

    def __str__(self):
        if type(self.base)==ScalarAdd:
            return "(" + str(self.base) + ")"+ "**{" + str(self.exponent) + "}"
        return str(self.base) + "**{" + str(self.exponent) + "}"

    ## (x**a)**b = x**(ab)
    def __pow__(self, index):
        return ScalarPow(self.base, self.exponent * index )

    ## Get 'free variable' for scalars for organization
    def get_inde_scalar(self):
        return { self.base }

    ## For exmaple, (a+b)^2= a^2 + 2ab + b^2
    def expand(self):
        expanded_base = self.base.expand()
        if type( expanded_base ) != ScalarAdd:
            return expanded_base ** self.exponent
        exp = self.exponent
        if is_number(self.exponent):
            if int(exp)==exp and exp>0:
                return self.poly_expansion(expanded_base, exp)
        return self

    ## expand ( a_1 + ... + a_n)^n
    def poly_expansion(self, ScalAdd, n):
        if n==1:
            return ScalAdd
        else:
            result = 0
            expanded_term = self.poly_expansion(ScalAdd, n-1)
            for expaned_arg in expanded_term.args:
                result = result + ScalAdd.distribution_law(expaned_arg)
            result = result + ScalAdd.distribution_law(expanded_term.constant)
            return result

    def substitute(self, sub_dict):
        try:
            base = self.base.substitute(sub_dict)
        except:
            base = self.base
        try:
            exponent = self.exponent.substitute(sub_dict)
        except:
            exponent = self.exponent
        return ScalarPow(base,exponent)
    

class Sqrt(ScalarPow):
    def __init__(self, inside):
        self.base = inside
        self.exponent = 1/2

    def __new__(cls, inside):
        if type(inside)==Scalar:
            return super().__new__(cls, inside, 1/2)
        else:
            return inside**(1/2)




####-------------------- Vectors ---------------####

###------- Base vector, v -------###
class Vector(VerifyObject):
    is_vector = True
    coeffi = 1

    def __init__(self, name):
        self.name = name
        self.vector = self

    ## Addition between two vectors
    def vec_vec_add(self, other):
        if self == ZeroVector:
            return other
        if other == ZeroVector:
            return self
        if type(self)==VectorAdd:
            if type(other)==VectorAdd:
                return VectorAdd( self.args + other.args )
            else:
                return VectorAdd( self.args + (other,) )
        else:  ## i.e. self is not a VectorAdd object
            if type(other)==VectorAdd:
                return VectorAdd( (self,) + other.args )
            else:
                return VectorAdd( (self , other) )

    ## Scalar multiplication for vector
    def scal_vec_mul(self, scalar):
        if type(self)==VectorMul:
            return VectorMul( scalar * self.coeffi , self.vector )
        elif type(self)==VectorAdd:
            return self.distribution_law(scalar)
        else:
            return VectorMul( scalar, self)

    ## Method to get 'free variables' for vector as set
    def get_inde_vec(self):
        return { self }

    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        return set()

    ## Alternative for ==, avoiding hashable issue
    def equals(self,other):
        return self - other == ZeroVector

    ## For Pretty printing,
    def check_minus_sign_in_coeffi(self):
        if is_number(self.coeffi):
            if self.coeffi<0:
                return True
            else:
                return False
        else:
            if self.coeffi.num_coeffi < 0:
                return True
            else:
                return False
            
###--- ZeroVector object : to define method 'equals' for vectors ---###
class ZeroVectorClass(Vector):
    def __str__(self):
        return "O"

    def __repr__(self):
        return "O"

    def _repr_latex_(self):
        return "$\\displaystyle %s$" % repr(self)

    def __hash__(self):
        return hash("ZeroVector")

    def __neg__(self):
        return self

ZeroVector = ZeroVectorClass("Zerovector")


###--- Class scalar multiple of vector  a * v ---###
class VectorMul(Vector):
    def __init__(self, coeffi, vector):
        self.coeffi = coeffi
        self.vector = vector

    def __new__(cls, coeffi, vector):
        if coeffi==0:
            return ZeroVector
        if coeffi==1:
            return vector
        return super().__new__(cls)

    def __str__(self):
        s = ""
        if type(self.coeffi) == ScalarAdd:
            s += "( " + str(self.coeffi) + " )"
            s += MulScalVecStr
        elif self.coeffi==1:
            s += ""
        elif self.coeffi==-1:
            s += "-"
        else:
            s += str(self.coeffi)
            s += MulScalVecStr
        if type(self.vector) == VectorAdd:
            return s + "( " + str(self.vector) + " )"
        else:
            return s + str(self.vector)

    ## Method to get 'free variables' for vector as set
    def get_inde_vec(self):
        return { self.vector }

    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        return self.vector.get_inde_Point()

    ## ex) (a+b)^2 * v = (a^2 + 2ab + b^2) * v
    def expand(self):
        try:
            return self.coeffi.expand() * self.vector
        except:
            return self

    def substitute(self, sub_dict):
        try:
            coeffi = self.coeffi.substitute(sub_dict)
        except:
            coeffi = self.coeffi
        vector = self.vector.substitute(sub_dict)
        return coeffi * vector


###--- v + w ---###
class VectorAdd(Vector):
    def __init__(self, args):
        self.args = self.organize_args(args)

    def __new__(cls, args):
        organized_args = cls.organize_args(cls, args)
        if organized_args == ():
            return ZeroVector
        elif len(organized_args) == 1:
            return organized_args[0]
        return super().__new__(cls)

    def __str__(self):
        s = ""
        s += str(self.args[0])
        for i in range( 1, len(self.args) ):
            if self.args[i].check_minus_sign_in_coeffi():
                s += str( self.args[i] )
            else:
                s += " + " + str( self.args[i] )
        return s

    ## For VectorAdd,
    def distribution_law(self, scalar):
        result_args = ()
        for arg in self.args:
            arg_to_add = arg.scal_vec_mul(scalar)
            if arg_to_add != ZeroVector:
                result_args += (arg_to_add,)
        return VectorAdd(result_args)

    ## Method to get 'free variables' for vector as set
    def get_inde_vec(self):
        inde_vecs = set()
        for arg in self.args:
            inde_vecs.add( arg.vector )
        return inde_vecs

    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        inde_Points = set()
        for arg in self.args:
            inde_Points = inde_Points.union( arg.vector.get_inde_Point() )
        return inde_Points

    ## Organize linear combination with indepedent variables
    def organize_args(self, args):
        og = ArgsOrganizer()
        return og.organize_VectorAdd_args(args)

    ## expansion for scalar coefficient : ex) (a+b)^2 * v + w = (a^2 + 2ab + b^2) * v + w
    def expand(self):
        result = ZeroVector
        for arg in self.args:
            result = result + arg.expand()
        return result

    def substitute(self, sub_dict):
        result = ZeroVector
        for arg in self.args:
            result += arg.substitute(sub_dict)
        return result
    

######--------------------------- Subclasses -----------------------------------######

#####------ Subclasses for scalars ------#####

####--- Inner Product ---####
class IP(Scalar):
    is_IP = True

    def __init__(self, args0, args1):
        if ( not is_vector(args0) ) or ( not is_vector(args1) ):
            raise TypeError( "Can't innerproduct" + str(type(args0)) + " with " + str(type(args1)) )
        og = ArgsOrganizer()
        self.args = og.sort_args( (args0, args1) )
        self.IP_term = self
        self.base = self

    ## change IP expression to <,> and ||.||^2
    def __str__(self):
        if self.args[0]==self.args[1]:
            s = "|| " + str(self.args[0]) + " ||^2"
        else:
            s = "< "+ str(self.args[0]) + ', ' + str(self.args[1]) + " >"
        return s

    ## change IP expression to <,> and ||.||^2
    def __repr__(self):
        if self.args[0]==self.args[1]:
            s = "|| " + repr(self.args[0]) + " ||^2"
        else:
            s = "\langle "+ repr(self.args[0]) + ', ' + repr(self.args[1]) + "\\rangle"
        return s

    ## Get 'free variable' of IP terms
    def get_inde_IP(self):
        return { self }

    ## Get 'free variable' of FV terms
    def get_inde_FV(self):
        return set()

    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        result = set()
        result = result.union( self.args[0].get_inde_Point() )
        result = result.union( self.args[1].get_inde_Point() )
        return result

    def expand(self):
        result = 0
        if type(self.args[0])==VectorAdd and type(self.args[1])==VectorAdd:
            for arg_0 in self.args[0].args:
                for arg_1 in self.args[1].args:
                    result += IP(arg_0, arg_1)
        elif type(self.args[0])==VectorAdd:
            for arg_0 in self.args[0].args:
                result += IP(arg_0, self.args[1])
        elif type(self.args[1])==VectorAdd:
            for arg_1 in self.args[1].args:
                result = IP(self.args[0], arg_1)
        else:
            return self.args[0].coeffi * self.args[1].coeffi * IP(self.args[0].vector, self.args[1].vector)
        return result

    def substitute(self, sub_dict):
        arg0 = self.args[0].substitute(sub_dict)
        arg1 = self.args[1].substitute(sub_dict)
        return IP(arg0, arg1)

# square
class Square(IP):
    def __init__(self, arg):
        super().__init__(arg, arg)


####----- Function Value ----####
class FV(Scalar):
    is_FV = True

    def __init__(self, name, x):
        super().__init__(name)
        self.input = x
        self.FV_term = self

    def __str__(self):
        s = self.name + "(" + str(self.input) + ")"
        return s

    ## Get 'free variable' of IP terms
    def get_inde_IP(self):
        return set()

    ## Get 'free variable' of FV terms
    def get_inde_FV(self):
        return { self }

    def substitute(self, sub_dict):
        new_input = self.input.substitute(sub_dict)
        if self.input!=new_input:
            return FV(self.name, new_input)
        else:
            return super().substitute(sub_dict)

## class inherits Function to produce FV object
class Function():
    def __init__(self, name):
        self.name = name

    def __call__(self,x):
        return FV(self.name, x)



###--- IterationCount ---###
## class for object about number of iteration, iteration may start with 0 or 1
## keyword argument assumptions are not yet implemented
class IterationCount(Scalar):
    is_integer = True

    def __init__(self, name, **kwargs):
        if 'start' in kwargs:
            if kwargs['start'] == 0:
                return Scalar.__init__(self, name, integer=True, negative=False, **kwargs)
            if kwargs['start'] == 1:
                return Scalar.__init__(self, name, integer=True, positive=True, **kwargs)
        else:
            return Scalar.__init__(self, name, interger=True, positive=True, **kwargs)
        

class ScalarSequence:
    def __init__(self,name):
        self.name = name

    def __call__(self, k):
        name = self.name + "_{" + str(k) + "}"
        return Scalar(name)


#####----- Subclasses for vectors -----#####        

## class for vectors such as x^k, y^k, nable.f(x)
class Point(Vector):
    ## Method to get 'free variables' for Point as set
    def get_inde_Point(self):
        return { self }
    

####---- Operator ----####
class OV(Vector):
    is_OV = True

    def __init__(self, name, x):
        super().__init__(name)
        self.input = x
        self.OV_term = self

    def __str__(self):
        s = self.name + "(" + str(self.input) + ")"
        return s

    ## Get 'free variable' of IP terms
    def get_inde_IP(self):
        return set()

    ## Get 'free variable' of FV terms
    def get_inde_OV(self):
        return { self }

    def substitute(self, sub_dict):
        new_input = self.input.substitute(sub_dict)
        if self.input!=new_input:
            return OV(self.name, new_input)
        else:
            return super().substitute(sub_dict)


## class for Operators such as gradient
class Operator:
    def __init__(self,name):
        self.name = name
        self.zeros = []

    def __call__(self,x:Vector):
        return OV(self.name, x)

    def zero(self,name):
        v = Point(name)
        self.zeros.append(v)
        return v
    

# class to express algorithm settings with parameter k
class Sequence:
    def __init__(self, name):
        self.name = name

    def __call__(self, k):
        name = self.name + "^{" + str(k) + "}"
        return Vector(name)
