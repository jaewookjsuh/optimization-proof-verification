from VerifyRelation import *
from VerifyObjects import *

Prop = set()
lemma = set()
tactic = set()
Var = set()

us = Scalar('us') #universal scalar
uv = Vector('uv') #universal vector
arb_n = Scalar('arb_n') 



def verify(prop, proof):
    if callable(prop):
        try: return verify_forall_scalar(prop,proof)
        except:
            try: return verify_forall_vector(prop,proof)
            except: raise TypeError(f'wrong input type: {type(prop)}')

    if isinstance(prop, Equal):
        return verify_equality(prop, proof)
    if isinstance(prop, le):
        return verify_le(prop, proof)
    if isinstance(prop, lt):
        return verify_lt(prop, proof)
    if isinstance(prop, prop_and ):
        return verify_and(prop, proof)



def verify_and(props, proofs):
    result = True
    for i in range(len(props.prop_list)):
        result = result and verify(props.prop_list[i], proofs[i])
    return result

#def verify_ifthen(prop, proof):
def verify_forall_scalar(prop,proof):
    #arb_num = Scalar('arb_num')  #represents arbitrary number and vector
    return verify(prop(arb_n), proof)

def verify_forall_vector(prop,proof):
    arb_vec = Vector('arb_vec')
    return verify(prop(arb_vec), proof)




def verify_equality(eq,proof):
    #Look up in Prop
  if eq in Prop:
      return True

  if isinstance(eq,neg):
      return not verify_equality(eq.inside, proof)

  #For now, we only consider substitute and simplify in proving steps
  #Using each steps of proof : ordered list of statements in Prop
  result = eq.lhs-eq.rhs
  if is_number(result):
      return result == 0

  for step in proof:
      if step in Prop:
        if isinstance(step, Equal):                 #substitution
          print(f'before: {result}'+ f' with step {step} ')
          result = result.substitute(step)
          print(f'substitued to : {result}')
        elif isinstance(step, lemma):               #add lemma
          propadd_eq(lemma.claim, lemma.proof)
        elif isinstance(step, tactic):
          #if step.tactic in Tactic:
          if callable(step.tactic):               #tactic
              step.tactic(step.claim)
        else: raise TypeError(f'Cannot use the following step: {step}' )
      else:
        raise TypeError( f'Should first verify the current step: {step}')

  #Check if LHS-RHS = 0
  if result == 0:
      return True
  elif result.simplify() == 0:
      return True
  else:
      return result.simplify().is_zero()



def verify_le(ineq, proof): #FIRST LET'S JUST FOCUS ON PROVING THETA

    if ineq in Prop:            #check if it is already known to be true
        return True

    lhs = ineq.lhs
    rhs = ineq.rhs

    #ineq_type = type(ineq)

    #if is_number(lhs) and is_number(rhs):

    try: return lhs <= rhs
    except:
      for step in proof:
        if step not in Prop:       #check if each proof step is verified
          raise TypeError( f'Should first verify the current step: {step}')
          return False

        if isinstance(step,Equal):
          if not is_number(lhs):
            lhs = lhs.substitute(step)
            try: lhs = lhs.simplify()
            except: pass
          if not is_number(rhs):
            rhs = rhs.substitute(step)
            try: rhs = rhs.simplify()
            except: pass


        if isinstance(step,le): #transitiivty
          if step.lhs == rhs:
            rhs = step.rhs
          if step.rhs == lhs:
            lhs = step.lhs

    try: return lhs <= rhs
    except:
        try: return 0<=(lhs-rhs).simplify()
        except: return le(lhs,rhs) in Prop or le(0,(rhs-lhs).simplify()) in Prop or le((lhs-rhs).simplify(),0) in Prop





def verify_lt(ineq, proof): #FIRST LET'S JUST FOCUS ON PROVING THETA

  if ineq in Prop:            #check if it is already known to be true
      return True

  lhs = ineq.lhs
  rhs = ineq.rhs

  #ineq_type = type(ineq)

  #if is_number(lhs) and is_number(rhs):

  try: return lhs < rhs
  except:
    for step in proof:
      if step not in Prop:       #check if each proof step is verified
        raise TypeError( f'Should first verify the current step: {step}')
        return False

      if isinstance(step,Equal):
        if not is_number(lhs):
          lhs0 = lhs
          lhs = lhs.substitute(step)
          try:
              lhs = lhs.simplify()
              #print(f'lhs: {lhs0} to {lhs}')
          except: pass

        if not is_number(rhs):
          rhs0 = rhs
          rhs = rhs.substitute(step)
          try:
              rhs = rhs.simplify()
              #print(f'rhs: {rhs0} to {rhs}')
          except: pass

      if isinstance(step,lt): #transitiivty
        if step.lhs == rhs:
          rhs = step.rhs
        if step.rhs == lhs:
          lhs = step.lhs



  try:
    #print('000')
    return lhs < rhs
  except:
        try:
            #print(f'aaa {0<(rhs-lhs).simplify()}')
            return 0<(rhs-lhs).simplify()
        except:
            #print(f'bbb {lhs}, and {rhs}')
            return lt(lhs,rhs) in Prop or lt(0,(rhs-lhs).simplify()) in Prop or lt((lhs-rhs).simplify(),0) in Prop



def induction(prop, proof_0, proof_succ): #must put proofs in list
    target = [prop]

    if isinstance(prop,prop_and): #for now we just assume that every target props are of fucntion type
        target = prop.prop_list
    #if isinstance(ifthen)

    #Case n=0
    case_0 = []
    for prop in target:
        if not callable(prop):
            raise TypeError('We only accept for all ~ in induction.')
        case_0.append(prop(0))

    case_0_istrue = verify(prop_and(case_0),proof_0)
    print(f'case 0 : {case_0_istrue} ')

    #Case succ
    case_succ = []
    for prop in target:
        Prop.add(prop(arb_n))
        case_succ.append(prop(arb_n + 1))

    case_succ_istrue = verify(prop_and(case_succ), proof_succ)
    print(f'case succ : {case_succ_istrue} ')

    if case_0_istrue and case_succ_istrue:
          Prop.add(prop)
    else:
          # print(f'Our failed target :: {prop_and(case_succ)}')
          # print(f'Our failed proof :: {proof_succ}, \n Prop:')
          # for qq in Prop:
          #     print(qq)
          raise ValueError(f'Induction failed.')



class neg():
    def __init__(self, prop):
        self.inside = prop
        self.is_equality = 0
        self.is_ineq = 0
        self.istrue = 2 if prop.istrue == 2 else 1 - prop.istrue

    def __str__(self):
        s = f'not_( {self.inside} )'
        return s

    def __repr__(self):
        s = " \\neg ( " + repr(self.inside) + ")"
        return s

    def _repr_latex_(self):
        return "$\\displaystyle %s$" % repr(self)



def propadd_assumption(prop):
  #if prop.istrue == 'assumed' :
  Prop.add(prop)


def propadd_eq(eq,proof):
  if verify_equality(eq,proof) == True:
    Prop.add(eq)
    #print(f'{eq} added to Proposition data')
  else: print('failed to verify')




def propadd_forall_scalar(forall_statement,proof): #For now this works for equalities with only one forall quantifier
  u = us
  if verify_equality(forall_statement(u),proof = []) == True:
    Prop.add (forall_statement)
    print('added to Proposition data')
  else: print('Failed to verify')

def propadd_forall_vector(forall_statement,proof): #For now this works for equalities with only one forall quantifier
  u = uv
  if verify_equality(forall_statement(u),proof = []) == True:
    Prop.add (forall_statement)
    print(f'{forall_statement} added to Proposition data')
  else: print('Failed to verify')

def propadd_intro(fun,u):
    if fun in Prop:
      Prop.add(fun(u))
      try: Prop.add(fun(u).simplify()) #Temporary
      except: pass
    else: print('Failed to verify')


def propadd_ineq(ineq,proof):
    if isinstance(ineq, le):
        if verify_le(ineq,proof) == True:
           Prop.add(ineq)

        else: raise ValueError(f'{ineq} not verified')

    elif isinstance(ineq, lt):
        if verify_lt(ineq,proof) == True:
            Prop.add(ineq)

        else: raise ValueError(f'{ineq} not verified')
    else: raise TypeError(f'Wrong input prop type: {type(ineq)}.')


def propadd_ineq_intro(fun,case) :
    if fun in Prop:
      Prop.add(fun(case))

def propadd_simplify(prop):
    if prop in Prop:
        try:
            Prop.add(prop.simplify())
            #print(f'{prop} to {prop.simplify()}')
        except:
            try:
                LHS = prop.lhs.simplify()
            except: pass
            try:
                RHS = prop.lhs.simplify()
            except: pass
            try: Prop.add(type(prop)(LHS,RHS))
            except:
                  for p in prop:
                      propadd_simplify(p)

class exists():
    def __init__(self,eq_fun):
        self.predicate = eq_fun
        self.istrue = 'unknown'

    def case(self, var):
        Var.add(var)
        Prop.add(self.predicate(var))

    def __hash__(self):
        return hash(self.predicate)

    def __eq__(self, other):
        if isinstance(other, exists):
            return self.predicate == other.predicate
        return False

def verify_existence(ex,var,proof):  #works for one variable
  if verify_equality(ex.predicate(var),proof) == True:
      #propadd_eq(ex.predicate(var),proof)
      Prop.add(ex)


class ifthen():
    def __init__(self, prop1, prop2):
        self.condition = prop1
        self.consequence = prop2
        self.istrue = 2

        if prop1.istrue == 0 or prop2.istrue == 1:
          self.istrue = 1



    def __str__(self):
        s = str(self.condition) + " => " + str(self.consequence)
        return s

    def __repr__(self):
        s = repr(self.condition) + " \\implies " + repr(self.condition)
        return s

    def _repr_latex_(self):
        return "$\\displaystyle %s$" % repr(self)


class  prop_and():
    def __init__(self, prop_list):
        self.prop_list = prop_list
        self.istrue = 1
        for prop in prop_list:
                self.istrue *= prop in Prop # or prop.istrue


    def __str__(self):
        s = ""
        for prop in self.prop_list:
            s+=f'{prop} & '
        return s[:-3]


    def __repr__(self):
        s = ""
        for prop in self.prop_list:
            s+=f'{prop} \\And '
        return s[:-3]

    def _repr_latex_(self):
        return "$\\displaystyle %s$" % repr(self)

    def proj(self,n):
        result = self.prop_list[n]
        if self in Prop:
            Prop.add(result)
        return result

class lemma():
    def __init__(self, claim, proof):
        self.claim = claim
        self.proof = proof
        self.istrue = 2

class tactic():
    def __init__(self, tactic, claim):
        self.claim = claim
        self.tactic = tactic
        #self.arguments = arguments

    def specify(self,arguments):
        if callable(self.arguments):
          return tactic(self.tactic, self.claim(arguments))
        else: raise ValueError('Check the claim type')

### Example axioms ###

def eq_to_le(eq) :  #equal implies <=
    p = (eq.args[0] <= eq.args[1])
    p.istrue = eq.istrue
    return p


def eq_refl(a):
    eq = Equal(a,a)
    eq.istrue = 1
    return eq

def eq_trans(eq1,eq2):
    if eq1.args[1] == eq2.args[0]:
        eq = Equal(eq1.args[0],eq2.args[1])
        eq.istrue = eq1.istrue * eq2.istrue
        return eq
    else:
        raise TypeError( "Can't apply transivity.")

def eq_sym(eq):
    result = Equal(eq.args[1],eq.args[0])
    result.istrue = eq.istrue
    return result


#double negation
def add_to_Prop_if_double_neg_in_Prop(prop):
    if isinstance(prop, neg) and isinstance(prop.inside, neg):
        prop.istrue = prop.inside.inside.istrue
        if prop in Prop:
            Prop.add(prop.inside.inside)



# =>
def MP(ifthen, P):
    if ifthen.condition == P:
        result = ifthen.consequence

        if (ifthen.istrue ==1 or ifthen in Prop) and (P.istrue ==1 or P in Prop):
            result.istrue = 1
            Prop.add(result)
        return result

    else: raise TypeError('Wrong Input for Modus Ponens')


# a less than b implies a less than or equal to b
def lt_to_le(lt):
    result = le(lt.lhs, lt.rhs)
    if lt.istrue == 1:
       result.istrue = 1
       Prop.add(result)
    return result

# if a<b the a \neq b.
def lt_to_neq(lt):
    result = neg(Equal(lt.lhs,lt.rhs))
    if lt.istrue ==1 or lt in Prop:
        result.istrue = 1  #even if lt.istrue == false, this can be true.
        Prop.add(result)
    return result

#if x <= y but x!=y, then x<y.
def le_and_neq_to_lt(le,neq):
    if le.lhs == neq.inside.lhs and le.rhs == neq.inside.rhs:
        result = lt(le.lhs, le.rhs)
        if le.istrue == 1 and neq.istrue == 1:
            result.istrue = 1
            Prop.add(result)
    return result



def le_of_lt(le0,lt1):
    if le0.rhs == lt1.lhs:
       return lt(le0.lhs, lt1.rhs)
    else: raise TypeError('wrong input type')


def lt_of_le(lt0,le1):
    if lt0.rhs == le1.lhs:
        return lt(lt0.lhs, le1.rhs)
    else: raise TypeError('wrong input type')


def le_of_le(le1,le2):
    if le1.rhs == le2.lhs:
       return le(le1.lhs, le2.rhs)
    else: raise TypeError('wrong input type')


def lt_of_lt(lt1,lt2):
    if lt1.rhs == lt2.lhs:
       return lt(lt1.lhs, lt2.rhs)
    else: raise TypeError('wrong input type')


def ineq_trans(ineq1, ineq2):
    if ineq1.rhs != ineq2.lhs:
        raise TypeError('Cannot apply transitivity')


    if isinstance(ineq1,le) and isinstance(ineq2,le):
        result = le_of_le(ineq1, ineq2)

    if isinstance(ineq1,le) and isinstance(ineq2,lt):
        result = le_of_lt(ineq1, ineq2)

    if isinstance(ineq1,lt) and isinstance(ineq2,le):
        result = lt_of_le(ineq1, ineq2)

    if isinstance(ineq1,lt) and isinstance(ineq2,lt):
        result = lt_of_lt(ineq1, ineq2)

    ineq1in = (ineq1.istrue == 1 or ineq1 in Prop)
    ineq2in = (ineq2.istrue == 1 or ineq2 in Prop)

    if ineq1in and ineq2in:
        result.istrue = 1
        Prop.add(result)

    try :  return result
    except: raise ValueError('wrong input type')




#nonegativity of square
def square_nonneg(scalar):
    result = le(0 , scalar * scalar)
    result.istrue = 1
    Prop.add(result)
    return result

#sum of nonneg is nonneg


#trichotomy

#python numbers
def le_of_numbers(a,b):
  if is_number(a) and is_number(b):
    if a<=b:
      result = le(a,b)
      result.istrue = 1
    else: result = lt(b,a)
    return result
  else: raise TypeError( "Please check the input types")


def lt_of_numbers(a,b):
  if is_number(a) and is_number(b):
    if a<b:
      result = lt(a,b)
      result.istrue = 1
    else: result = le(b,a)
    return result
  else: raise TypeError( "Please check the input types")






def divide_equality_by_nonzero(eq, divisor):
    if neg(Equal(divisor,0)) in Prop or neg(Equal(0,divisor)) in Prop and isinstance(eq,Equal) :  # divisor != 0 & eq : Equal
        result = Equal( eq.lhs / divisor , eq.rhs / divisor )
        if eq.istrue == 1 or eq in Prop:              #preserve the truth value
            result.istrue = 1
            Prop.add(result)
        return result

    else: raise ValueError( "You should verify that you are dividing an equality by nonzero.")


def divide_inequality(ineq, divisor):
    if isinstance(ineq,(le,lt)):
        if lt(0,divisor) in Prop:        #positive multiplication prserves order
            result = type(ineq)(ineq.lhs / divisor, ineq.rhs / divisor )
            if ineq.istrue == 1 or ineq in Prop:
                result.istrue = 1
                Prop.add(result)
            return result

        if lt(divisor, 0) in Prop:       #negative multiplication reverses order
            result = type(ineq)(ineq.rhs / divisor, ineq.lhs / divisor )
            if ineq.istrue == 1 or ineq in Prop:
                result.istrue = 1
                Prop.add(result)
            return result

    else: raise ValueError( "You should verify that you are dividing an inequality by nonzero.")


# multiplication
def mul_inequality(ineq, multiplier):
    if isinstance(ineq,(le,lt)):
        if Equal(0,multiplier) in Prop or Equal(multiplier,0) in Prop or multiplier == 0:
            return Equal(0,0)                           #multiplication by 0

        elif le(0, multiplier) in Prop or lt(0, multiplier) in Prop or 0 < multiplier:
            result = type(ineq)(ineq.lhs * multiplier, ineq.rhs * multiplier )
            if ineq.istrue == 1 or ineq in Prop:
                result.istrue = 1
                Prop.add(result)
            return result

        elif le(multiplier, 0) in Prop or lt(multiplier, 0) in Prop or multiplier < 0:
            result = type(ineq)(ineq.rhs * multiplier, ineq.lhs * multiplier )
            if ineq.istrue == 1 or ineq in Prop:
                result.istrue = 1
                Prop.add(result)
            return result

        else: return None

    else: raise TypeError( "You should verify that you are multiplying an inequality.")


def mul_equality(eq, multiplier):
    if isinstance(eq, Equal):
        result = Equal(eq.lhs * multiplier, eq.rhs * multiplier)
        if eq.istrue == 1 or eq in Prop:
            result.istrue = 1
            Prop.add(result)

        return result
    else: raise TypeError( "You should verify that you are multiplying an equality.")

#addition
def add_of(summand, adder):
    if isinstance(summand, (Equal,le,lt)):
        result = type(summand)(summand.lhs + adder, summand.rhs + adder)
        if summand.istrue == 1 or summand in Prop:
            result.istrue = 1
            Prop.add(result)

        return result
    else: raise TypeError( "You should verify that you are adding the right type.")


def sqrt_nonneg(term):
    if isinstance(term, ScalarPow):
        if term.exponent == 1/2:
            Prop.add(le(0,term))
        else: raise ValueError("The term is not 1/2th power")
    else: raise ValueError("The input should be the form sqrt")


def verify_forall_le(fun,proof):
      return verify_le(fun(us))



def sqrt_of_ineq(ineq):
    if isinstance(ineq,(le,lt)):
      if le(0,ineq.lhs) in Prop and le(0,ineq.rhs) in Prop:
          result = type(ineq)(ineq.lhs.sqrt(),ineq.rhs.sqrt())
          result.istrue = 1
          Prop.add(result)
          return result
    else: raise TypeError('wrong input type')


def neg_of_le(scalar):
  result = le(-scalar,0)
  if le(0,scalar) in Prop:
      result.istrue = 1
      Prop.add(result)

  return result

def sum_of_nonneg(a,b):
    return ifthen( prop_and([le(0,a), le(0,b)]), le(0,a+b) )