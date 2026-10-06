import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGInverseEntries

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDAGSemantic
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open PreparationVacuumDAGCoefficient PreparationVacuumClockSymbol
open scoped BigOperators

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

inductive ExprSort where | symbol | polynomial

abbrev Value : ExprSort → Type
  | .symbol => Symbol
  | .polynomial => AngularPolynomial

-- The only function-valued leaves are the original source functions. In particular
-- there is no arbitrary-symbol, completed-clock, or completed-energy constructor.
inductive Primitive where
  | literal (c : ℝ)
  | principal (slot : Fin 13)
  | leaf (degree : Fin 3) (slot : Fin 14)
  | clock
  | inverseClock
  | inverseJacobian (a b : Fin 4)

def primitiveValue : Primitive → Symbol
  | .literal c => fun _ => c
  | .principal j => engineSource 0 j
  | .leaf d j => originalLeaf d j
  | .clock => sourceClock
  | .inverseClock => fun x => (sourceClock x)⁻¹
  | .inverseJacobian a b => fun x => (principalForceJacobian x)⁻¹ a b

inductive Expression : ExprSort → Type where
  | primitive (p : Primitive) : Expression .symbol
  | addS (e f : Expression .symbol) : Expression .symbol
  | negS (e : Expression .symbol) : Expression .symbol
  | mulS (e f : Expression .symbol) : Expression .symbol
  | sumS {n : ℕ} (terms : Fin n → Expression .symbol) : Expression .symbol
  | coefficient (u : AngularExponent) (e : Expression .polynomial) : Expression .symbol
  | average (e : Expression .polynomial) : Expression .symbol
  | zeroP : Expression .polynomial
  | monomial (u : AngularExponent) (e : Expression .symbol) : Expression .polynomial
  | addP (e f : Expression .polynomial) : Expression .polynomial
  | negP (e : Expression .polynomial) : Expression .polynomial
  | mulP (e f : Expression .polynomial) : Expression .polynomial
  | sumP {n : ℕ} (terms : Fin n → Expression .polynomial) : Expression .polynomial
  | weighted (r : ℕ) (e f : Expression .polynomial) : Expression .polynomial

def evaluate {s : ExprSort} (e : Expression s) : Value s :=
  Expression.rec (motive:=fun s _ => Value s)
    primitiveValue
    (fun _ _ a b => a+b)
    (fun _ a => -a)
    (fun _ _ a b => a*b)
    (fun _ values => ∑ i,values i)
    (fun u _ p => MvPolynomial.coeff u p)
    (fun _ p => PreparationVacuumEngineSource.average p)
    0
    (fun u _ f => MvPolynomial.monomial u f)
    (fun _ _ p q => p+q)
    (fun _ p => -p)
    (fun _ _ p q => p*q)
    (fun _ values => ∑ i,values i)
    (fun r _ _ p q => PreparationVacuumEngineSource.weighted r p q) e

inductive Term : (s : ExprSort) → Value s → Type where
  | primitive (p : Primitive) : Term .symbol (primitiveValue p)
  | addS {f g : Symbol} : Term .symbol f → Term .symbol g → Term .symbol (f+g)
  | negS {f : Symbol} : Term .symbol f → Term .symbol (-f)
  | mulS {f g : Symbol} : Term .symbol f → Term .symbol g → Term .symbol (f*g)
  | sumS {n : ℕ} {f : Fin n → Symbol} : (∀ i,Term .symbol (f i)) → Term .symbol (∑ i,f i)
  | coefficient {P : AngularPolynomial} (u : AngularExponent) : Term .polynomial P → Term .symbol (MvPolynomial.coeff u P)
  | average {P : AngularPolynomial} : Term .polynomial P → Term .symbol (PreparationVacuumEngineSource.average P)
  | zeroP : Term .polynomial 0
  | monomial {f : Symbol} (u : AngularExponent) : Term .symbol f → Term .polynomial (MvPolynomial.monomial u f)
  | addP {P Q : AngularPolynomial} : Term .polynomial P → Term .polynomial Q → Term .polynomial (P+Q)
  | negP {P : AngularPolynomial} : Term .polynomial P → Term .polynomial (-P)
  | mulP {P Q : AngularPolynomial} : Term .polynomial P → Term .polynomial Q → Term .polynomial (P*Q)
  | sumP {n : ℕ} {f : Fin n → AngularPolynomial} : (∀ i,Term .polynomial (f i)) → Term .polynomial (∑ i,f i)
  | weighted {P Q : AngularPolynomial} (r : ℕ) : Term .polynomial P → Term .polynomial Q → Term .polynomial (PreparationVacuumEngineSource.weighted r P Q)

def erase {s : ExprSort} {v : Value s} (term : Term s v) : Expression s :=
  Term.rec (motive:=fun s _ _ => Expression s)
    Expression.primitive
    (fun _ _ a b => .addS a b)
    (fun _ a => .negS a)
    (fun _ _ a b => .mulS a b)
    (fun _ terms => .sumS terms)
    (fun u _ e => .coefficient u e)
    (fun _ e => .average e)
    Expression.zeroP
    (fun u _ e => .monomial u e)
    (fun _ _ e f => .addP e f)
    (fun _ e => .negP e)
    (fun _ _ e f => .mulP e f)
    (fun _ terms => .sumP terms)
    (fun r _ _ e f => .weighted r e f) term

theorem evaluate_erase {s : ExprSort} {v : Value s} (term : Term s v) : evaluate (erase term)=v := by
  induction term <;> simp_all [erase,evaluate]

abbrev SymbolTerm (f : Symbol) := Term .symbol f
abbrev PolynomialTerm (P : AngularPolynomial) := Term .polynomial P
abbrev SeriesTerm (X : List AngularPolynomial) := ∀ n : ℕ,PolynomialTerm (X.getD n 0)
abbrev ClockTerm {k : ℕ} (clock : ClockAt k) := ∀ a j,SymbolTerm (clock a j)

def zeroS : SymbolTerm 0 := Term.primitive (.literal 0)
def constantS (c : ℝ) : SymbolTerm (fun _ => c) := Term.primitive (.literal c)
def constantP {f : Symbol} (e : SymbolTerm f) : PolynomialTerm (MvPolynomial.C f) := Term.monomial 0 e

def subS {f g : Symbol} (e : SymbolTerm f) (d : SymbolTerm g) : SymbolTerm (f-g) := by
  simpa only [sub_eq_add_neg] using Term.addS e (Term.negS d)
def subP {P Q : AngularPolynomial} (e : PolynomialTerm P) (d : PolynomialTerm Q) : PolynomialTerm (P-Q) := by
  simpa only [sub_eq_add_neg] using Term.addP e (Term.negP d)

def rangeP (n : ℕ) (f : ℕ → AngularPolynomial) (terms : ∀ i,PolynomialTerm (f i)) :
    PolynomialTerm (∑ i∈Finset.range n,f i) := by
  rw [←Fin.sum_univ_eq_sum_range]
  exact Term.sumP (fun i => terms i.val)

def seriesNil : SeriesTerm [] := fun _ => Term.zeroP

def seriesAppendOne {X : List AngularPolynomial} {P : AngularPolynomial}
    (x : SeriesTerm X) (p : PolynomialTerm P) : SeriesTerm (X++[P]) := by
  intro n
  by_cases low : n<X.length
  · rw [List.getD_append _ _ _ _ low]; exact x n
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases same : n=X.length
    · subst n; simpa only [Nat.sub_self,List.getD_cons_zero] using p
    · rw [List.getD_eq_default _ _ (by simp only [List.length_cons,List.length_nil]; omega)]
      exact Term.zeroP

-- Central coefficients retain their source-function identity on their actual pole domain.
theorem primitive_principal_normalized (j : Fin 13) (x : Phase) :
    primitiveValue (.principal j) x=coefficientValue (principalCoefficient j) x :=
  (principalCoefficient_native j x).symm

theorem primitive_inverse_normalized (a b : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    primitiveValue (.inverseJacobian a b) x=coefficientValue (inverseCoefficient a b) x :=
  (inverseCoefficient_native a b x hx).symm

theorem primitive_inverseClock_normalized (x : Phase) :
    primitiveValue .inverseClock x=coefficientValue (inversePoleCoefficient 0) x :=
  (inverseClockCoefficient_native x).symm

end LowEnergy.PreparationVacuumDAGSemantic
