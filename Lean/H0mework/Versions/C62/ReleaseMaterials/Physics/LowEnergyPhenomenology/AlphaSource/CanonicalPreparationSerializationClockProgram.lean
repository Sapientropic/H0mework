import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationEmitterStages

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceSerialization
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth PreparationVacuumEnginePaidDepth
open PreparationVacuumDAGCoefficient PreparationVacuumClockSymbol
open scoped BigOperators

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

inductive ExprSort where | symbol | polynomial

abbrev Value : ExprSort → Type
  | .symbol => Symbol
  | .polynomial => AngularPolynomial

-- Earlier clocks are fixed sourceEngine coordinates; the level type excludes the
-- stage currently being generated. The original C/0 seed is emitted separately.
inductive Primitive (K : ℕ) where
  | base (p : PreparationVacuumDAGSemantic.Primitive)
  | clockReference (level : Fin K) (axis : Fin 4)

def primitiveValue {K : ℕ} : Primitive K → Symbol
  | .base p => PreparationVacuumDAGSemantic.primitiveValue p
  | .clockReference level axis => sourceEngine K axis (Fin.succ level)

variable {K : ℕ}

inductive Expression (K : ℕ) : ExprSort → Type where
  | primitive (p : Primitive K) : Expression K .symbol
  | addS (e f : Expression K .symbol) : Expression K .symbol
  | negS (e : Expression K .symbol) : Expression K .symbol
  | mulS (e f : Expression K .symbol) : Expression K .symbol
  | sumS {n : ℕ} (terms : Fin n → Expression K .symbol) : Expression K .symbol
  | coefficient (u : AngularExponent) (e : Expression K .polynomial) : Expression K .symbol
  | average (e : Expression K .polynomial) : Expression K .symbol
  | zeroP : Expression K .polynomial
  | monomial (u : AngularExponent) (e : Expression K .symbol) : Expression K .polynomial
  | addP (e f : Expression K .polynomial) : Expression K .polynomial
  | negP (e : Expression K .polynomial) : Expression K .polynomial
  | mulP (e f : Expression K .polynomial) : Expression K .polynomial
  | sumP {n : ℕ} (terms : Fin n → Expression K .polynomial) : Expression K .polynomial
  | weighted (r : ℕ) (e f : Expression K .polynomial) : Expression K .polynomial

def evaluate {s : ExprSort} (e : Expression K s) : Value s :=
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

inductive Term (K : ℕ) : (s : ExprSort) → Value s → Type where
  | primitive (p : Primitive K) : Term K .symbol (primitiveValue p)
  | addS {f g : Symbol} : Term K .symbol f → Term K .symbol g → Term K .symbol (f+g)
  | negS {f : Symbol} : Term K .symbol f → Term K .symbol (-f)
  | mulS {f g : Symbol} : Term K .symbol f → Term K .symbol g → Term K .symbol (f*g)
  | sumS {n : ℕ} {f : Fin n → Symbol} : (∀ i,Term K .symbol (f i)) → Term K .symbol (∑ i,f i)
  | coefficient {P : AngularPolynomial} (u : AngularExponent) : Term K .polynomial P → Term K .symbol (MvPolynomial.coeff u P)
  | average {P : AngularPolynomial} : Term K .polynomial P → Term K .symbol (PreparationVacuumEngineSource.average P)
  | zeroP : Term K .polynomial 0
  | monomial {f : Symbol} (u : AngularExponent) : Term K .symbol f → Term K .polynomial (MvPolynomial.monomial u f)
  | addP {P Q : AngularPolynomial} : Term K .polynomial P → Term K .polynomial Q → Term K .polynomial (P+Q)
  | negP {P : AngularPolynomial} : Term K .polynomial P → Term K .polynomial (-P)
  | mulP {P Q : AngularPolynomial} : Term K .polynomial P → Term K .polynomial Q → Term K .polynomial (P*Q)
  | sumP {n : ℕ} {f : Fin n → AngularPolynomial} : (∀ i,Term K .polynomial (f i)) → Term K .polynomial (∑ i,f i)
  | weighted {P Q : AngularPolynomial} (r : ℕ) : Term K .polynomial P → Term K .polynomial Q → Term K .polynomial (PreparationVacuumEngineSource.weighted r P Q)

def erase {s : ExprSort} {v : Value s} (term : Term K s v) : Expression K s :=
  Term.rec (motive:=fun s _ _ => Expression K s)
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

theorem evaluate_erase {s : ExprSort} {v : Value s} (term : Term K s v) : evaluate (erase term)=v := by
  induction term <;> simp_all [erase,evaluate]

abbrev SymbolTerm (K : ℕ) (f : Symbol) := Term K .symbol f
abbrev PolynomialTerm (K : ℕ) (P : AngularPolynomial) := Term K .polynomial P
abbrev SeriesTerm (K : ℕ) (X : List AngularPolynomial) := ∀ n : ℕ,PolynomialTerm K (X.getD n 0)
abbrev ClockTerm (K : ℕ) {k : ℕ} (clock : ClockAt k) := ∀ a j,SymbolTerm K (clock a j)

def zeroS : SymbolTerm K 0 := Term.primitive (.base (.literal 0))
def constantS (c : ℝ) : SymbolTerm K (fun _ => c) := Term.primitive (.base (.literal c))
def constantP {f : Symbol} (e : SymbolTerm K f) : PolynomialTerm K (MvPolynomial.C f) := Term.monomial 0 e

def subS {f g : Symbol} (e : SymbolTerm K f) (d : SymbolTerm K g) : SymbolTerm K (f-g) := by
  simpa only [sub_eq_add_neg] using Term.addS e (Term.negS d)
def subP {P Q : AngularPolynomial} (e : PolynomialTerm K P) (d : PolynomialTerm K Q) : PolynomialTerm K (P-Q) := by
  simpa only [sub_eq_add_neg] using Term.addP e (Term.negP d)

def rangeP (n : ℕ) (f : ℕ → AngularPolynomial) (terms : ∀ i,PolynomialTerm K (f i)) :
    PolynomialTerm K (∑ i∈Finset.range n,f i) := by
  rw [←Fin.sum_univ_eq_sum_range]
  exact Term.sumP (fun i => terms i.val)

def seriesNil : SeriesTerm K [] := fun _ => Term.zeroP

def seriesAppendOne {X : List AngularPolynomial} {P : AngularPolynomial}
    (x : SeriesTerm K X) (p : PolynomialTerm K P) : SeriesTerm K (X++[P]) := by
  intro n
  by_cases low : n<X.length
  · rw [List.getD_append _ _ _ _ low]; exact x n
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases same : n=X.length
    · subst n; simpa only [Nat.sub_self,List.getD_cons_zero] using p
    · rw [List.getD_eq_default _ _ (by simp only [List.length_cons,List.length_nil]; omega)]
      exact Term.zeroP

def clockAtTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm K clock) (a : Fin 4) (j : ℕ) :
    SymbolTerm K ((smooth_program_const% "clockAt") clock a j) := by
  change SymbolTerm K (if h : j<k+1 then clock a ⟨j,h⟩ else 0)
  split_ifs
  · exact clockTerms _ _
  · exact zeroS

def clockPolynomialTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm K clock) (a : Fin 4) (j : ℕ) :
    PolynomialTerm K ((smooth_program_const% "clockPolynomial") clock a j) := constantP (clockAtTerm clockTerms a j)

def ellTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm K clock) (j : ℕ) :
    PolynomialTerm K ((smooth_program_const% "ellPolynomial") clock j) :=
  Term.addP (clockPolynomialTerm clockTerms 0 j) (Term.sumP (fun a : Fin 3 =>
    Term.mulP (by
      change PolynomialTerm K (MvPolynomial.monomial (Finsupp.single a 1) (1 : Symbol))
      have one : (fun _ : Phase => (1 : ℝ))=(1 : Symbol) := by funext x; rfl
      rw [←one]
      exact Term.monomial (Finsupp.single a 1) (constantS 1))
      (clockPolynomialTerm clockTerms (Fin.succ a) j)))

def sourceTerm (n : ℕ) (slot : Fin 13) : SymbolTerm K (engineSource n slot) := by
  cases n with
  | zero => exact Term.primitive (.base (.principal slot))
  | succ n =>
    cases n with
    | zero => exact Term.primitive (.base (.leaf 1 (Fin.castSucc slot)))
    | succ n =>
      cases n with
      | zero =>
        apply Term.addS (Term.primitive (.base (.leaf 0 (Fin.castSucc slot))))
        by_cases h : slot=0
        · simp only [h,ite_true]; exact Term.primitive (.base (.leaf 0 (Fin.last 13)))
        · simp only [h,ite_false]; exact zeroS
      | succ n => exact zeroS

def traceTerm (n : ℕ) : SymbolTerm K (engineTrace n) :=
  Term.addS (Term.addS (sourceTerm n 4) (sourceTerm n 5)) (sourceTerm n 6)

def sourceSeriesTerm (slot : Fin 13) : SeriesTerm K ((smooth_program_const% "sourceSeries") slot) := by
  intro n
  cases n with
  | zero => exact constantP (sourceTerm 0 slot)
  | succ n =>
    cases n with
    | zero => exact constantP (sourceTerm 1 slot)
    | succ n =>
      cases n with
      | zero => exact constantP (sourceTerm 2 slot)
      | succ n => exact Term.zeroP

def traceSeriesTerm : SeriesTerm K (smooth_program_const% "traceSeries") := by
  intro n
  cases n with
  | zero => exact constantP (traceTerm 0)
  | succ n =>
    cases n with
    | zero => exact constantP (traceTerm 1)
    | succ n =>
      cases n with
      | zero => exact constantP (traceTerm 2)
      | succ n => exact Term.zeroP

def jordanSeriesTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    {X : List AngularPolynomial} (input : SeriesTerm K X) (a : Fin 4) :
    SeriesTerm K ((smooth_program_const% "js") depth clock a X) := by
  intro n
  by_cases hn : n<depth+1
  · change PolynomialTerm K ((List.ofFn (fun m : Fin (depth+1) =>
      ∑ i∈Finset.range (m.val+1),∑ j∈Finset.range (m.val+1-i),weighted (m.val-i-j)
        ((smooth_program_const% "clockPolynomial") clock a i) (X.getD j 0))).getD n 0)
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hn,dif_pos,Option.getD_some]
    exact rangeP _ _ (fun i => rangeP _ _ (fun j =>
      Term.weighted _ (clockPolynomialTerm clockTerms a i) (input j)))
  · rw [List.getD_eq_default _ _ (by change (List.ofFn _).length≤n; simp only [List.length_ofFn]; omega)]
    exact Term.zeroP

def resolventNextTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    {X answers : List AngularPolynomial} (input : SeriesTerm K X) (earlier : SeriesTerm K answers) (n : ℕ) :
    PolynomialTerm K ((smooth_program_const% "resolventNext") clock X answers n) := by
  apply Term.mulP (constantP (Term.primitive (.base .inverseClock)))
  apply subP (input n)
  apply rangeP
  intro i
  apply rangeP
  intro j
  split_ifs
  · exact Term.zeroP
  · exact Term.weighted _ (ellTerm clockTerms i) (earlier j)

def resolventTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    {X : List AngularPolynomial} (input : SeriesTerm K X) :
    SeriesTerm K ((smooth_program_const% "resolvent") depth clock X) := by
  have fold (indices : List ℕ) (initial : List AngularPolynomial) (initialTerms : SeriesTerm K initial) :
      SeriesTerm K (indices.foldl (fun answers n => answers++[(smooth_program_const% "resolventNext") clock X answers n]) initial) := by
    induction indices generalizing initial with
    | nil => exact initialTerms
    | cons n indices ih =>
      exact ih _ (seriesAppendOne initialTerms (resolventNextTerm clockTerms input initialTerms n))
  exact fold (List.range (depth+1)) [] seriesNil

def actTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    (token : Token) {X : List AngularPolynomial} (input : SeriesTerm K X) :
    SeriesTerm K ((smooth_program_const% "act") depth clock token X) := by
  cases token with
  | inverse => exact resolventTerm depth clockTerms input
  | jordan a => exact jordanSeriesTerm depth clockTerms input a

def wordTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    (tokens : List Token) {X : List AngularPolynomial} (input : SeriesTerm K X) :
    SeriesTerm K ((smooth_program_const% "word") depth clock tokens X) := by
  induction tokens with
  | nil => exact input
  | cons token tokens ih => exact actTerm depth clockTerms token ih

def tableTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    (a b : Fin 4) (equation : Option (Fin 4)) {X : List AngularPolynomial}
    (input : SeriesTerm K X) (n : Fin (depth+1)) :
    SymbolTerm K ((smooth_program_const% "applyT") depth clock a b equation X n) := by
  have fold (terms : List TableTerm) (initial : AngularPolynomial) (initialTerm : PolynomialTerm K initial) :
      PolynomialTerm K (terms.foldl (fun out term => out+
        (smooth_program_const% "scale") (fun _ => term.coefficient)
          (MvPolynomial.monomial term.exponent 1*
            ((smooth_program_const% "word") depth clock term.tokens X).getD n.val 0)) initial) := by
    induction terms generalizing initial with
    | nil => exact initialTerm
    | cons term terms ih =>
      exact ih _ (Term.addP initialTerm (Term.mulP (constantP (constantS term.coefficient))
        (Term.mulP (Term.monomial term.exponent (constantS 1))
          (wordTerm depth clockTerms term.tokens input n.val))))
  exact Term.average (fold ((smooth_program_const% "table") a b equation) 0 Term.zeroP)

def affineTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    SymbolTerm K ((smooth_program_const% "affine") depth clock equation n) := by
  cases equation with
  | none => exact Term.sumS (fun a : Fin 4 => Term.coefficient 0
      (jordanSeriesTerm depth clockTerms (sourceSeriesTerm (Fin.castAdd 9 a)) a n.val))
  | some a => exact Term.negS (Term.coefficient 0 (sourceSeriesTerm (Fin.castAdd 9 a) n.val))

def forceOrEnergyTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) : SymbolTerm K (forceOrEnergy depth clock equation n) := by
  unfold forceOrEnergy
  refine subS (subS (subS (Term.addS (affineTerm depth clockTerms equation n) ?_) ?_) ?_) ?_
  · exact Term.mulS (constantS (1/2)) (tableTerm depth clockTerms 0 0 equation traceSeriesTerm n)
  · exact Term.sumS (fun i : Fin 3 => Term.mulS (constantS (1/2))
      (tableTerm depth clockTerms (Fin.succ i) (Fin.succ i) equation (sourceSeriesTerm ⟨4+i.val,by omega⟩) n))
  · exact Term.sumS (fun i : Fin 3 => tableTerm depth clockTerms
      (Fin.succ ((smooth_program_const% "crossFirst") i)) (Fin.succ ((smooth_program_const% "crossSecond") i))
      equation (sourceSeriesTerm ((smooth_program_const% "crossSlot") i)) n)
  · exact Term.sumS (fun i : Fin 3 => tableTerm depth clockTerms 0 (Fin.succ i)
      equation (sourceSeriesTerm ⟨10+i.val,by omega⟩) n)

theorem originalProgram_readback {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm K clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    evaluate (erase (forceOrEnergyTerm depth clockTerms equation n))=forceOrEnergy depth clock equation n :=
  evaluate_erase _


-- The reference constructor is indexed by the source's actual earlier stage.
theorem source_seed (k : ℕ) (a : Fin 4) : sourceEngine k a 0=if a=0 then sourceClock else 0 := by
  induction k with
  | zero=>exact sourceEngine_initial a
  | succ k ih=>
    change sourceEngine (k+1) a (Fin.castSucc 0)=_
    rw [sourceEngine_preserves,ih]

def referenceClockTerms (k : ℕ) : ClockTerm k (sourceEngine k) := by
  intro a level
  induction level using Fin.cases with
  | zero=>
    rw [source_seed]
    split_ifs
    · exact Term.primitive (.base .clock)
    · exact zeroS
  | succ j=>exact Term.primitive (.clockReference j a)


theorem referenceClockTerms_positive (k : ℕ) (a : Fin 4) (j : Fin k) :
    erase (referenceClockTerms k a (Fin.succ j))=Expression.primitive (.clockReference j a) := by
  simp only [referenceClockTerms,Fin.cases_succ,erase]

def referenceResidual (k : ℕ) (a : Fin 4) : Expression k .symbol :=
  erase (forceOrEnergyTerm (k+1) (referenceClockTerms k) (some a) (Fin.last (k+1)))

def referenceClockDefinition (k : ℕ) (a : Fin 4) : Expression k .symbol :=
  .negS (.sumS (fun b : Fin 4 => .mulS (.primitive (.base (.inverseJacobian a b)))
    (referenceResidual k b)))

def referenceEnergy (k : ℕ) : Expression k .symbol :=
  erase (forceOrEnergyTerm (k+1) (referenceClockTerms k) none (Fin.last (k+1)))

theorem referenceResidual_native (k : ℕ) (a : Fin 4) :
    evaluate (referenceResidual k a)=forceOrEnergy (k+1) (sourceEngine k) (some a) (Fin.last (k+1)) :=
  evaluate_erase _

theorem referenceClockDefinition_native (k : ℕ) (a : Fin 4) :
    evaluate (referenceClockDefinition k a)=sourceEngine (k+1) a (Fin.last (k+1)) := by
  funext x
  change -(∑ b : Fin 4,(principalForceJacobian x)⁻¹ a b*evaluate (referenceResidual k b) x)=_
  simp only [referenceResidual_native]
  exact (sourceEngine_generated k a x).symm

theorem referenceEnergy_native (k : ℕ) : evaluate (referenceEnergy k)=sourceEngineEnergy (k+1) := by
  rw [sourceEngineEnergy_newestExcluded k]
  exact evaluate_erase _

end LowEnergy.PreparationVacuumSourceSerialization
