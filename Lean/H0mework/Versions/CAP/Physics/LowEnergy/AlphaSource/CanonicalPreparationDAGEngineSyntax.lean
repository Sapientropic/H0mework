import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGSyntax

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDAGSemantic
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth
open scoped BigOperators

def clockAtTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm clock) (a : Fin 4) (j : ℕ) :
    SymbolTerm ((smooth_program_const% "clockAt") clock a j) := by
  change SymbolTerm (if h : j<k+1 then clock a ⟨j,h⟩ else 0)
  split_ifs
  · exact clockTerms _ _
  · exact zeroS

def clockPolynomialTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm clock) (a : Fin 4) (j : ℕ) :
    PolynomialTerm ((smooth_program_const% "clockPolynomial") clock a j) := constantP (clockAtTerm clockTerms a j)

def ellTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm clock) (j : ℕ) :
    PolynomialTerm ((smooth_program_const% "ellPolynomial") clock j) :=
  Term.addP (clockPolynomialTerm clockTerms 0 j) (Term.sumP (fun a : Fin 3 =>
    Term.mulP (by
      change PolynomialTerm (MvPolynomial.monomial (Finsupp.single a 1) (1 : Symbol))
      have one : (fun _ : Phase => (1 : ℝ))=(1 : Symbol) := by funext x; rfl
      rw [←one]
      exact Term.monomial (Finsupp.single a 1) (constantS 1))
      (clockPolynomialTerm clockTerms (Fin.succ a) j)))

def sourceTerm (n : ℕ) (slot : Fin 13) : SymbolTerm (engineSource n slot) := by
  cases n with
  | zero => exact Term.primitive (.principal slot)
  | succ n =>
    cases n with
    | zero => exact Term.primitive (.leaf 1 (Fin.castSucc slot))
    | succ n =>
      cases n with
      | zero =>
        apply Term.addS (Term.primitive (.leaf 0 (Fin.castSucc slot)))
        by_cases h : slot=0
        · simp only [h,ite_true]; exact Term.primitive (.leaf 0 (Fin.last 13))
        · simp only [h,ite_false]; exact zeroS
      | succ n => exact zeroS

def traceTerm (n : ℕ) : SymbolTerm (engineTrace n) :=
  Term.addS (Term.addS (sourceTerm n 4) (sourceTerm n 5)) (sourceTerm n 6)

def sourceSeriesTerm (slot : Fin 13) : SeriesTerm ((smooth_program_const% "sourceSeries") slot) := by
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

def traceSeriesTerm : SeriesTerm (smooth_program_const% "traceSeries") := by
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

def jordanSeriesTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    {X : List AngularPolynomial} (input : SeriesTerm X) (a : Fin 4) :
    SeriesTerm ((smooth_program_const% "js") depth clock a X) := by
  intro n
  by_cases hn : n<depth+1
  · change PolynomialTerm ((List.ofFn (fun m : Fin (depth+1) =>
      ∑ i∈Finset.range (m.val+1),∑ j∈Finset.range (m.val+1-i),weighted (m.val-i-j)
        ((smooth_program_const% "clockPolynomial") clock a i) (X.getD j 0))).getD n 0)
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hn,dif_pos,Option.getD_some]
    exact rangeP _ _ (fun i => rangeP _ _ (fun j =>
      Term.weighted _ (clockPolynomialTerm clockTerms a i) (input j)))
  · rw [List.getD_eq_default _ _ (by change (List.ofFn _).length≤n; simp only [List.length_ofFn]; omega)]
    exact Term.zeroP

def resolventNextTerm {k : ℕ} {clock : ClockAt k} (clockTerms : ClockTerm clock)
    {X answers : List AngularPolynomial} (input : SeriesTerm X) (earlier : SeriesTerm answers) (n : ℕ) :
    PolynomialTerm ((smooth_program_const% "resolventNext") clock X answers n) := by
  apply Term.mulP (constantP (Term.primitive .inverseClock))
  apply subP (input n)
  apply rangeP
  intro i
  apply rangeP
  intro j
  split_ifs
  · exact Term.zeroP
  · exact Term.weighted _ (ellTerm clockTerms i) (earlier j)

def resolventTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    {X : List AngularPolynomial} (input : SeriesTerm X) :
    SeriesTerm ((smooth_program_const% "resolvent") depth clock X) := by
  have fold (indices : List ℕ) (initial : List AngularPolynomial) (initialTerms : SeriesTerm initial) :
      SeriesTerm (indices.foldl (fun answers n => answers++[(smooth_program_const% "resolventNext") clock X answers n]) initial) := by
    induction indices generalizing initial with
    | nil => exact initialTerms
    | cons n indices ih =>
      exact ih _ (seriesAppendOne initialTerms (resolventNextTerm clockTerms input initialTerms n))
  exact fold (List.range (depth+1)) [] seriesNil

def actTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    (token : Token) {X : List AngularPolynomial} (input : SeriesTerm X) :
    SeriesTerm ((smooth_program_const% "act") depth clock token X) := by
  cases token with
  | inverse => exact resolventTerm depth clockTerms input
  | jordan a => exact jordanSeriesTerm depth clockTerms input a

def wordTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    (tokens : List Token) {X : List AngularPolynomial} (input : SeriesTerm X) :
    SeriesTerm ((smooth_program_const% "word") depth clock tokens X) := by
  induction tokens with
  | nil => exact input
  | cons token tokens ih => exact actTerm depth clockTerms token ih

def tableTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    (a b : Fin 4) (equation : Option (Fin 4)) {X : List AngularPolynomial}
    (input : SeriesTerm X) (n : Fin (depth+1)) :
    SymbolTerm ((smooth_program_const% "applyT") depth clock a b equation X n) := by
  have fold (terms : List TableTerm) (initial : AngularPolynomial) (initialTerm : PolynomialTerm initial) :
      PolynomialTerm (terms.foldl (fun out term => out+
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

def affineTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    SymbolTerm ((smooth_program_const% "affine") depth clock equation n) := by
  cases equation with
  | none => exact Term.sumS (fun a : Fin 4 => Term.coefficient 0
      (jordanSeriesTerm depth clockTerms (sourceSeriesTerm (Fin.castAdd 9 a)) a n.val))
  | some a => exact Term.negS (Term.coefficient 0 (sourceSeriesTerm (Fin.castAdd 9 a) n.val))

def forceOrEnergyTerm {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) : SymbolTerm (forceOrEnergy depth clock equation n) := by
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

theorem originalProgram_readback {k : ℕ} (depth : ℕ) {clock : ClockAt k} (clockTerms : ClockTerm clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    evaluate (erase (forceOrEnergyTerm depth clockTerms equation n))=forceOrEnergy depth clock equation n :=
  evaluate_erase _

end LowEnergy.PreparationVacuumDAGSemantic
