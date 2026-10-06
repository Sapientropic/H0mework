import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineSmoothSymbols

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineSmooth
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationVacuumEngineIdentities
open scoped BigOperators ContDiff

open Lean Elab Term in
elab "smooth_program_const%" name:str : term => do
  unless #["sourceSeries","traceSeries","clockAt","clockPolynomial","ellPolynomial",
      "js","resolventNext","resolvent","act","word","scale","applyT","affine",
      "table","crossFirst","crossSecond","crossSlot","nextClock","generatedCorrection",
      "generatedResidual"].contains name.getString do
    throwError "Not an original Engine program declaration"
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  Lean.Meta.mkConstWithFreshMVarLevels (Name.str ns name.getString)

def SmoothClock {k : ℕ} (clock : ClockAt k) : Prop := ∀ a j, SmoothSymbol (clock a j)
def SmoothSeries (X : List AngularPolynomial) : Prop := ∀ P∈X, SmoothPolynomial P

theorem smoothSeries_nil : SmoothSeries [] := by intro P h; simp at h

theorem smoothSeries_cons {P : AngularPolynomial} {X : List AngularPolynomial}
    (hp : SmoothPolynomial P) (hx : SmoothSeries X) : SmoothSeries (P::X) := by
  intro Q h
  rcases List.mem_cons.mp h with same|tail
  · simpa only [same] using hp
  · exact hx Q tail

theorem smoothSeries_getD {X : List AngularPolynomial} (hx : SmoothSeries X) (n : ℕ) :
    SmoothPolynomial (X.getD n 0) := by
  induction X generalizing n with
  | nil => simpa using smoothPolynomial_zero
  | cons P X ih =>
    cases n with
    | zero => simpa using hx P (List.mem_cons_self)
    | succ n =>
      simpa using ih (fun Q h => hx Q (List.mem_cons_of_mem P h)) n

theorem smoothSeries_append {X Y : List AngularPolynomial} (hx : SmoothSeries X) (hy : SmoothSeries Y) :
    SmoothSeries (X++Y) := by
  intro P h
  rcases List.mem_append.mp h with h|h
  · exact hx P h
  · exact hy P h

theorem clockAt_smooth {k : ℕ} {clock : ClockAt k} (hc : SmoothClock clock) (a : Fin 4) (j : ℕ) :
    SmoothSymbol ((smooth_program_const% "clockAt") clock a j) := by
  change SmoothSymbol (if h : j<k+1 then clock a ⟨j,h⟩ else 0)
  split_ifs
  · exact hc _ _
  · exact smoothSymbol_zero

theorem clockPolynomial_smooth {k : ℕ} {clock : ClockAt k}
    (hc : SmoothClock clock) (a : Fin 4) (j : ℕ) :
    SmoothPolynomial ((smooth_program_const% "clockPolynomial") clock a j) :=
  smoothPolynomial_constant (clockAt_smooth hc a j)

theorem ellPolynomial_smooth {k : ℕ} {clock : ClockAt k} (hc : SmoothClock clock) (j : ℕ) :
    SmoothPolynomial ((smooth_program_const% "ellPolynomial") clock j) := by
  change SmoothPolynomial ((smooth_program_const% "clockPolynomial") clock 0 j+
    ∑ a : Fin 3,MvPolynomial.X a*(smooth_program_const% "clockPolynomial") clock (Fin.succ a) j)
  apply smoothPolynomial_add (clockPolynomial_smooth hc 0 j)
  apply smoothPolynomial_sum
  intro a _
  exact smoothPolynomial_mul (smoothPolynomial_X a) (clockPolynomial_smooth hc _ j)

theorem sourceSeries_smooth (slot : Fin 13) : SmoothSeries ((smooth_program_const% "sourceSeries") slot) := by
  change SmoothSeries [MvPolynomial.C (engineSource 0 slot),MvPolynomial.C (engineSource 1 slot),
    MvPolynomial.C (engineSource 2 slot)]
  exact smoothSeries_cons (smoothPolynomial_constant (engineSource_smooth 0 slot))
    (smoothSeries_cons (smoothPolynomial_constant (engineSource_smooth 1 slot))
      (smoothSeries_cons (smoothPolynomial_constant (engineSource_smooth 2 slot)) smoothSeries_nil))

theorem traceSeries_smooth : SmoothSeries (smooth_program_const% "traceSeries") := by
  change SmoothSeries [MvPolynomial.C (engineTrace 0),MvPolynomial.C (engineTrace 1),MvPolynomial.C (engineTrace 2)]
  exact smoothSeries_cons (smoothPolynomial_constant (engineTrace_smooth 0))
    (smoothSeries_cons (smoothPolynomial_constant (engineTrace_smooth 1))
      (smoothSeries_cons (smoothPolynomial_constant (engineTrace_smooth 2)) smoothSeries_nil))

theorem sourceJ_program_smooth {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : SmoothClock clock)
    (a : Fin 4) {X : List AngularPolynomial} (hx : SmoothSeries X) :
    SmoothSeries ((smooth_program_const% "js") depth clock a X) := by
  intro P h
  change P∈List.ofFn (fun n : Fin (depth+1) =>
    ∑ i∈Finset.range (n.val+1),∑ j∈Finset.range (n.val+1-i),
      weighted (n.val-i-j) ((smooth_program_const% "clockPolynomial") clock a i) (X.getD j 0)) at h
  obtain ⟨n,rfl⟩ := List.mem_ofFn.mp h
  apply smoothPolynomial_sum
  intro i _
  apply smoothPolynomial_sum
  intro j _
  exact smoothPolynomial_weighted _ (clockPolynomial_smooth hc a i) (smoothSeries_getD hx j)

theorem sourceR_next_smooth {k : ℕ} {clock : ClockAt k} (hc : SmoothClock clock)
    {X answers : List AngularPolynomial} (hx : SmoothSeries X) (ha : SmoothSeries answers) (n : ℕ) :
    SmoothPolynomial ((smooth_program_const% "resolventNext") clock X answers n) := by
  change SmoothPolynomial (MvPolynomial.C (fun x => (sourceClock x)⁻¹)*
    (X.getD n 0-∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1-i),
      if i=0 ∧ n-i-j=0 then 0 else weighted (n-i-j)
        ((smooth_program_const% "ellPolynomial") clock i) (answers.getD j 0)))
  apply smoothPolynomial_mul (smoothPolynomial_constant sourceClock_inverse_smooth)
  apply smoothPolynomial_sub (smoothSeries_getD hx n)
  apply smoothPolynomial_sum
  intro i _
  apply smoothPolynomial_sum
  intro j _
  split_ifs
  · exact smoothPolynomial_zero
  · exact smoothPolynomial_weighted _ (ellPolynomial_smooth hc i) (smoothSeries_getD ha j)

theorem sourceR_program_smooth {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : SmoothClock clock)
    {X : List AngularPolynomial} (hx : SmoothSeries X) :
    SmoothSeries ((smooth_program_const% "resolvent") depth clock X) := by
  have fold (indices : List ℕ) (initial : List AngularPolynomial) (hi : SmoothSeries initial) :
      SmoothSeries (indices.foldl (fun answers n => answers++[
        (smooth_program_const% "resolventNext") clock X answers n]) initial) := by
    induction indices generalizing initial with
    | nil => exact hi
    | cons n indices ih =>
      rw [List.foldl_cons]
      apply ih
      exact smoothSeries_append hi (smoothSeries_cons (sourceR_next_smooth hc hx hi n) smoothSeries_nil)
  exact fold (List.range (depth+1)) [] smoothSeries_nil

theorem sourceAct_program_smooth {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : SmoothClock clock)
    (token : Token) {X : List AngularPolynomial} (hx : SmoothSeries X) :
    SmoothSeries ((smooth_program_const% "act") depth clock token X) := by
  cases token with
  | inverse => exact sourceR_program_smooth depth hc hx
  | jordan a => exact sourceJ_program_smooth depth hc a hx

theorem sourceWord_program_smooth {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : SmoothClock clock)
    (tokens : List Token) {X : List AngularPolynomial} (hx : SmoothSeries X) :
    SmoothSeries ((smooth_program_const% "word") depth clock tokens X) := by
  induction tokens with
  | nil => exact hx
  | cons token tokens ih => exact sourceAct_program_smooth depth hc token ih

theorem sourceTable_program_smooth {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : SmoothClock clock)
    (a b : Fin 4) (equation : Option (Fin 4)) {X : List AngularPolynomial} (hx : SmoothSeries X)
    (n : Fin (depth+1)) :
    SmoothSymbol ((smooth_program_const% "applyT") depth clock a b equation X n) := by
  have fold (terms : List TableTerm) (initial : AngularPolynomial) (hi : SmoothPolynomial initial) :
      SmoothPolynomial (terms.foldl (fun out term => out+
        MvPolynomial.C (fun _ => term.coefficient)*
          (MvPolynomial.monomial term.exponent 1*
            ((smooth_program_const% "word") depth clock term.tokens X).getD n.val 0)) initial) := by
    induction terms generalizing initial with
    | nil => exact hi
    | cons term terms ih =>
      rw [List.foldl_cons]
      apply ih
      exact smoothPolynomial_add hi (smoothPolynomial_mul
        (smoothPolynomial_constant (smoothSymbol_const term.coefficient))
        (smoothPolynomial_mul (smoothPolynomial_monomial _ (smoothSymbol_const 1))
          (smoothSeries_getD (sourceWord_program_smooth depth hc term.tokens hx) n.val)))
  exact smoothPolynomial_average (fold ((smooth_program_const% "table") a b equation) 0 smoothPolynomial_zero)

theorem sourceAffine_program_smooth {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : SmoothClock clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    SmoothSymbol ((smooth_program_const% "affine") depth clock equation n) := by
  cases equation with
  | none =>
    apply smoothSymbol_sum
    intro a _
    exact smoothSeries_getD (sourceJ_program_smooth depth hc a (sourceSeries_smooth (Fin.castAdd 9 a))) n.val 0
  | some a => exact smoothSymbol_neg (smoothSeries_getD (sourceSeries_smooth (Fin.castAdd 9 a)) n.val 0)

theorem forceOrEnergy_program_smooth {k : ℕ} (depth : ℕ) {clock : ClockAt k} (hc : SmoothClock clock)
    (equation : Option (Fin 4)) (n : Fin (depth+1)) :
    SmoothSymbol (forceOrEnergy depth clock equation n) := by
  unfold forceOrEnergy
  apply smoothSymbol_sub
  · apply smoothSymbol_sub
    · apply smoothSymbol_sub
      · exact smoothSymbol_add (sourceAffine_program_smooth depth hc equation n)
          (smoothSymbol_mul (smoothSymbol_const (1/2))
            (sourceTable_program_smooth depth hc 0 0 equation traceSeries_smooth n))
      · apply smoothSymbol_sum
        intro i _
        exact smoothSymbol_mul (smoothSymbol_const (1/2))
          (sourceTable_program_smooth depth hc (Fin.succ i) (Fin.succ i) equation
            (sourceSeries_smooth _) n)
    · apply smoothSymbol_sum
      intro i _
      exact sourceTable_program_smooth depth hc _ _ equation (sourceSeries_smooth _) n
  · apply smoothSymbol_sum
    intro i _
    exact sourceTable_program_smooth depth hc _ _ equation (sourceSeries_smooth _) n

end LowEnergy.PreparationVacuumEngineSmooth
