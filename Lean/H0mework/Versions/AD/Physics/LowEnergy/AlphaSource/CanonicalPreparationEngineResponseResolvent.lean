import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineResponseSeries

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineResponse
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

open Lean Elab Term in
elab "filtration_const%" name:str : term => do
  unless #["R_agreement","J_agreement","word_agreement","R_succ"].contains name.getString do
    throwError "Not a frozen original program filtration theorem"
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineFiltration 0) "LowEnergy") "PreparationVacuumEngineIdentities"
  Lean.Meta.mkConstWithFreshMVarLevels (Name.str ns name.getString)

private abbrev originalR := engine_const% "resolvent"
private abbrev originalRNext := program_const% "resolventNext"
private abbrev originalEll := program_const% "ellPolynomial"
private abbrev originalClockAt := engine_const% "clockAt"

def sourceNewestEll (k : ℕ) : AngularPolynomial :=
  sourceNewestPolynomial k 0+∑ a : Fin 3,MvPolynomial.X a*sourceNewestPolynomial k (Fin.succ a)

private theorem originalEll_coefficient (k : ℕ) (i : ℕ) :
    originalEll (sourceEngine k) i=sourceClockCoefficient k 0 i+
      ∑ a : Fin 3,MvPolynomial.X a*sourceClockCoefficient k (Fin.succ a) i := by
  program_unfold "ellPolynomial"
  program_unfold "clockPolynomial"
  rfl

theorem sourceEll_newest (k : ℕ) : originalEll (sourceEngine (k+1)) (k+1)=sourceNewestEll k := by
  rw [originalEll_coefficient]
  simp only [sourceClockCoefficient_newest,sourceNewestEll]

theorem sourceEll_padding (k : ℕ) : originalEll (sourceEngine k) (k+1)=0 := by
  rw [originalEll_coefficient]
  simp only [sourceClockCoefficient_padding,mul_zero,Finset.sum_const_zero,add_zero]

theorem sourceEll_preserves (k : ℕ) (i : ℕ) (hi : i≤k) :
    originalEll (sourceEngine (k+1)) i=originalEll (sourceEngine k) i := by
  rw [originalEll_coefficient,originalEll_coefficient]
  simp only [sourceClockCoefficient_preserves k _ i hi]

private theorem R_newest {l : ℕ} (k : ℕ) (c : ClockAt l) (X : List AngularPolynomial) :
    (originalR (k+1) c X).getD (k+1) 0=originalRNext c X (originalR k c X) (k+1) := by
  have succ := (filtration_const% "R_succ") k c X
  change originalR (k+1) c X=originalR k c X++[originalRNext c X (originalR k c X) (k+1)] at succ
  rw [succ]
  rw [List.getD_append_right]
  · simp only [source_resolvent_length,Nat.sub_self,List.getD_cons_zero]
  · exact (source_resolvent_length k c X).le

private theorem resolvent_change (k : ℕ) (A : List AngularPolynomial) (i j : ℕ)
    (hi : i≤k+1) (hj : j≤k+1-i) :
    (if i=0 ∧ k+1-i-j=0 then 0 else
      weighted (k+1-i-j) (originalEll (sourceEngine (k+1)) i) (A.getD j 0))-
    (if i=0 ∧ k+1-i-j=0 then 0 else
      weighted (k+1-i-j) (originalEll (sourceEngine k) i) (A.getD j 0))=
      if i=k+1 then sourceNewestEll k*A.getD 0 0 else 0 := by
  by_cases last : i=k+1
  · subst i
    have jzero : j=0 := by omega
    subst j
    simp [sourceEll_newest,sourceEll_padding,weighted_zero]
  · rw [sourceEll_preserves k i (by omega)]
    simp only [sub_self,if_neg last]

theorem sourceResolvent_newest (k : ℕ) (X Y : List AngularPolynomial)
    (lower : ∀ j, j≤k → X.getD j 0=Y.getD j 0) :
    (originalR (k+1) (sourceEngine (k+1)) X).getD (k+1) 0-
      (originalR (k+1) (sourceEngine k) Y).getD (k+1) 0=
      MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*
        (X.getD (k+1) 0-Y.getD (k+1) 0-
          sourceNewestEll k*(originalR k (sourceEngine k) Y).getD 0 0) := by
  have previous := (filtration_const% "R_agreement") k (sourceEngine (k+1)) (sourceEngine k)
    X Y (sourceEngine_clockAgreement k) lower
  change originalR k (sourceEngine (k+1)) X=originalR k (sourceEngine k) Y at previous
  rw [R_newest,R_newest,previous]
  program_unfold "resolventNext"
  program_unfold "scale"
  have each :
    (∑ i ∈ Finset.range (k+1+1),∑ j ∈ Finset.range (k+1+1-i),
      ((if i=0 ∧ k+1-i-j=0 then 0 else weighted (k+1-i-j)
          (originalEll (sourceEngine (k+1)) i) ((originalR k (sourceEngine k) Y).getD j 0))-
        (if i=0 ∧ k+1-i-j=0 then 0 else weighted (k+1-i-j)
          (originalEll (sourceEngine k) i) ((originalR k (sourceEngine k) Y).getD j 0))))=
      sourceNewestEll k*(originalR k (sourceEngine k) Y).getD 0 0 := by
    have changed :
      (∑ i ∈ Finset.range (k+1+1),∑ j ∈ Finset.range (k+1+1-i),
        ((if i=0 ∧ k+1-i-j=0 then 0 else weighted (k+1-i-j)
            (originalEll (sourceEngine (k+1)) i) ((originalR k (sourceEngine k) Y).getD j 0))-
          (if i=0 ∧ k+1-i-j=0 then 0 else weighted (k+1-i-j)
            (originalEll (sourceEngine k) i) ((originalR k (sourceEngine k) Y).getD j 0))))=
      (∑ i ∈ Finset.range (k+1+1),∑ j ∈ Finset.range (k+1+1-i),
        if i=k+1 then sourceNewestEll k*(originalR k (sourceEngine k) Y).getD 0 0 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact resolvent_change k _ i j (by have := Finset.mem_range.mp hi; omega)
        (by have := Finset.mem_range.mp hj; omega)
    rw [changed]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
  simp_rw [Finset.sum_sub_distrib] at each
  rw [←each]
  ring

end LowEnergy.PreparationVacuumEngineResponse
