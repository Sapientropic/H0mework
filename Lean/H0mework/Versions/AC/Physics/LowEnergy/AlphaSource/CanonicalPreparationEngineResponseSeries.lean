import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineFiltration

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineResponse
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

private abbrev originalClockAt := engine_const% "clockAt"
private abbrev originalJ := engine_const% "js"

def sourceClockCoefficient (k : ℕ) (a : Fin 4) (i : ℕ) : AngularPolynomial :=
  MvPolynomial.C (originalClockAt (sourceEngine k) a i)

def sourceNewestPolynomial (k : ℕ) (a : Fin 4) : AngularPolynomial :=
  MvPolynomial.C (sourceEngine (k+1) a (Fin.last (k+1)))

theorem sourceEngine_seed_preserved (k : ℕ) (a : Fin 4) :
    sourceEngine k a ⟨0,by omega⟩=if a=0 then sourceClock else 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have equal := sourceEngine_preserves k a ⟨0,by omega⟩
    exact equal.trans ih

theorem sourceClockCoefficient_zero (k : ℕ) (a : Fin 4) :
    sourceClockCoefficient k a 0=MvPolynomial.C (if a=0 then sourceClock else 0) := by
  unfold sourceClockCoefficient
  program_unfold "clockAt"
  simp only [show 0<k+1 by omega,dif_pos]
  rw [sourceEngine_seed_preserved]

theorem sourceClockCoefficient_padding (k : ℕ) (a : Fin 4) :
    sourceClockCoefficient k a (k+1)=0 := by
  unfold sourceClockCoefficient
  program_unfold "clockAt"
  simp

theorem sourceClockCoefficient_newest (k : ℕ) (a : Fin 4) :
    sourceClockCoefficient (k+1) a (k+1)=sourceNewestPolynomial k a := by
  unfold sourceClockCoefficient sourceNewestPolynomial
  program_unfold "clockAt"
  simp only [show k+1<k+1+1 by omega,dif_pos]
  rfl

theorem sourceClockCoefficient_preserves (k : ℕ) (a : Fin 4) (i : ℕ) (hi : i≤k) :
    sourceClockCoefficient (k+1) a i=sourceClockCoefficient k a i :=
  congrArg MvPolynomial.C (sourceEngine_clockAgreement k a i hi)

private theorem convolution_change (k : ℕ) (a : Fin 4) (X Y : List AngularPolynomial)
    (lower : ∀ j, j≤k → X.getD j 0=Y.getD j 0) (i j : ℕ)
    (hi : i≤k+1) (hj : j≤k+1-i) :
    weighted (k+1-i-j) (sourceClockCoefficient (k+1) a i) (X.getD j 0)-
      weighted (k+1-i-j) (sourceClockCoefficient k a i) (Y.getD j 0)=
        if i=k+1 then sourceNewestPolynomial k a*Y.getD 0 0
        else if j=k+1 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0)
        else 0 := by
  by_cases ilast : i=k+1
  · subst i
    have jzero : j=0 := by omega
    subst j
    simp only [Nat.sub_self,sourceClockCoefficient_newest,
      sourceClockCoefficient_padding,weighted_zero,zero_mul,sub_zero,ite_true,
      lower 0 (by omega)]
  · by_cases jlast : j=k+1
    · subst j
      have izero : i=0 := by omega
      subst i
      rw [sourceClockCoefficient_preserves k a 0 (by omega)]
      simp only [Nat.sub_zero,Nat.sub_self,weighted_zero,if_neg (by omega : ¬0=k+1),ite_true]
      ring
    · have ibound : i≤k := by omega
      have jbound : j≤k := by omega
      rw [sourceClockCoefficient_preserves k a i ibound,lower j jbound]
      simp only [sub_self,if_neg ilast,if_neg jlast]

theorem sourceJordan_newest (k : ℕ) (a : Fin 4) (X Y : List AngularPolynomial)
    (lower : ∀ j, j≤k → X.getD j 0=Y.getD j 0) :
    (originalJ (k+1) (sourceEngine (k+1)) a X).getD (k+1) 0-
      (originalJ (k+1) (sourceEngine k) a Y).getD (k+1) 0=
      sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0)+
        sourceNewestPolynomial k a*Y.getD 0 0 := by
  program_unfold "js"
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    show k+1<k+1+1 by omega,dif_pos,Option.getD_some]
  program_unfold "clockPolynomial"
  change (∑ i ∈ Finset.range (k+1+1),∑ j ∈ Finset.range (k+1+1-i),
    weighted (k+1-i-j) (sourceClockCoefficient (k+1) a i) (X.getD j 0))-
    (∑ i ∈ Finset.range (k+1+1),∑ j ∈ Finset.range (k+1+1-i),
    weighted (k+1-i-j) (sourceClockCoefficient k a i) (Y.getD j 0))=_
  rw [←Finset.sum_sub_distrib]
  simp_rw [←Finset.sum_sub_distrib]
  have each :
      (∑ i ∈ Finset.range (k+1+1),∑ j ∈ Finset.range (k+1+1-i),
        (weighted (k+1-i-j) (sourceClockCoefficient (k+1) a i) (X.getD j 0)-
          weighted (k+1-i-j) (sourceClockCoefficient k a i) (Y.getD j 0)))=
      (∑ i ∈ Finset.range (k+1+1),∑ j ∈ Finset.range (k+1+1-i),
        if i=k+1 then sourceNewestPolynomial k a*Y.getD 0 0
        else if j=k+1 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact convolution_change k a X Y lower i j (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hj; omega)
  rw [each]
  simp only [Finset.sum_ite_irrel]
  have endpoint (i : ℕ) :
      (∑ j ∈ Finset.range (k+1+1-i),
        if j=k+1 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0) else 0)=
      if i=0 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0) else 0 := by
    by_cases izero : i=0
    · subst i
      simp
    · have outside : ¬k+1<k+1+1-i := by omega
      simp [outside,izero]
  simp_rw [endpoint]
  have split (f : ℕ → AngularPolynomial) (i : ℕ) :
      (if i=k+1 then f i else if i=0 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0) else 0)=
      (if i=k+1 then f i else 0)+(if i=0 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0) else 0) := by
    by_cases last : i=k+1
    · subst i
      simp
    · simp only [if_neg last,zero_add]
  let F : ℕ → AngularPolynomial := fun i => ∑ _j ∈ Finset.range (k+1+1-i),sourceNewestPolynomial k a*Y.getD 0 0
  change (∑ i ∈ Finset.range (k+1+1),if i=k+1 then F i else
    if i=0 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0) else 0)=_
  trans (∑ i ∈ Finset.range (k+1+1),((if i=k+1 then F i else 0)+
    (if i=0 then sourceClockCoefficient k a 0*(X.getD (k+1) 0-Y.getD (k+1) 0) else 0)))
  · exact Finset.sum_congr rfl (fun i _ => split F i)
  rw [Finset.sum_add_distrib]
  simp [F]
  ring

end LowEnergy.PreparationVacuumEngineResponse
