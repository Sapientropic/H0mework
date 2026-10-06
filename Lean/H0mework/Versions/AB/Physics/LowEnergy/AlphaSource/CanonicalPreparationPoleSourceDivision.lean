import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGNormalized
import Mathlib.RingTheory.MvPolynomial.Groebner

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPoleCancellation
open PreparationVacuumDAGCoefficient
open scoped BigOperators MonomialOrder

def sourceOrder : MonomialOrder CentralVariable := MonomialOrder.lex

theorem sourcePole_nonzero (i : Fin 3) : polePolynomial i≠0 := by
  fin_cases i
  · simp [polePolynomial]
  · simp [polePolynomial]
  · intro zero
    let e : CentralPolynomial →+* ℚ:=MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun j:Fin 7=>if j=1 then 2 else if j=2 ∨ j=3 then 1 else 0)
    have matrix : centralQ.map e=Matrix.diagonal (fun j:Fin 3=>if j=2 then (2:ℚ) else 1) := by
      ext a b
      fin_cases a <;> fin_cases b <;> norm_num [centralQ,e,Matrix.map_apply,Matrix.diagonal,Fin.ext_iff]
    have read:=congrArg e zero
    change e determinantPolynomial=0 at read
    rw [determinantPolynomial,e.map_det] at read
    change (centralQ.map e).det=0 at read
    rw [matrix] at read
    norm_num [Matrix.det_diagonal,Fin.prod_univ_three,Fin.ext_iff] at read

theorem sourcePole_leading_unit (i : Fin 3) : IsUnit (sourceOrder.leadingCoeff (polePolynomial i)) :=
  isUnit_iff_ne_zero.mpr (sourceOrder.leadingCoeff_ne_zero_iff.mpr (sourcePole_nonzero i))

def poleQuotient (i : Fin 3) (P : CentralPolynomial) : CentralPolynomial :=
  Classical.choose (MonomialOrder.div_single (m:=sourceOrder) (sourcePole_leading_unit i) P)

def poleRemainder (i : Fin 3) (P : CentralPolynomial) : CentralPolynomial :=
  Classical.choose (Classical.choose_spec (MonomialOrder.div_single (m:=sourceOrder) (sourcePole_leading_unit i) P))

theorem poleDivision_identity (i : Fin 3) (P : CentralPolynomial) :
    P=poleQuotient i P*polePolynomial i+poleRemainder i P :=
  (Classical.choose_spec (Classical.choose_spec (MonomialOrder.div_single (m:=sourceOrder)
    (sourcePole_leading_unit i) P))).1

theorem poleRemainder_reduced (i : Fin 3) (P : CentralPolynomial) :
    ∀ a∈(poleRemainder i P).support,¬ sourceOrder.degree (polePolynomial i)≤a :=
  (Classical.choose_spec (Classical.choose_spec (MonomialOrder.div_single (m:=sourceOrder)
    (sourcePole_leading_unit i) P))).2.2

theorem poleRemainder_zero_iff (i : Fin 3) (P : CentralPolynomial) :
    poleRemainder i P=0 ↔ polePolynomial i∣P := by
  constructor
  · intro zero
    refine ⟨poleQuotient i P,?_⟩
    simpa only [zero,add_zero,mul_comm] using poleDivision_identity i P
  · rintro ⟨q,hq⟩
    by_contra nonzero
    have difference : poleRemainder i P=polePolynomial i*(q-poleQuotient i P) := by
      have original : polePolynomial i*q=poleQuotient i P*polePolynomial i+poleRemainder i P :=
        hq.symm.trans (poleDivision_identity i P)
      linear_combination -original
    have delta : q-poleQuotient i P≠0 := by
      intro zero
      apply nonzero
      rw [difference,zero,mul_zero]
    have degree:=sourceOrder.degree_mul (sourcePole_nonzero i) delta
    rw [←difference] at degree
    have lower : sourceOrder.degree (polePolynomial i)≤ sourceOrder.degree (poleRemainder i P) := by
      rw [degree]
      exact le_self_add
    exact poleRemainder_reduced i P _ (sourceOrder.degree_mem_support nonzero) lower

end LowEnergy.PreparationVacuumPoleCancellation
