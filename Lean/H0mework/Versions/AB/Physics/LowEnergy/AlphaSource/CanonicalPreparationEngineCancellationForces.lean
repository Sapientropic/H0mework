import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineCancellationEquation
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockPoleSupport

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineCancellation
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities PreparationVacuumEngineResponse
open PreparationVacuumCanonicalMoyal PreparationActualFactor PreparationVacuumClockPole
open PreparationVacuumClockJacobian CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open PreparationPhaseSource PreparationVacuumWeyl
open scoped BigOperators Matrix

open Lean Elab Tactic in
elab "unfold_response_table" : tactic => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  let ids := #["table","energyTable","differentiateTerm","derivativeExponent","sourceSeries","traceSeries",
    "crossFirst","crossSecond","crossSlot"].map (fun suffix => mkIdent (Name.str ns suffix))
  evalTactic (← `(tactic| simp only [$[$ids:ident],*,Fin.sum_univ_succ]))

private theorem average_add (P Q : AngularPolynomial) : average (P+Q)=average P+average Q := by
  funext zp
  have delta := congrFun (average_sub (P+Q) Q) zp
  simp only [add_sub_cancel_right,Pi.sub_apply] at delta
  change _=average P zp+average Q zp
  linarith

private theorem average_zero : average (0 : AngularPolynomial)=0 := by
  simp [average]

private theorem average_neg (P : AngularPolynomial) : average (-P)=-average P := by
  simpa only [zero_sub,average_zero] using average_sub 0 P

private theorem average_sum {α : Type*} (s : Finset α) (f : α → AngularPolynomial) :
    average (∑ i ∈ s,f i)=∑ i ∈ s,average (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,average_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,average_add,ih]

private theorem average_C_mul (f : Symbol) (P : AngularPolynomial) :
    average (MvPolynomial.C f*P)=f*average P := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [Finset.mul_sum,average_sum]
  simp only [MvPolynomial.C_mul_monomial,average_monomial]
  funext zp
  simp only [Finset.sum_apply,Pi.mul_apply]
  unfold average
  simp only [Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  change angularMoment u*(f zp*MvPolynomial.coeff u P zp)=f zp*(angularMoment u*MvPolynomial.coeff u P zp)
  ring

private theorem average_mul_C (P : AngularPolynomial) (f : Symbol) :
    average (P*MvPolynomial.C f)=f*average P := by
  rw [mul_comm]
  exact average_C_mul f P

private theorem monomial_mul_C (u : AngularExponent) (f g : Symbol) :
    MvPolynomial.monomial u f*MvPolynomial.C g=MvPolynomial.monomial u (f*g) := by
  rw [mul_comm,MvPolynomial.C_mul_monomial,mul_comm g f]

private theorem moment_single (i : Fin 3) : angularMoment (Finsupp.single i 1)=0 :=
  angularMoment_odd _ i (by simp)

private theorem moment_pair (i j : Fin 3) :
    angularMoment (Finsupp.single i 1+Finsupp.single j 1)=if i=j then 1/12 else 0 := by
  have n01 : (0 : Fin 3)≠1 := by decide
  have n02 : (0 : Fin 3)≠2 := by decide
  have n12 : (1 : Fin 3)≠2 := by decide
  have two : (⟨2,by omega⟩ : Fin 3)=2 := rfl
  fin_cases i <;> fin_cases j <;>
    norm_num [angularMoment,Fin.forall_fin_succ,Fin.prod_univ_succ,Fin.sum_univ_succ,
      Finsupp.single_apply,n01,n02,n12,Ne.symm n01,Ne.symm n02,Ne.symm n12,two,Nat.doubleFactorial]

private theorem moment_pair00 :
    angularMoment (Finsupp.single (0 : Fin 3) 1+Finsupp.single (0 : Fin 3) 1)=1/12 := by
  simpa only [ite_true] using moment_pair (0 : Fin 3) (0 : Fin 3)

private theorem moment_pair01 :
    angularMoment (Finsupp.single (0 : Fin 3) 1+Finsupp.single (1 : Fin 3) 1)=0 := by
  simpa only [if_neg (by decide : (0 : Fin 3)≠1)] using moment_pair (0 : Fin 3) (1 : Fin 3)

private theorem moment_pair02 :
    angularMoment (Finsupp.single (0 : Fin 3) 1+Finsupp.single (2 : Fin 3) 1)=0 := by
  simpa only [if_neg (by decide : (0 : Fin 3)≠2)] using moment_pair (0 : Fin 3) (2 : Fin 3)

private theorem moment_pair10 :
    angularMoment (Finsupp.single (1 : Fin 3) 1+Finsupp.single (0 : Fin 3) 1)=0 := by
  simpa only [if_neg (by decide : (1 : Fin 3)≠0)] using moment_pair (1 : Fin 3) (0 : Fin 3)

private theorem moment_pair11 :
    angularMoment (Finsupp.single (1 : Fin 3) 1+Finsupp.single (1 : Fin 3) 1)=1/12 := by
  simpa only [ite_true] using moment_pair (1 : Fin 3) (1 : Fin 3)

private theorem moment_pair12 :
    angularMoment (Finsupp.single (1 : Fin 3) 1+Finsupp.single (2 : Fin 3) 1)=0 := by
  simpa only [if_neg (by decide : (1 : Fin 3)≠2)] using moment_pair (1 : Fin 3) (2 : Fin 3)

private theorem moment_pair20 :
    angularMoment (Finsupp.single (2 : Fin 3) 1+Finsupp.single (0 : Fin 3) 1)=0 := by
  simpa only [if_neg (by decide : (2 : Fin 3)≠0)] using moment_pair (2 : Fin 3) (0 : Fin 3)

private theorem moment_pair21 :
    angularMoment (Finsupp.single (2 : Fin 3) 1+Finsupp.single (1 : Fin 3) 1)=0 := by
  simpa only [if_neg (by decide : (2 : Fin 3)≠1)] using moment_pair (2 : Fin 3) (1 : Fin 3)

private theorem moment_pair22 :
    angularMoment (Finsupp.single (2 : Fin 3) 1+Finsupp.single (2 : Fin 3) 1)=1/12 := by
  simpa only [ite_true] using moment_pair (2 : Fin 3) (2 : Fin 3)

theorem sourceForceResponse_jacobian (k : ℕ) (a : Fin 4) (zp : PreparationVacuumCanonicalMoyal.Phase) (nonzero : sourceClock zp≠0) :
    sourceEquationResponse k (some a) zp=
      ∑ b : Fin 4,principalForceJacobian zp a b*sourceEngine (k+1) b (Fin.last (k+1)) zp := by
  fin_cases a <;> unfold sourceEquationResponse sourceAffineResponse sourceTableResponse
  all_goals unfold principalForceJacobian
  all_goals unfold_response_table
  all_goals simp
  all_goals unfold_response_table
  all_goals simp
  all_goals simp only [sourceWordPair,sourceActZero,sourceActVariation,
    sourceClockCoefficient_zero,sourceNewestEll]
  all_goals try simp
  all_goals unfold sourceNewestPolynomial sourceInversePolynomial
  all_goals simp only [Fin.sum_univ_succ,mul_add,add_mul,mul_sub]
  all_goals simp
  all_goals simp only [←MvPolynomial.C_mul,MvPolynomial.X,MvPolynomial.C_mul_monomial,monomial_mul_C,MvPolynomial.monomial_mul]
  all_goals simp only [average_add,average_sub,average_neg,average_C_mul,
    average_monomial,average_constant,average_zero]
  all_goals try simp only [moment_single,
    moment_pair00,moment_pair01,moment_pair02,moment_pair10,moment_pair11,
    moment_pair12,moment_pair20,moment_pair21,moment_pair22]
  all_goals norm_num
  all_goals try simp only [mul_add,mul_sub,mul_neg,←MvPolynomial.C_mul,average_add]
  all_goals norm_num
  all_goals dsimp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,engineSource,
    PreparationVacuumEnergyTail.originalEnginePrincipalLeaves]
  all_goals simp
  all_goals try rw [engineTrace_principal]
  all_goals dsimp only [sourceTrace,sourceClock] at nonzero ⊢
  all_goals try rw [S_symmetric (nativePhase zp).1 (nativePhase zp).2 1 0]
  all_goals try rw [S_symmetric (nativePhase zp).1 (nativePhase zp).2 2 0]
  all_goals try rw [S_symmetric (nativePhase zp).1 (nativePhase zp).2 2 1]
  all_goals simp only [T,Fin.sum_univ_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  all_goals field_simp [nonzero]
  all_goals ring_nf
  all_goals try simp only [average_neg,←MvPolynomial.C_pow,
    monomial_mul_C,MvPolynomial.monomial_mul,average_monomial]
  all_goals try simp only [moment_single,
    moment_pair00,moment_pair01,moment_pair02,moment_pair10,moment_pair11,
    moment_pair12,moment_pair20,moment_pair21,moment_pair22]
  all_goals norm_num
  all_goals try rw [engineTrace_principal]
  all_goals dsimp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,sourceClock,sourceTrace]
  all_goals simp only [T,Fin.sum_univ_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  all_goals field_simp [nonzero]
  all_goals norm_num
  all_goals ring

theorem sourceEngineForces_successor_zero (k : ℕ) (a : Fin 4)
    (z : CanonicalPreparationCutoff.FlatConfiguration) (p : CanonicalPreparationSquareCutoff.PhysicalMomentum)
    (position : z∈thetaPositionClosed) (direction : normalizedMomentum p∈thetaDirectionClosed) (nonzero : p≠0) :
    sourceEngineForces (k+1) a (z,p)=0 := by
  let zp : PreparationVacuumCanonicalMoyal.Phase := (z,p)
  let residual : Fin 4 → ℝ := fun b => forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1)) zp
  let newest : Fin 4 → ℝ := fun b => sourceEngine (k+1) b (Fin.last (k+1)) zp
  have cone := source_support_positiveCone z p position direction nonzero
  have clock : sourceClock zp≠0 := (C_positive cone).ne'
  have legal := sourceJ_inverse_right zp cone (sourceM_det_nonzero z p position direction nonzero)
  rw [sourceJ_engine,←source_clock_inverse z p position direction nonzero] at legal
  have generated : newest=-((principalForceJacobian zp)⁻¹*ᵥresidual) := by
    funext b
    exact sourceEngine_generated k b zp
  have actual : (fun b => sourceEngineForces (k+1) b zp)=residual+principalForceJacobian zp*ᵥnewest := by
    funext b
    have response := congrFun (sourceEquation_newest k (some b)) zp
    rw [sourceForceResponse_jacobian k b zp clock] at response
    change sourceEngineForces (k+1) b zp-residual b=(principalForceJacobian zp*ᵥnewest) b at response
    change _=residual b+(principalForceJacobian zp*ᵥnewest) b
    linarith
  rw [generated,Matrix.mulVec_neg,Matrix.mulVec_mulVec,legal,Matrix.one_mulVec,add_neg_cancel] at actual
  exact congrFun actual a

end LowEnergy.PreparationVacuumEngineCancellation
