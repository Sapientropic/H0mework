import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEnginePaidForces

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEnginePaidDepth
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities PreparationVacuumEngineResponse
open PreparationVacuumEngineCancellation PreparationVacuumCanonicalMoyal PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open PreparationPhaseSource PreparationVacuumWeyl
open scoped BigOperators

private abbrev originalSource := table_const% "sourceSeries"

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

theorem sourceEnergyResponse_zero (k : ℕ) (zp : PreparationVacuumCanonicalMoyal.Phase) :
    sourceEquationResponse k none zp=0 := by
  unfold sourceEquationResponse sourceAffineResponse sourceTableResponse
  unfold_response_table
  simp
  simp only [sourceWordPair,sourceActZero,sourceActVariation,sourceClockCoefficient_zero,sourceNewestEll]
  simp
  unfold sourceNewestPolynomial sourceInversePolynomial
  simp only [Fin.sum_univ_succ,mul_add,add_mul,mul_sub]
  simp
  simp only [←MvPolynomial.C_mul,MvPolynomial.X,monomial_mul_C,MvPolynomial.C_mul_monomial]
  simp only [average_add,average_sub,average_neg,average_C_mul,average_monomial,average_constant,average_zero]
  simp only [moment_single]
  simp only [engineSource,PreparationVacuumEnergyTail.originalEnginePrincipalLeaves]
  simp
  rw [engineTrace_principal]
  dsimp only [sourceClock,sourceTrace,Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
  simp [engineSource,PreparationVacuumEnergyTail.originalEnginePrincipalLeaves]
  by_cases zero : C (nativePhase zp).1 (nativePhase zp).2=0
  · simp [zero]
  · field_simp [zero]
    ring

theorem sourceEngineEnergy_newestExcluded (k : ℕ) :
    sourceEngineEnergy (k+1)=forceOrEnergy (k+1) (sourceEngine k) none (Fin.last (k+1)) := by
  funext zp
  have response := congrFun (sourceEquation_newest k none) zp
  rw [sourceEnergyResponse_zero k zp] at response
  change sourceEngineEnergy (k+1) zp-_=0 at response
  linarith

end LowEnergy.PreparationVacuumEnginePaidDepth
