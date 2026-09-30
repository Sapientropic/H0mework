import H0mework.Versions.X.NavierStokes.CartanAction.Response

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanCompensation

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineLorentzConnectionVariation
open StageNineHolonomicField StageNineFullDiracAdjointMaterial StageNineFullDiracAdjointLocalOperator
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativePauliJet
open NativeSourceCartan NativeCartanContorsionSupport NativeCartanMaterialResponse
open NativeMaterialAdjointPrincipal

noncomputable section

def correction (velocity : PhysicalSpace) (direction : Fin 4) :
    SU7MotherLieAlgebra.P286LieBlockData :=
  NativePauliCoframeAction.connection velocity (-response velocity) direction

def compensatedIncrement (velocity : PhysicalSpace) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  increment velocity direction + gaugeIncrement velocity (-response velocity) direction

theorem compensated_inverse_zero (velocity : PhysicalSpace) :
    currentCoframeMatterTemporalPrincipalInverse (NativeCanonicalFluidCoframe.coframe velocity)
      (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (compensatedIncrement velocity)) = 0 := by
  have phase : phaseResidual (normalizedVelocity velocity) (-response velocity) = 0 := by
    rw [show -response velocity = ((-1 : ℝ) : ℂ) • response velocity by simp,
      phase_smul, response_phase_zero, mul_zero]
  have sum : gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (compensatedIncrement velocity) =
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (increment velocity) +
        gaugeVector velocity (-response velocity) := by
    simp only [gaugeVectorAt, compensatedIncrement, map_add, Finset.sum_add_distrib, smul_add]
    rfl
  rw [sum, map_add, response_inverse, NativePauliCoframeAction.actual_inverse_response,
    phase, Complex.ofReal_zero, zero_smul, sub_zero, map_neg, add_neg_cancel]

theorem compensated_vector_zero (velocity : PhysicalSpace) :
    gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (compensatedIncrement velocity) = 0 := by
  have equation := congrArg (currentCoframeMatterTemporalPrincipal (NativeCanonicalFluidCoframe.coframe velocity))
    (compensated_inverse_zero velocity)
  rw [currentCoframeMatterTemporalPrincipalInverse_right _
    (NativeCanonicalFluidCoframe.temporalPrincipal_noncharacteristic velocity), map_zero] at equation
  exact equation

private theorem gamma_swap (first second : Fin 4) (different : first ≠ second) :
    diracGamma first * diracGamma second = -(diracGamma second * diracGamma first) := by
  apply add_eq_zero_iff_eq_neg.mp
  rw [diracGamma_clifford]
  simp [complexMinkowskiEntry, minkowskiInternalMetric, different]

theorem gamma_commutes_bivector (direction first second : Fin 4)
    (differentFirst : direction ≠ first) (differentSecond : direction ≠ second) :
    diracGamma direction * (diracGamma first * diracGamma second) =
      (diracGamma first * diracGamma second) * diracGamma direction := by
  rw [← mul_assoc, gamma_swap direction first differentFirst, neg_mul, mul_assoc,
    gamma_swap direction second differentSecond, mul_neg, neg_neg, mul_assoc]

def cartanOperator (velocity : PhysicalSpace) (direction : Fin 4) : Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift
    (lorentzSkewConnectionOfBivectorOneForm (contorsion velocity)) direction)

/-- The generated support closes the full Clifford commutator, not just a selected matter evaluation. -/
theorem gamma_commutes_increment (velocity : PhysicalSpace) (direction : Fin 4) :
    diracGamma direction * diracSpinConnectionLift
        (lorentzSkewConnectionOfBivectorOneForm (contorsion velocity)) direction =
      diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm (contorsion velocity)) direction * diracGamma direction := by
  simp only [diracSpinConnectionLift, loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro pair _
  by_cases repeated : direction = lorentzBivectorFirst pair ∨ direction = lorentzBivectorSecond pair
  · rw [contorsion_support velocity direction pair repeated]
    simp
  · rw [gamma_commutes_bivector direction _ _ (not_or.mp repeated).1 (not_or.mp repeated).2]

theorem principal_commutes_cartanOperator (velocity : PhysicalSpace) (direction : Fin 4)
    (matter : DiracExteriorMatterCarrier) :
    principal velocity direction (cartanOperator velocity direction matter) =
      cartanOperator velocity direction (principal velocity direction matter) := by
  simp only [principal_gamma, cartanOperator, LinearMap.smul_apply, map_smul]
  simp only [← LinearMap.comp_apply, ← SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul]
  rw [gamma_commutes_increment]

def correctionOperator (velocity : PhysicalSpace) (direction : Fin 4) : Module.End ℂ DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed (correction velocity direction))

theorem principal_commutes_correctionOperator (velocity : PhysicalSpace) (direction : Fin 4)
    (matter : DiracExteriorMatterCarrier) :
    principal velocity direction (correctionOperator velocity direction matter) =
      correctionOperator velocity direction (principal velocity direction matter) := by
  have commuting := LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal
    (inverseCoframeDiracGamma {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction)
    (exteriorSpinorMotherLieAction (p286LieBlockEmbed (correction velocity direction)))) matter
  simpa only [principal, correctionOperator, diracExteriorMotherLieAction, LinearMap.smul_apply,
    map_smul, LinearMap.comp_apply] using congrArg (fun value => Complex.I • value) commuting

theorem cartan_adjoint (velocity : PhysicalSpace) (direction : Fin 4) (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (cartanOperator velocity direction matter) candidate =
      -fullCanonicalDiracAdjoint matter (cartanOperator velocity direction candidate) :=
  LinearMap.congr_fun (fullCanonicalDiracAdjoint_spinConnection _ direction matter) candidate

theorem correction_adjoint (velocity : PhysicalSpace) (direction : Fin 4) (matter candidate : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (correctionOperator velocity direction matter) candidate =
      -fullCanonicalDiracAdjoint matter (correctionOperator velocity direction candidate) :=
  LinearMap.congr_fun (fullCanonicalDiracAdjoint_motherLieConnection _ matter) candidate

/-- The correction preserves the entire canonical-dual equation on every full-carrier variation. -/
theorem compensated_dual_zero (velocity : PhysicalSpace) (candidate : DiracExteriorMatterCarrier) :
    (∑ direction, NativeCanonicalFluidCoframe.dual velocity (principal velocity direction
      (cartanOperator velocity direction candidate + correctionOperator velocity direction candidate))) = 0 := by
  have term (direction : Fin 4) : NativeCanonicalFluidCoframe.dual velocity (principal velocity direction
      (cartanOperator velocity direction candidate + correctionOperator velocity direction candidate)) =
      fullCanonicalDiracAdjoint (principal velocity direction
        (cartanOperator velocity direction (NativeCanonicalFluidCoframe.matter velocity) +
          correctionOperator velocity direction (NativeCanonicalFluidCoframe.matter velocity))) candidate := by
    rw [NativeSourceMaterialAdjoint.source_dual, principal_adjoint]
    simp only [fullCanonicalDiracAdjoint_add, LinearMap.add_apply, cartan_adjoint, correction_adjoint,
      map_add, principal_commutes_cartanOperator, principal_commutes_correctionOperator]
    ring
  have vector : (∑ direction, principal velocity direction
      (cartanOperator velocity direction (NativeCanonicalFluidCoframe.matter velocity) +
        correctionOperator velocity direction (NativeCanonicalFluidCoframe.matter velocity))) = 0 := by
    simpa only [principal, cartanOperator, correctionOperator, correction, gaugeVectorAt,
      compensatedIncrement, increment, gaugeIncrement, Finset.smul_sum, LinearMap.smul_apply]
      using compensated_vector_zero velocity
  have dual := congrArg (fun matter => fullCanonicalDiracAdjoint matter candidate) vector
  simp only [Fin.sum_univ_four, fullCanonicalDiracAdjoint_add, LinearMap.add_apply,
    fullCanonicalDiracAdjoint_zero, LinearMap.zero_apply] at dual
  simpa only [term, Fin.sum_univ_four] using dual

end
end SaturationMonoid.NavierStokes.NativeCartanCompensation
