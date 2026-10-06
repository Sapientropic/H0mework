import H0mework.Versions.AB.Physics.MotherSource.HyperchargeResponse.Gauge
import H0mework.Versions.AB.Physics.LowEnergyResponse.ScalarSignature

/-! Scalar response of the same full U temporal gauge perturbation.
The original joint vacuum and the original action sign remain explicit. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
namespace SaturationMonoid.PhysicsCore.Stage10.HyperchargeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLimitScalarBalanceClosure
open Stage9C.Material.SpinPair
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

/-- Infinitesimal hypercharge action on the original four-channel vacuum. -/
def scalarCharge : ScalarCoordinateCarrier :=
  scalarMotherLieAction (p286LieBlockEmbed chargeDirection)
    (sourceGeneratedVacuumCoordinates Stage10.Runtime.source)

theorem scalar_derivative (potential : BasePoint → ℝ) (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative (primitive potential) point direction =
      if direction = 0 then potential point • scalarCharge else 0 := by
  have original := congrFun (actual_scalarCovariantDerivative_zero point) direction
  have originalAction :
      scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point direction))
        (actual.scalar point) = 0 := by
    simpa [holonomicScalarCovariantDerivative, actual_scalar, fieldDirectionalDerivative] using original
  simp only [holonomicScalarCovariantDerivative, primitive, Stage10.Runtime.configuration_eq,
    p286LieBlockEmbed_add, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_add, scalarMotherLieAction_real_smul, originalAction, zero_add]
  rw [actual_scalar]
  simp only [fieldDirectionalDerivative]
  rw [scalarCharge, Stage10.Runtime.source_eq]
  split_ifs <;> simp

theorem actual_scalar_kinetic (potential : BasePoint → ℝ) (point : BasePoint) :
    generatedScalarKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      -scalarCoordinateSquaredNorm (potential point • scalarCharge) / (2 * lapse^2) := by
  have field : holonomicScalarCovariantDerivative (primitive potential) point =
      fun direction => if direction = 0 then potential point • scalarCharge else 0 :=
    funext (scalar_derivative potential point)
  unfold generatedScalarKineticDensity
  simp only [toContinuumPointField]
  rw [field]
  simp only [scalarFrameRelativeCovariantDerivative, Stage10.Runtime.source_eq,
    scalarFrameRelativeCoordinates_zeroChart]
  have coframe : (primitive potential).coframe point = actual.coframe point := by
    simp only [primitive, Stage10.Runtime.configuration_eq]
  rw [coframe]
  exact LowEnergy.Response.ScalarSignature.temporal_kinetic point (potential point • scalarCharge)

theorem fundamental_charge_basis (index : SU7MotherIndex) :
    fundamentalMotherLieAction (p286LieBlockEmbed chargeDirection) (su7FundamentalBasis index) =
      ((fundamentalHyperchargeWeight index : ℂ) * Complex.I) • su7FundamentalBasis index := by
  fin_cases index <;> ext row <;> fin_cases row <;>
    norm_num [fundamentalMotherLieAction, chargeDirection, p286LieBlockEmbed,
      rawP286LieBlock, weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      hyperchargeGenerator, su7FundamentalBasis, Matrix.mulVecLin, Matrix.mulVec,
      fundamentalHyperchargeWeight] <;> simp

/-- The original exterior representation generates every charge weight. -/
theorem exterior_charge_basis (degree : ℕ) (index : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree (p286LieBlockEmbed chargeDirection)
      (su7ExteriorBasis degree index) =
      ((exteriorHyperchargeWeight index : ℂ) * Complex.I) • su7ExteriorBasis degree index := by
  classical
  rw [exteriorMotherLieAction_basis]
  have term (position : Fin degree) :
      (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree (p286LieBlockEmbed chargeDirection) index position) =
      ((fundamentalHyperchargeWeight (exteriorPositionEquiv index position).1 : ℂ) * Complex.I) •
        su7ExteriorBasis degree index := by
    rw [exteriorBasisLieActionTerm_eq_update]
    have eigen := fundamental_charge_basis (exteriorPositionEquiv index position).1
    change fundamentalMotherLieAction (p286LieBlockEmbed chargeDirection)
      (exteriorBasisInput degree index position) = _ at eigen
    change fundamentalMotherLieAction (p286LieBlockEmbed chargeDirection)
      (exteriorBasisInput degree index position) =
      ((fundamentalHyperchargeWeight (exteriorPositionEquiv index position).1 : ℂ) * Complex.I) •
        exteriorBasisInput degree index position at eigen
    rw [eigen, (exteriorPower.ιMulti ℂ degree).map_update_smul,
      Function.update_eq_self, exteriorBasisInput_wedge_eq_basis]
  change (∑ position : Fin degree, (exteriorPower.ιMulti ℂ degree)
    (exteriorBasisLieActionInput degree (p286LieBlockEmbed chargeDirection) index position)) = _
  simp_rw [term]
  rw [← Finset.sum_smul, ← Finset.sum_mul]
  congr 2
  rw [← Int.cast_sum]
  congr 1
  exact exteriorPosition_sum_eq_subset_sum index fundamentalHyperchargeWeight

/-- Both charged components of the actual four-channel vacuum are retained. -/
theorem joint_scalar_charge :
    exteriorMotherLieAction 4 (p286LieBlockEmbed chargeDirection)
      finiteGenerationJointBreakingScalar =
      -Complex.I • finiteGenerationBreakingTensor 0 0 +
        Complex.I • finiteGenerationBreakingTensor 1 1 := by
  have weights (o i : Fin 2) :
      exteriorHyperchargeWeight (finiteGenerationScalarIndex o i) =
        if o = 0 ∧ i = 0 then -1 else if o = 1 ∧ i = 1 then 1 else 0 := by
    fin_cases o <;> fin_cases i <;> decide
  unfold finiteGenerationJointBreakingScalar
  simp only [map_sum]
  simp only [finiteGenerationBreakingTensor]
  simp only [exterior_charge_basis]
  simp [Fin.sum_univ_two, weights]

theorem scalarCharge_coordinates (index : ScalarBasisIndex) :
    scalarCharge index =
      if index = finiteGenerationScalarIndex 0 0 then -Complex.I
      else if index = finiteGenerationScalarIndex 1 1 then Complex.I else 0 := by
  have distinct : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 1 1 := by decide
  unfold scalarCharge scalarMotherLieAction
  rw [Stage10.Runtime.source_eq]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply,
    positive_sourceGeneratedVacuumBase, joint_scalar_charge, map_add, map_smul]
  by_cases first : index = finiteGenerationScalarIndex 0 0
  · subst index
    simp [scalarCoordinateEquiv, finiteGenerationBreakingTensor, distinct]
  · by_cases second : index = finiteGenerationScalarIndex 1 1
    · subst index
      simp [scalarCoordinateEquiv, finiteGenerationBreakingTensor, Ne.symm distinct]
    · simp [scalarCoordinateEquiv, finiteGenerationBreakingTensor, first, second]

theorem scalarCharge_norm (amplitude : ℝ) :
    scalarCoordinateSquaredNorm (amplitude • scalarCharge) = 2 * amplitude^2 := by
  have distinct : finiteGenerationScalarIndex 0 0 ≠ finiteGenerationScalarIndex 1 1 := by decide
  have term (index : ScalarBasisIndex) :
      Complex.normSq ((amplitude • scalarCharge) index) =
        (if index = finiteGenerationScalarIndex 0 0 then amplitude^2 else 0) +
        (if index = finiteGenerationScalarIndex 1 1 then amplitude^2 else 0) := by
    simp only [PiLp.smul_apply, scalarCharge_coordinates]
    by_cases first : index = finiteGenerationScalarIndex 0 0
    · subst index
      simp [distinct, pow_two]
    · by_cases second : index = finiteGenerationScalarIndex 1 1
      · subst index
        simp [Ne.symm distinct, pow_two]
      · simp [first, second]
  simp only [scalarCoordinateSquaredNorm, term, Finset.sum_add_distrib]
  simp
  ring

theorem actual_scalar_kinetic_exact (potential : BasePoint → ℝ) (point : BasePoint) :
    generatedScalarKineticDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (primitive potential) point) =
      -(potential point)^2 / lapse^2 := by
  rw [actual_scalar_kinetic, scalarCharge_norm]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.HyperchargeResponse
