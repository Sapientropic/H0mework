import H0mework.Versions.R2.Physics.SourceDirac.Forward
import H0mework.Versions.R2.Physics.SpinPair.CoframeMatter

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineCoframeLocalDifferentiability StageNineCoframeVariation
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open StageNineDiracKineticLocalSpinDensity StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineDiracDualYukawaLocalSpinDensity
open StageNineScalarLocalSpinDensity StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionVariationDensity StageNineEnrichedProofFreeSource
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeCoframeLocalVariation StageNineCartanTangentSimplicityResponse
open StageNineHolonomicGravityCurvatureVarianceNormalization StageNineBlockwiseConstitutive
open StageNineTopologicalFourFormPairing
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous Gauge Dirac
open SU7ExteriorBreakingYukawa

noncomputable section

theorem field_gravityCurvature (step : ℕ) (point : BasePoint) :
    holonomicGravityCurvature (fieldAt step) point = homogeneousCurvature spinScale :=
  homogeneousCurvature_actual _ _ (field_gravityConnection step) point

theorem field_gravityMultiplier (step : ℕ) :
    (fieldAt step).gravitySimplicityMultiplier =
      fun _ => homogeneousGravityReaction (clock step) spinScale := by
  have generated : (fieldAt step).gravitySimplicityMultiplier =
      formNativeGravityReactionField (fieldAt step) :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated (sourceAt step) _
  rw [generated]
  funext point
  change gravityInternalDualEquiv (physicalIIPlusBivector ((fieldAt step).coframe point)) -
    gravityInternalPairVarianceNormalization (holonomicGravityCurvature (fieldAt step) point) = _
  rw [field_coframe, field_gravityCurvature]
  rfl

theorem gravity_reaction_coordinates (step : ℕ) (point : BasePoint)
    (row column : LorentzianIndex) :
    formNativeCoframeConstraintReaction (toContinuumPointField (fieldAt step) point)
      (Matrix.single row column 1) =
      if row = column then
        if row = 0 then 3 - 3*spinScale^2 else clock step*(3-spinScale^2)
      else 0 := by
  change gravityTopologicalWedgeCoefficient ((fieldAt step).gravitySimplicityMultiplier point)
    (physicalIIPlusCoframeTangent ((fieldAt step).coframe point) (Matrix.single row column 1)) = _
  rw [field_gravityMultiplier, field_coframe]
  exact homogeneousGravityReaction_coordinates _ _ _ _

private theorem time_load (direction : LorentzianIndex) (rate p q u v : ℂ) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma direction)
      (spinPairMatter (Complex.I*rate*u) (-Complex.I*rate*v))) =
      if direction = 0 then 2*rate*(p*v+q*u) else 0 := by
  rw [map_smul, spinPairDual_diracMatrix]
  fin_cases direction <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree, smul_eq_mul]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

private theorem rotation_load
    (first : LorentzianIndex) (second : Fin 3) (coefficient p q u v : ℂ) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma first)
      (coefficient • diracMatrixMatterAction (spinRotation second) (spinPairMatter u v))) =
      if first = second.succ then -2*coefficient*(p*v+q*u) else 0 := by
  rw [map_smul, map_smul, map_smul]
  have composed : diracMatrixMatterAction (diracGamma first)
      (diracMatrixMatterAction (spinRotation second) (spinPairMatter u v)) =
      diracMatrixMatterAction (diracGamma first * spinRotation second) (spinPairMatter u v) := by
    rw [diracMatrixMatterAction_mul, LinearMap.comp_apply]
  rw [composed, spinPairDual_diracMatrix]
  fin_cases first <;> fin_cases second <;>
    simp [spinRotation, diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, smul_eq_mul] <;> ring_nf
  all_goals simp [Complex.I_sq]; ring

def kineticLoad (step : ℕ) (point : BasePoint) : LorentzianCoframe :=
  fun internal direction =>
    ((fieldAt step).conjugateMatter point (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (holonomicMatterCovariantDerivative (fieldAt step) point direction))).re

private theorem kinetic_load_time (step : ℕ) (point : BasePoint) (internal : LorentzianIndex) :
    kineticLoad step point internal 0 =
      if internal = 0 then 4*spinScale*phaseRate step else 0 := by
  unfold kineticLoad
  rw [field_dual, matter_covariant_time, time_load, upperDual_lower, lowerDual_upper]
  split_ifs <;> simp [Complex.mul_re, Complex.mul_im]
  all_goals ring

private theorem kinetic_load_space (step : ℕ) (point : BasePoint)
    (internal : LorentzianIndex) (direction : Fin 3) :
    kineticLoad step point internal direction.succ =
      if internal = direction.succ then -2*spinScale*(spinScale-gaugeScale) else 0 := by
  unfold kineticLoad
  rw [field_dual, matter_covariant_spatial, rotation_load, upperDual_lower, lowerDual_upper]
  split_ifs <;> simp [Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem kinetic_load_diagonal (step : ℕ) (point : BasePoint) :
    kineticLoad step point = Matrix.diagonal
      ![4*spinScale*phaseRate step, -2*spinScale*(spinScale-gaugeScale),
        -2*spinScale*(spinScale-gaugeScale), -2*spinScale*(spinScale-gaugeScale)] := by
  ext internal direction
  induction direction using Fin.cases with
  | zero => rw [kinetic_load_time]; fin_cases internal <;> simp
  | succ direction => rw [kinetic_load_space]; fin_cases internal <;> fin_cases direction <;> simp

private theorem inverseGamma_load
    (candidate : LorentzianCoframe) (direction : LorentzianIndex)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (derivative : DiracExteriorMatterCarrier) :
    (dual (Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := candidate, derivative := 0 } direction) derivative)).re =
      ∑ internal, candidate⁻¹ direction internal *
        (dual (Complex.I • diracMatrixMatterAction (diracGamma internal) derivative)).re := by
  unfold inverseCoframeDiracGamma
  simp only [Fin.sum_univ_four, coframeDiracMatrixMatterAction_add_matrix,
    coframeDiracMatrixMatterAction_smul_matrix, smul_add, map_add, map_smul, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]

theorem frozen_kinetic_density (step : ℕ) (point : BasePoint) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumMatterKineticDensity (sourceAt step) 0 point
      (withCoframe (toContinuumPointField (fieldAt step) point) candidate) =
      |candidate.det| * ∑ direction, ∑ internal,
        candidate⁻¹ direction internal * kineticLoad step point internal direction := by
  unfold generatedDensitizedContinuumMatterKineticDensity generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [withCoframe, toContinuumPointField, generatedVolumeDensity,
    matterDualFrameRelative_chartZero, matterDerivativeFrameRelative_zeroChart,
    Finset.smul_sum, map_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro direction _
  exact inverseGamma_load candidate direction _ _

private theorem frozen_scalar_density_zero (step : ℕ) (point : BasePoint) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity (sourceAt step) 0 point
      (withCoframe (toContinuumPointField (fieldAt step) point) candidate) = 0 := by
  unfold generatedDensitizedContinuumScalarDensity generatedScalarKineticDensity generatedScalarPotential
  simp only [withCoframe, toContinuumPointField, scalar_covariant_zero, field_scalar,
    scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart]
  simp [scalarCoordinatePairingRe, scalarCoordinateSquaredNorm]

private theorem frozen_yukawa_density_zero (step : ℕ) (point : BasePoint) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumDiracDualYukawaDensity (sourceAt step) 0 point
      (withCoframe (toContinuumPointField (fieldAt step) point) candidate) = 0 := by
  have vector : generatedContinuumDiracDualYukawaVector (sourceAt step) 0 point
      (withCoframe (toContinuumPointField (fieldAt step) point) candidate) = 0 := by
    have original := Scalar.yukawa_vector_zero step point
    unfold generatedContinuumDiracDualYukawaVector at original ⊢
    simpa only [withCoframe] using original
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  rw [vector]
  simp

theorem frozen_matter_density (step : ℕ) (point : BasePoint) (candidate : LorentzianCoframe) :
    diracDualFormNativeCoframeMatterDensity (sourceAt step) point
      (toContinuumPointField (fieldAt step) point) candidate =
      |candidate.det| * inverseLoad (kineticLoad step point) candidate := by
  unfold diracDualFormNativeCoframeMatterDensity generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [frozen_scalar_density_zero, frozen_kinetic_density, frozen_yukawa_density_zero]
  simp [inverseLoad]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe
