import H0mework.Versions.R2.Physics.SpinPair.DiracActual

/-! The full frozen covariant-derivative load of the shared actual. Its
sixteen entries feed the original coframe derivative without new equations. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineCoframeLocalDifferentiability StageNineCoframeVariation
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open StageNineDiracKineticLocalSpinDensity StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineDiracDualYukawaLocalSpinDensity
open StageNineScalarLocalSpinDensity StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionVariationDensity StageNineEnrichedProofFreeSource
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7ExteriorBreakingYukawa

noncomputable section

private abbrev Source := positiveSmoothUnifiedSource

private theorem spinPair_timeLoad (direction : LorentzianIndex) (rate p q u v : ℂ) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma direction)
      (spinPairMatter (Complex.I*rate*u) (-Complex.I*rate*v))) =
      if direction = 0 then 2*rate*(p*v+q*u) else 0 := by
  rw [map_smul, spinPairDual_diracMatrix]
  fin_cases direction <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree, smul_eq_mul]
  all_goals ring_nf
  all_goals
    simp [Complex.I_sq]

private theorem spinPair_rotationLoad
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
  all_goals
    simp [Complex.I_sq]
    ring

def actualKineticLoad (point : BasePoint) : LorentzianCoframe :=
  fun internal direction =>
    (actual.conjugateMatter point (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (holonomicMatterCovariantDerivative actual point direction))).re

private theorem actualKineticLoad_time (point : BasePoint) (internal : LorentzianIndex) :
    actualKineticLoad point internal 0 =
      if internal = 0 then 4*spinScale*frequency else 0 := by
  unfold actualKineticLoad
  rw [actual_conjugateMatter, actual_matterCovariant_time, spinPair_timeLoad,
    upperDual_lower_product, lowerDual_upper_product]
  split_ifs <;> simp [Complex.mul_re, Complex.mul_im]
  all_goals ring

private theorem actualKineticLoad_space (point : BasePoint)
    (internal : LorentzianIndex) (direction : Fin 3) :
    actualKineticLoad point internal direction.succ =
      if internal = direction.succ then -2*spinScale*(spinScale-gaugeScale) else 0 := by
  unfold actualKineticLoad
  rw [actual_conjugateMatter, actual_matterCovariant_spatial, spinPair_rotationLoad,
    upperDual_lower_product, lowerDual_upper_product]
  split_ifs <;> simp [Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem actualKineticLoad_diagonal (point : BasePoint) :
    actualKineticLoad point = Matrix.diagonal
      ![4*spinScale*frequency, -2*spinScale*(spinScale-gaugeScale),
        -2*spinScale*(spinScale-gaugeScale), -2*spinScale*(spinScale-gaugeScale)] := by
  ext internal direction
  induction direction using Fin.cases with
  | zero =>
      rw [actualKineticLoad_time]
      fin_cases internal <;> simp
  | succ direction =>
      rw [actualKineticLoad_space]
      fin_cases internal <;> fin_cases direction <;> simp

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

theorem actual_frozenKineticDensity (point : BasePoint) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumMatterKineticDensity Source 0 point
      (withCoframe (toContinuumPointField actual point) candidate) =
      |candidate.det| * ∑ direction, ∑ internal,
        candidate⁻¹ direction internal * actualKineticLoad point internal direction := by
  unfold generatedDensitizedContinuumMatterKineticDensity generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [withCoframe, toContinuumPointField, generatedVolumeDensity,
    matterDualFrameRelative_chartZero, matterDerivativeFrameRelative_zeroChart,
    Finset.smul_sum, map_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro direction _
  exact inverseGamma_load candidate direction _ _

private theorem actual_frozenScalarDensity_zero (point : BasePoint) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity Source 0 point
      (withCoframe (toContinuumPointField actual point) candidate) = 0 := by
  unfold generatedDensitizedContinuumScalarDensity generatedScalarKineticDensity generatedScalarPotential
  simp only [withCoframe, toContinuumPointField, actual_scalarCovariantDerivative_zero, actual_scalar,
    scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart]
  simp [scalarCoordinatePairingRe, scalarCoordinateSquaredNorm]

private theorem actual_frozenYukawaDensity_zero (point : BasePoint) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumDiracDualYukawaDensity Source 0 point
      (withCoframe (toContinuumPointField actual point) candidate) = 0 := by
  have vector : generatedContinuumDiracDualYukawaVector Source 0 point
      (withCoframe (toContinuumPointField actual point) candidate) = 0 := by
    have original := actual_yukawaVector_zero point
    unfold generatedContinuumDiracDualYukawaVector at original ⊢
    simpa only [withCoframe] using original
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  rw [vector]
  simp

theorem actual_frozenMatterDensity (point : BasePoint) (candidate : LorentzianCoframe) :
    diracDualFormNativeCoframeMatterDensity Source point (toContinuumPointField actual point) candidate =
      |candidate.det| * ∑ direction, ∑ internal,
        candidate⁻¹ direction internal * actualKineticLoad point internal direction := by
  unfold diracDualFormNativeCoframeMatterDensity generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [actual_frozenScalarDensity_zero, actual_frozenKineticDensity, actual_frozenYukawaDensity_zero]
  simp

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
