import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Classical
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Source

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.CanonicalMatter
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open YangMills.FullPairing Stage10.ChargedPreparation LowEnergy.FullQuantum
open Stage9DEF.Compatibility
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open StageNineMatterPointwiseEquation StageNineCurrentCoframeMatterTemporalPrincipal
open scoped InnerProductSpace
noncomputable section

theorem native_time_pair (point : BasePoint) (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier) :
    normalizedMomentum actual point dual matter = dual (diracMatrixMatterAction diracGammaZero matter) := by
  rw [normalizedMomentum, LinearMap.smul_apply, LinearMap.comp_apply, actual_temporal_principal,
    actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos, map_smul]
  simp only [smul_eq_mul]
  have nonzero : (lapse : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  field_simp
  simp [Complex.I_sq]

def temporalMother : YangMills.FullPairing.Mother := flipMatter.comp (diracMatrixMatterAction diracGammaZero)

theorem positive_time_preparation (matter : DiracExteriorMatterCarrier) :
    temporalMother (preparation matter) = preparation matter := by
  funext spin
  fin_cases spin <;>
    simp [temporalMother, flipMatter, spinFlip, diracMatrixMatterAction, diracGammaZero,
      preparation, Fin.sum_univ_four]

theorem paired_time (matter : DiracExteriorMatterCarrier) :
    pairedMother preparation (temporalMother.comp preparation) matter =
      dualPreparation (diracMatrixMatterAction diracGammaZero (preparation matter)) := by
  simp [pairedMother, dualPreparation, temporalMother, fromOperator, operator]

theorem prepared_time_pair (point : BasePoint) :
    normalizedMomentum actual point ((actual.conjugateMatter point).comp dualPreparation)
      (preparation (actual.matter point)) = 4*(spinScale : ℂ) := by
  rw [native_time_pair, LinearMap.comp_apply, ← paired_time, dual_gram]
  have same : temporalMother.comp preparation = preparation := by
    apply LinearMap.ext
    exact positive_time_preparation
  rw [same, full_prepared_inner]
  ring

theorem prepared_time_positive (point : BasePoint) :
    0 < (normalizedMomentum actual point ((actual.conjugateMatter point).comp dualPreparation)
      (preparation (actual.matter point))).re := by
  rw [prepared_time_pair]
  simpa using mul_pos (by norm_num : (0 : ℝ) < 4) spinScale_pos

theorem action_time_momentum (source : SmoothUnifiedSource) (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    matterDifferentialMomentum source configuration (matterCoordinateEquiv ((-Complex.I) • matter)) 0 point =
      (normalizedMomentum configuration point (configuration.conjugateMatter point) matter).re := by
  unfold matterDifferentialMomentum matterDifferentialVariationVector normalizedMomentum
    currentCoframeMatterTemporalPrincipal generatedVolumeDensity
  simp only [toContinuumPointField, LinearEquiv.symm_apply_apply, map_smul,
    LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

def preparedConfiguration : StageNineHolonomicConfiguration :=
  { Stage10.Runtime.configuration with
    matter := fun point => preparation (Stage10.Runtime.configuration.matter point)
    conjugateMatter := fun point => (Stage10.Runtime.configuration.conjugateMatter point).comp dualPreparation }

theorem prepared_action_time_momentum (point : BasePoint) :
    matterDifferentialMomentum Stage10.Runtime.source preparedConfiguration
      (matterCoordinateEquiv ((-Complex.I) • preparedConfiguration.matter point)) 0 point =
      4*spinScale := by
  rw [Stage10.Runtime.source_eq, action_time_momentum, preparedConfiguration, Stage10.Runtime.configuration_eq]
  change (normalizedMomentum actual point ((actual.conjugateMatter point).comp dualPreparation)
    (preparation (actual.matter point))).re = _
  rw [prepared_time_pair]
  simp

end
end SaturationMonoid.PhysicsCore.Stage10.CanonicalMatter
