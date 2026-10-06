import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Source
import H0mework.Versions.AB.Physics.MotherSource.ActionNormalization

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open DiracCliffordRepresentation Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing ChargedPreparation.SpatialSpectrum Stage10.CanonicalMatter
open StageNineGlobalIntegratedAction StageNineMatterPointwiseEquation
open scoped Matrix InnerProductSpace
noncomputable section

theorem amplitude_square (point : BasePoint) : star (amplitude point)*amplitude point = (1/2 : ℂ) := by
  simp [amplitude]
  have phase := Source.phase_star_mul frequency point
  have scale : (spinScale : ℂ)^2 = 2 := by exact_mod_cast spinScale_sq
  change (starRingEnd ℂ) (upperPhase point)*upperPhase point = 1 at phase
  linear_combination ((spinScale : ℂ)^2/4)*phase + scale/4

theorem values_square (point : BasePoint) (momentum : Fin 3 → ℝ) :
    (∑ index : Source.Index, star (values point momentum index)*values point momentum index) =
      (weight momentum : ℂ) := by
  have factor : (∑ index : Source.Index, star (values point momentum index)*values point momentum index) =
      (star (amplitude point)*amplitude point)*
        ∑ index : Fin 4, star (coefficients momentum index)*coefficients momentum index := by
    simp [values, upperValues, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  rw [factor, amplitude_square, coefficients_square]
  simp [weight]
  ring

def normalization (momentum : Fin 3 → ℝ) : ℝ := (Real.sqrt (weight momentum))⁻¹

theorem normalized_weight (momentum : Fin 3 → ℝ) : normalization momentum^2*weight momentum = 1 := by
  rw [normalization, inv_pow, Real.sq_sqrt (weight_positive momentum).le,
    inv_mul_cancel₀ (weight_positive momentum).ne']

theorem normalized_weight_complex (momentum : Fin 3 → ℝ) :
    (normalization momentum : ℂ)^2*(weight momentum : ℂ) = 1 := by
  exact_mod_cast normalized_weight momentum

def normalizedPreparation (momentum : Fin 3 → ℝ) : Mother :=
  (normalization momentum : ℂ) • preparation momentum

def normalizedValues (point : BasePoint) (momentum : Fin 3 → ℝ) : Source.Index → ℂ :=
  (normalization momentum : ℂ) • values point momentum

theorem normalized_source (point : BasePoint) (momentum : Fin 3 → ℝ) :
    normalizedPreparation momentum (embed (Source.vector point)) = embed (normalizedValues point momentum) := by
  simp only [normalizedPreparation, LinearMap.smul_apply, source_preparation, normalizedValues, map_smul]

theorem full_prepared (point : BasePoint) (momentum : Fin 3 → ℝ) :
    operator (normalizedPreparation momentum) (YangMills.FullPairing.prepared point) =
      naturalCoordinates (embed (normalizedValues point momentum)) := by
  rw [YangMills.FullPairing.prepared, operator_coordinates, normalized_source]

theorem normalized_values_square (point : BasePoint) (momentum : Fin 3 → ℝ) :
    (∑ index : Source.Index, star (normalizedValues point momentum index)*normalizedValues point momentum index) = 1 := by
  have real : star (normalization momentum : ℂ) = (normalization momentum : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
  simp only [normalizedValues, Pi.smul_apply, smul_eq_mul, star_mul, real]
  have factor : (∑ index : Source.Index,
      (star (values point momentum index)*(normalization momentum : ℂ))*
        ((normalization momentum : ℂ)*values point momentum index)) =
      (normalization momentum : ℂ)^2*
        ∑ index : Source.Index, star (values point momentum index)*values point momentum index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [factor, values_square, normalized_weight_complex]

theorem full_prepared_gram (point : BasePoint) (momentum : Fin 3 → ℝ) :
    inner ℂ (operator (normalizedPreparation momentum) (YangMills.FullPairing.prepared point))
      (operator (normalizedPreparation momentum) (YangMills.FullPairing.prepared point)) = 1 := by
  rw [full_prepared, inner_embed, coordinates_embed, normalized_values_square]

theorem prepared_time_pair (point : BasePoint) (momentum : Fin 3 → ℝ) :
    LowEnergy.FullQuantum.normalizedMomentum actual point
      ((actual.conjugateMatter point).comp (canonicalDual (normalizedPreparation momentum)))
      (normalizedPreparation momentum (actual.matter point)) = 4*(spinScale : ℂ) := by
  rw [canonical_time_gram, full_prepared_gram, mul_one]

theorem original_current (point : BasePoint) (momentum : Fin 3 → ℝ) :
    actual.conjugateMatter point
      (canonicalDual (normalizedPreparation momentum) (currentAction 0 HyperchargeResponse.chargeDirection
        (normalizedPreparation momentum (actual.matter point)))) = -4*(spinScale : ℂ) := by
  rw [canonical_current_gram]
  have composed : operator (canonicalCharge.comp (normalizedPreparation momentum))
      (YangMills.FullPairing.prepared point) =
        operator canonicalCharge (operator (normalizedPreparation momentum) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared, operator_coordinates]
  rw [composed, full_prepared, operator_coordinates, inner_embed]
  simp_rw [canonical_charge_coordinates, mul_neg]
  rw [Finset.sum_neg_distrib, normalized_values_square]
  ring

theorem normalized_full_hamiltonian (point : BasePoint) (momentum : Fin 3 → ℝ) :
    LowEnergy.FullQuantum.hamiltonian Stage10.Runtime.configuration point momentum
      (normalizedPreparation momentum (embed (Source.vector point))) =
        (energy momentum : ℂ) • normalizedPreparation momentum (embed (Source.vector point)) := by
  simp only [normalizedPreparation, LinearMap.smul_apply, source_preparation, map_smul,
    original_full_hamiltonian]
  exact smul_comm _ _ _

def normalizedConfiguration (momentum : Fin 3 → ℝ) : StageNineHolonomicConfiguration :=
  { Stage10.Runtime.configuration with
    matter := fun point => normalizedPreparation momentum (Stage10.Runtime.configuration.matter point)
    conjugateMatter := fun point => (Stage10.Runtime.configuration.conjugateMatter point).comp
      (canonicalDual (normalizedPreparation momentum)) }

theorem action_unit_phase (point : BasePoint) (momentum : Fin 3 → ℝ) :
    Stage10.ActionNormalization.actionScale*
      matterDifferentialMomentum Stage10.Runtime.source (normalizedConfiguration momentum)
        (matterCoordinateEquiv ((-Complex.I) • (normalizedConfiguration momentum).matter point)) 0 point = 1 := by
  have native : matterDifferentialMomentum Stage10.Runtime.source (normalizedConfiguration momentum)
      (matterCoordinateEquiv ((-Complex.I) • (normalizedConfiguration momentum).matter point)) 0 point = 4*spinScale := by
    rw [Stage10.Runtime.source_eq, action_time_momentum]
    change (LowEnergy.FullQuantum.normalizedMomentum Stage10.Runtime.configuration point
      ((Stage10.Runtime.configuration.conjugateMatter point).comp (canonicalDual (normalizedPreparation momentum)))
      (normalizedPreparation momentum (Stage10.Runtime.configuration.matter point))).re = _
    rw [Stage10.Runtime.configuration_eq, prepared_time_pair]
    simp
  rw [native, Stage10.ActionNormalization.actionScale_source]
  exact inv_mul_cancel₀ (mul_pos (by norm_num) spinScale_pos).ne'

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle
