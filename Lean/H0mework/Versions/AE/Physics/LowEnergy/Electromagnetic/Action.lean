import H0mework.Versions.AE.Physics.LowEnergy.Electromagnetic.Direction
import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Action
import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Pair

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Action
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineDiracDualFormNativeMotherAction StageNineFormNativeMotherAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing Stage10 Stage10.CanonicalMatter
open scoped InnerProductSpace
noncomputable section

/-- The original time principal supplies the dual; the direction remains an actual gauge variation. -/
def canonicalDirection (direction : P286LieBlockData) : Mother :=
  phaseInverse.comp (currentAction 0 direction)

theorem canonical_direction_source (direction : P286LieBlockData) (matter : DiracExteriorMatterCarrier) :
    canonicalDirection direction matter = Complex.I •
      diracExteriorMotherLieAction (p286LieBlockEmbed direction) matter := by
  simp only [canonicalDirection, LinearMap.comp_apply, currentAction, LinearMap.smul_apply, diracGamma,
    Matrix.cons_val_zero, phaseInverse, LinearMap.neg_apply, map_smul]
  change Complex.I • phaseInverse (diracMatrixMatterAction diracGammaZero
    (diracExteriorMotherLieAction (p286LieBlockEmbed direction) matter)) = _
  rw [phase_inverse_source]

/-- Every native direction consumes the same repaired independent dual and source pairing. -/
theorem current_gram (direction : P286LieBlockData) (point : BasePoint) (preparation : Mother) :
    actual.conjugateMatter point
      (canonicalDual preparation (currentAction 0 direction (preparation (actual.matter point)))) =
      4*(spinScale : ℂ)*inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
        (operator ((canonicalDirection direction).comp preparation) (YangMills.FullPairing.prepared point)) := by
  have paired (matter : DiracExteriorMatterCarrier) :
      canonicalDual preparation (currentAction 0 direction (preparation matter)) =
        pairedMother preparation ((canonicalDirection direction).comp preparation) matter := by
    simp [canonicalDual, pairedMother, canonicalDirection, fromOperator, operator]
  rw [paired, dual_gram]

theorem canonical_coordinates (direction : P286LieBlockData) (values : Source.Index → ℂ)
    (index : Source.Index) :
    coordinates (canonicalDirection direction (embed values)) index =
      Complex.I*∑ other : Fin 2, values (index.1,other)*
        ((direction.1 : Matrix (Fin 3) (Fin 3) ℂ)
          (index.2.castLE (by decide)) (other.castLE (by decide)) +
          if index.2 = other then direction.2.2.1 else 0) := by
  rw [canonical_direction_source]
  change sourceColorDoubletDual index.2
    ((Complex.I • diracExteriorMotherLieAction (p286LieBlockEmbed direction)
      (sourceColorDiracMatter (fun spin state => values (spin,state)))) index.1) = _
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, sourceColorDoubletDual_motherAction]

private def restAmplitude (point : BasePoint) : ℂ :=
  (ChargedPreparation.CanonicalParticle.normalization 0 : ℂ)*
    ChargedPreparation.CanonicalParticle.amplitude point*(2*frequency : ℂ)

private theorem rest_values (point : BasePoint) :
    ChargedPreparation.CanonicalParticle.normalizedValues point 0 =
      ChargedPreparation.CanonicalParticle.upperValues ![0,restAmplitude point,-restAmplitude point,0] := by
  funext index
  rcases index with ⟨spin,state⟩
  fin_cases spin <;> fin_cases state <;>
    simp [ChargedPreparation.CanonicalParticle.normalizedValues, ChargedPreparation.CanonicalParticle.values,
      ChargedPreparation.CanonicalParticle.upperValues, ChargedPreparation.CanonicalParticle.coefficients,
      ChargedPreparation.SpatialSpectrum.rate, ChargedPreparation.SpatialSpectrum.spatialSquare,
      Real.sqrt_sq_eq_abs, abs_of_pos ChargedPreparation.Dispersion.frequency_pos, restAmplitude] <;> ring

private theorem rest_amplitude_unit (point : BasePoint) :
    2*(star (restAmplitude point)*restAmplitude point) = 1 := by
  have unit := ChargedPreparation.CanonicalParticle.normalized_values_square point 0
  rw [rest_values] at unit
  simpa [Fintype.sum_prod_type, ChargedPreparation.CanonicalParticle.upperValues,
    Fin.sum_univ_four, Fin.sum_univ_two, two_mul] using unit

/-- The original rest particle generates the complete native current, including the color-neutral part. -/
theorem original_rest_current (direction : P286LieBlockData) (point : BasePoint) :
    actual.conjugateMatter point
      (canonicalDual (ChargedPreparation.CanonicalParticle.normalizedPreparation 0)
        (currentAction 0 direction
          (ChargedPreparation.CanonicalParticle.normalizedPreparation 0 (actual.matter point)))) =
      4*(spinScale : ℂ)*Complex.I*
        (((direction.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0+
          (direction.1 : Matrix (Fin 3) (Fin 3) ℂ) 1 1)/2+direction.2.2.1) := by
  rw [current_gram]
  have composed : operator ((canonicalDirection direction).comp
      (ChargedPreparation.CanonicalParticle.normalizedPreparation 0)) (YangMills.FullPairing.prepared point) =
      operator (canonicalDirection direction)
        (operator (ChargedPreparation.CanonicalParticle.normalizedPreparation 0) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared, operator_coordinates]
  rw [composed, ChargedPreparation.CanonicalParticle.full_prepared, operator_coordinates, inner_embed]
  simp_rw [canonical_coordinates]
  rw [rest_values]
  simp only [Fintype.sum_prod_type]
  simp [ChargedPreparation.CanonicalParticle.upperValues, Fin.sum_univ_four, Fin.sum_univ_two, Fin.castLE]
  have unit := rest_amplitude_unit point
  change 2*((starRingEnd ℂ) (restAmplitude point)*restAmplitude point) = 1 at unit
  linear_combination (2*(spinScale : ℂ)*Complex.I*
    ((direction.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0+
      (direction.1 : Matrix (Fin 3) (Fin 3) ℂ) 1 1+2*direction.2.2.1))*unit

theorem neutral_matter_action (color weak hypercharge : ℝ) (values : Source.Index → ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed (Direction.neutral color weak hypercharge)) (embed values) =
      (((color+hypercharge : ℝ) : ℂ)*Complex.I) • embed values := by
  funext spin
  change exteriorSpinorMotherLieAction (p286LieBlockEmbed (Direction.neutral color weak hypercharge))
    (∑ state : Fin 2, values (spin,state) • sourceColorDoubletMatter state) =
      (((color+hypercharge : ℝ) : ℂ)*Complex.I) •
        (∑ state : Fin 2, values (spin,state) • sourceColorDoubletMatter state)
  simp only [map_sum, map_smul, Direction.source_doublet_action, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro state _
  exact smul_comm _ _ _

theorem neutral_canonical_action (color weak hypercharge : ℝ) (values : Source.Index → ℂ) :
    canonicalDirection (Direction.neutral color weak hypercharge) (embed values) =
      (-((color+hypercharge : ℝ) : ℂ)) • embed values := by
  rw [canonical_direction_source, neutral_matter_action, smul_smul]
  congr 1
  calc
    Complex.I*(((color+hypercharge : ℝ) : ℂ)*Complex.I) =
      ((color+hypercharge : ℝ) : ℂ)*(Complex.I*Complex.I) := by ring
    _ = -((color+hypercharge : ℝ) : ℂ) := by rw [Complex.I_mul_I, mul_neg_one]

/-- The actual all-momentum charged particle has its original action current in each neutral direction. -/
theorem original_neutral_current (color weak hypercharge : ℝ) (point : BasePoint) (momentum : Fin 3 → ℝ) :
    actual.conjugateMatter point
      (canonicalDual (ChargedPreparation.CanonicalParticle.normalizedPreparation momentum)
        (currentAction 0 (Direction.neutral color weak hypercharge)
          (ChargedPreparation.CanonicalParticle.normalizedPreparation momentum (actual.matter point)))) =
        -4*(spinScale : ℂ)*((color+hypercharge : ℝ) : ℂ) := by
  rw [current_gram]
  have composed :
      operator ((canonicalDirection (Direction.neutral color weak hypercharge)).comp
        (ChargedPreparation.CanonicalParticle.normalizedPreparation momentum)) (YangMills.FullPairing.prepared point) =
      (-((color+hypercharge : ℝ) : ℂ)) •
        operator (ChargedPreparation.CanonicalParticle.normalizedPreparation momentum) (YangMills.FullPairing.prepared point) := by
    have composition : operator ((canonicalDirection (Direction.neutral color weak hypercharge)).comp
        (ChargedPreparation.CanonicalParticle.normalizedPreparation momentum)) (YangMills.FullPairing.prepared point) =
      operator (canonicalDirection (Direction.neutral color weak hypercharge))
        (operator (ChargedPreparation.CanonicalParticle.normalizedPreparation momentum) (YangMills.FullPairing.prepared point)) := by
      simp [YangMills.FullPairing.prepared, operator_coordinates]
    rw [composition, ChargedPreparation.CanonicalParticle.full_prepared, operator_coordinates,
      neutral_canonical_action, map_smul]
  rw [composed, inner_smul_right, ChargedPreparation.CanonicalParticle.full_prepared_gram]
  ring

/-- The four generated scalar channels are consumed by the complete original mother action.
The electric term retains the actual background and every spatial cross term. -/
theorem neutral_mother_response (color weak hypercharge : BasePoint → ℝ) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Runtime.source 0 point
      (toContinuumPointField (TemporalGauge.configuration
        (fun p => Direction.neutral (color p) (weak p) (hypercharge p))) point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Runtime.source 0 point
        (toContinuumPointField Runtime.configuration point) +
      lapse*TemporalGauge.squared (TemporalGauge.electric
        (fun p => Direction.neutral (color p) (weak p) (hypercharge p)) point) -
      ((hypercharge point)^2+(weak point)^2+4*(color point)^2+
        (2*color point-weak point+hypercharge point)^2)/(2*lapse) := by
  rw [TemporalGauge.mother_density_shift]
  unfold TemporalGauge.quadraticDensity
  rw [show TemporalGauge.scalarCharge (Direction.neutral (color point) (weak point) (hypercharge point)) =
    Direction.scalarCharge (Direction.neutral (color point) (weak point) (hypercharge point)) from rfl,
    Direction.scalar_norm]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Action
