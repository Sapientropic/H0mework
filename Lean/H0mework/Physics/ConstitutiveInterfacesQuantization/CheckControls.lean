import H0mework.Physics.QuantumCompatibility.Hermitian
import H0mework.Physics.QuantumObservation.Prediction

/-! A changed dual is a changed observable.  These controls retain the source
preparation and expose the effect of omitting its independent-dual exchange. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.QuantizationCheck

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open SU7ExteriorMatterGaugeCovariantJet SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Matrix

noncomputable section

def rawCurrent (direction : LorentzianIndex) (generator : Fin 3) : Matrix8 :=
  compression (currentAction direction (sourceColorP286Generator generator))

private theorem generator_coordinates (generator : Fin 3) (output input : Fin 2) :
    sourceColorDoubletDual output
      (exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator generator))
        (sourceColorDoubletMatter input)) = sourceColorPauli generator output input := by
  rw [sourceColorDoublet_generatorAction]
  fin_cases output <;> simp [map_smul, sourceColorDoubletDual_basis]

theorem rawCurrent_mulVec (direction : LorentzianIndex) (generator : Fin 3)
    (values : Source.Index → ℂ) (row : Source.Index) :
    (rawCurrent direction generator *ᵥ values) row =
      ∑ spin, ∑ color, Complex.I * diracGamma direction row.1 spin *
        sourceColorPauli generator row.2 color * values (spin, color) := by
  rw [rawCurrent, compression_mulVec]
  change sourceColorDoubletDual row.2
      (Complex.I • ∑ spin, diracGamma direction row.1 spin •
        exteriorSpinorMotherLieAction
          (p286LieBlockEmbed (sourceColorP286Generator generator))
          (∑ color, values (spin, color) • sourceColorDoubletMatter color)) = _
  simp only [map_smul, map_sum, generator_coordinates, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext spin
  congr 1
  ext color
  ring

theorem rawCurrent_entry (direction : LorentzianIndex) (generator : Fin 3)
    (row column : Source.Index) :
    rawCurrent direction generator row column =
      Complex.I * diracGamma direction row.1 column.1 *
        sourceColorPauli generator row.2 column.2 := by
  rcases column with ⟨spin, color⟩
  have action := rawCurrent_mulVec direction generator (Pi.single (spin, color) 1) row
  fin_cases color <;>
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Fintype.sum_prod_type,
      mul_ite, Prod.mk.injEq] using action

theorem rawCurrent_source_read_phases (point : BasePoint) :
    vectorRead point (rawCurrent 1 0) =
      (star (upperPhase point) * lowerPhase point +
        star (lowerPhase point) * upperPhase point) / 4 := by
  unfold vectorRead
  simp_rw [rawCurrent_mulVec]
  simp [Source.vector, Source.amplitude, spinPairCoefficients, diracGamma,
    diracGammaOne, sourceColorPauli, Fintype.sum_prod_type, Fin.sum_univ_four,
    Fin.sum_univ_two]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Keeping the state but omitting the accepted independent dual changes the current. -/
theorem rawCurrent_source_read (point : BasePoint) :
    vectorRead point (rawCurrent 1 0) =
      (Observation.coherentWeight point : ℂ) - 1 / 2 := by
  rw [rawCurrent_source_read_phases, Observation.coherentWeight_formula,
    Complex.normSq_eq_conj_mul_self]
  simp only [map_div₀, map_add, map_ofNat]
  have upper := Source.phase_star_mul frequency point
  have lower := Source.phase_star_mul (-frequency) point
  change star (upperPhase point) * upperPhase point = 1 at upper
  change star (lowerPhase point) * lowerPhase point = 1 at lower
  change (starRingEnd ℂ) (upperPhase point) * upperPhase point = 1 at upper
  change (starRingEnd ℂ) (lowerPhase point) * lowerPhase point = 1 at lower
  change ((starRingEnd ℂ) (upperPhase point) * lowerPhase point +
    (starRingEnd ℂ) (lowerPhase point) * upperPhase point) / 4 = _
  linear_combination -upper / 4 - lower / 4

theorem omitted_dual_dark_read :
    vectorRead (Dynamics.timeDisplacement Observation.darkTime) (rawCurrent 1 0) =
      (-1 / 2 : ℂ) := by
  rw [rawCurrent_source_read, Observation.prediction_dark]
  norm_num

theorem accepted_dual_dark_read :
    State.evaluation (Dynamics.timeDisplacement Observation.darkTime)
      (physicalCurrent 1 (sourceColorP286Generator 0)) = (1 / 2 : ℂ) := by
  simpa using physicalCurrent_prediction (Dynamics.timeDisplacement Observation.darkTime) 0 0

theorem omitted_dual_dark_mismatch :
    vectorRead (Dynamics.timeDisplacement Observation.darkTime) (rawCurrent 1 0) ≠
      State.evaluation (Dynamics.timeDisplacement Observation.darkTime)
        (physicalCurrent 1 (sourceColorP286Generator 0)) := by
  rw [omitted_dual_dark_read, accepted_dual_dark_read]
  norm_num

theorem omitted_dual_zero_read : vectorRead 0 (rawCurrent 1 0) = (1 / 2 : ℂ) := by
  rw [rawCurrent_source_read, Observation.coherentWeight_zero]
  norm_num

/-- Agreement at the initial preparation does not preserve the current observable. -/
theorem initial_agreement_dark_separation :
    vectorRead 0 (rawCurrent 1 0) =
        State.evaluation 0 (physicalCurrent 1 (sourceColorP286Generator 0)) ∧
      vectorRead (Dynamics.timeDisplacement Observation.darkTime) (rawCurrent 1 0) ≠
        State.evaluation (Dynamics.timeDisplacement Observation.darkTime)
          (physicalCurrent 1 (sourceColorP286Generator 0)) := by
  constructor
  · rw [omitted_dual_zero_read]
    simpa using (physicalCurrent_prediction 0 0 0).symm
  · exact omitted_dual_dark_mismatch

end
end SaturationMonoid.PhysicsCore.QuantizationCheck
