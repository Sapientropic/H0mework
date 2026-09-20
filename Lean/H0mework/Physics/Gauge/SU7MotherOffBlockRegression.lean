import H0mework.Physics.Gauge.SU7MotherGaugeActionVariations

/-!
# Off-block mother-connection regression

A concrete skew-adjoint color/weak cross-block first-jet perturbation has
strictly positive full cross-spectral Frobenius energy.  Thus the mother action
detects departures from the P286 image while its exact block restriction
retains zero penalty.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherGaugeAction

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open SourceRelativePhysicalStationaryFamily
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations
open NonzeroSourceGaugeStationaryConfiguration
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction

noncomputable section

def colorZeroIndex : SU7MotherIndex := Sum.inl 0
def weakZeroIndex : SU7MotherIndex := Sum.inr (Sum.inl 0)

/-- A concrete skew-adjoint color/weak cross-block perturbation. -/
def offBlockRaw : Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  fun row column =>
    if row = colorZeroIndex ∧ column = weakZeroIndex then 1
    else if row = weakZeroIndex ∧ column = colorZeroIndex then -1
    else 0

def offBlockGenerator : SU7MotherLieMatrix := by
  refine ⟨offBlockRaw, ?_, ?_⟩
  · ext row column
    fin_cases row <;> fin_cases column <;> simp [offBlockRaw,
      colorZeroIndex, weakZeroIndex]
  · simp [Matrix.trace, offBlockRaw, colorZeroIndex, weakZeroIndex]

@[simp] theorem offBlockGenerator_colorWeak_entry :
    (offBlockGenerator : Matrix SU7MotherIndex SU7MotherIndex ℂ)
      colorZeroIndex weakZeroIndex = 1 := by
  simp [offBlockGenerator, offBlockRaw, colorZeroIndex, weakZeroIndex]

theorem offBlockEnergy_eq_of_cross_entries_eq
    (first second : SU7MotherLieMatrix)
    (entries_eq : ∀ row column,
      breakingLevel row ≠ breakingLevel column →
        (first : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column =
          (second : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column) :
    offBlockEnergy first = offBlockEnergy second := by
  unfold offBlockEnergy
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  by_cases sameLevel : breakingLevel row = breakingLevel column
  · simp [sameLevel]
  · simp [sameLevel, entries_eq row column sameLevel]

theorem offBlockEnergy_p286_add_generator
    (data : P286LieBlockData) :
    offBlockEnergy (p286LieBlockEmbed data + offBlockGenerator) =
      offBlockEnergy offBlockGenerator := by
  apply offBlockEnergy_eq_of_cross_entries_eq
  intro row column levels_ne
  have blockZero := selected_entry_zero_of_breakingLevel_ne
    positiveSource (p286LieBlockEmbed data)
    (p286LieBlockEmbed_selected positiveSource data)
    row column levels_ne
  change
    (p286LieBlockEmbed data : Matrix SU7MotherIndex SU7MotherIndex ℂ)
          row column +
        (offBlockGenerator : Matrix SU7MotherIndex SU7MotherIndex ℂ)
          row column =
      (offBlockGenerator : Matrix SU7MotherIndex SU7MotherIndex ℂ)
        row column
  rw [blockZero, zero_add]

theorem offBlockEnergy_offBlockGenerator_pos :
    0 < offBlockEnergy offBlockGenerator := by
  unfold offBlockEnergy
  apply Finset.sum_pos'
  · intro row _
    apply Finset.sum_nonneg
    intro column _
    split
    · norm_num
    · exact Complex.normSq_nonneg _
  · refine ⟨colorZeroIndex, Finset.mem_univ colorZeroIndex, ?_⟩
    apply Finset.sum_pos'
    · intro column _
      split
      · norm_num
      · exact Complex.normSq_nonneg _
    · refine ⟨weakZeroIndex, Finset.mem_univ weakZeroIndex, ?_⟩
      have levels_ne :
          breakingLevel colorZeroIndex ≠ breakingLevel weakZeroIndex := by
        norm_num [breakingLevel, colorZeroIndex, weakZeroIndex]
      rw [if_neg levels_ne, offBlockGenerator_colorWeak_entry]
      norm_num [Complex.normSq]

def addOffBlockExteriorPerturbation
    (q : SU7MotherGaugeConfiguration) : SU7MotherGaugeConfiguration :=
  { q with
    connection :=
      { q.connection with
        exteriorDerivative := fun pair =>
          if pair = 0 then
            q.connection.exteriorDerivative pair + offBlockGenerator
          else q.connection.exteriorDerivative pair } }

theorem motherBreakingPenalty_offBlockPerturbation_pos
    (q : StandardModelGaugeConfiguration) :
    0 < motherBreakingPenalty
      (addOffBlockExteriorPerturbation
        (liftStageFiveGaugeConfiguration q)) := by
  change 0 <
    (∑ direction : LorentzianIndex,
      offBlockEnergy
        ((liftStageFiveGaugeConfiguration q).connection.potential direction)) +
      (∑ pair : Fin 6,
        offBlockEnergy
          (if pair = 0 then
            (liftStageFiveGaugeConfiguration q).connection.exteriorDerivative pair +
              offBlockGenerator
          else
            (liftStageFiveGaugeConfiguration q).connection.exteriorDerivative pair)) +
      (∑ pair : Fin 6,
        offBlockEnergy ((liftStageFiveGaugeConfiguration q).auxiliary pair)) +
      (∑ pair : Fin 6,
        offBlockEnergy
          ((liftStageFiveGaugeConfiguration q).constitutiveMultiplier pair))
  have derivativePositive :
      0 < ∑ pair : Fin 6,
        offBlockEnergy
          (if pair = 0 then
            (liftStageFiveGaugeConfiguration q).connection.exteriorDerivative pair +
              offBlockGenerator
          else
            (liftStageFiveGaugeConfiguration q).connection.exteriorDerivative pair) := by
    apply Finset.sum_pos'
    · intro pair _
      exact offBlockEnergy_nonneg _
    · refine ⟨0, Finset.mem_univ 0, ?_⟩
      simp only [if_pos]
      change 0 < offBlockEnergy
        (liftSectorValue (q.strong.curvature 0) (q.weak.curvature 0)
          (q.hypercharge.curvature 0) + offBlockGenerator)
      rw [liftSectorValue, offBlockEnergy_p286_add_generator]
      exact offBlockEnergy_offBlockGenerator_pos
  have potentialNonneg :
      0 ≤ ∑ direction : LorentzianIndex,
        offBlockEnergy
          ((liftStageFiveGaugeConfiguration q).connection.potential direction) :=
    Finset.sum_nonneg fun direction _ => offBlockEnergy_nonneg _
  have auxiliaryNonneg :
      0 ≤ ∑ pair : Fin 6,
        offBlockEnergy ((liftStageFiveGaugeConfiguration q).auxiliary pair) :=
    Finset.sum_nonneg fun pair _ => offBlockEnergy_nonneg _
  have multiplierNonneg :
      0 ≤ ∑ pair : Fin 6,
        offBlockEnergy
          ((liftStageFiveGaugeConfiguration q).constitutiveMultiplier pair) :=
    Finset.sum_nonneg fun pair _ => offBlockEnergy_nonneg _
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos potentialNonneg derivativePositive)
      auxiliaryNonneg)
    multiplierNonneg

end
end SaturationMonoid.PhysicsCore.SU7MotherGaugeAction
