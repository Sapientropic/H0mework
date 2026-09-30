import H0mework.Versions.X.Fock.HistoryModel.SourceWord.Minimal
import H0mework.Probability.Information.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordCodeRisk

open SourceGeneratedActionWords SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open scoped Classical
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype
  SourceConditionalNext.Image.valuesMeasurable SourceConditionalNext.Image.valuesSingleton

variable {Code : Type*} [Fintype Code] [DecidableEq Code]
  [MeasurableSpace Code] [MeasurableSingletonClass Code]

def query (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code) : Actors runtime → Code :=
  fun actor => encode (SourceWordMinimalCode.wordEquiv runtime word actor)

def risk (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code)
    (decoder : Code → SourceJointClockGraph.Carrier) : ℝ :=
  ∑ actor : Actors runtime,
    (((((Fock.sourceLaw (inventoryBound runtime)).map nativeStep).map
      (Fock.actualWord (inventoryBound runtime + 1) word)).map
        (Fock.point (inventoryBound runtime + 1)))
      (SourceWordMinimalCode.wordRead runtime word actor)).toReal *
      ‖SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor -
        decoder (query runtime word encode actor)‖ ^ 2

omit [Fintype Code] [DecidableEq Code] [MeasurableSpace Code]
  [MeasurableSingletonClass Code] in
theorem risk_eq (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code)
    (decoder : Code → SourceJointClockGraph.Carrier) :
    risk runtime word encode decoder =
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor -
          decoder (query runtime word encode actor)‖ ^ 2 := by
  unfold risk
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceWordMinimalCode.wordRead,
    SourceWordDynamicNext.source_word_mass runtime word actor]

omit [Fintype Code] in
theorem information_lower (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code)
    (decoder : Code → SourceJointClockGraph.Carrier) :
    SourceConditionalInventory.cost (inventoryBound runtime) (query runtime word encode) /
        (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ((Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
          (inventoryBound runtime) (query runtime word encode)) - 1) / 12) ≤
      risk runtime word encode decoder := by
  rw [risk_eq]
  exact SourceCompiledGWord.information_lower runtime (inventoryBound runtime + 1)
    word (query runtime word encode) decoder

theorem cost_deficit (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code) :
    ((inventoryBound runtime + 1 : ℝ) - Fintype.card Code) /
      (inventoryBound runtime + 1 : ℝ) ≤
      SourceConditionalInventory.cost (inventoryBound runtime) (query runtime word encode) /
        (inventoryBound runtime + 1 : ℝ) := by
  rw [SourceConditionalInventory.cost_eq]
  have cardBound :
      (SourceUniformFibreVariance.outputs (inventoryBound runtime)
        (query runtime word encode)).card ≤ Fintype.card Code := by
    calc
      _ ≤ (Finset.univ : Finset Code).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = _ := Finset.card_univ
  have realBound :
      ((SourceUniformFibreVariance.outputs (inventoryBound runtime)
        (query runtime word encode)).card : ℝ) ≤ Fintype.card Code := by
    exact_mod_cast cardBound
  gcongr

/-- The executed word's original source mass pays both lost code states and conditional uncertainty. -/
theorem code_information_risk (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code)
    (decoder : Code → SourceJointClockGraph.Carrier) :
    ((inventoryBound runtime + 1 : ℝ) - Fintype.card Code) /
        (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ((Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
          (inventoryBound runtime) (query runtime word encode)) - 1) / 12) ≤
      risk runtime word encode decoder := by
  exact (add_le_add (cost_deficit runtime word encode) le_rfl).trans
    (information_lower runtime word encode decoder)

omit [Fintype Code] [DecidableEq Code] in
theorem risk_account (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code)
    (decoder : Code → SourceJointClockGraph.Carrier) :
    risk runtime word encode decoder =
      SourceConditionalInventory.cost (inventoryBound runtime) (query runtime word encode) /
        (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime))
          (query runtime word encode)
          (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
            (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
              (inventoryBound runtime)))‖ ^ 2 +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceCompiledGWord.effect (inventoryBound runtime + 1) word
          (SourceVectorMoment.mean
            (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
              (query runtime word encode) (query runtime word encode actor)
              (SourceWeightedRecovery.observed_supported _ _ actor
                (SourceUniformFibreVariance.source_positive _ actor)))
            (SourceConditionalInventory.values (inventoryBound runtime))) -
          decoder (query runtime word encode actor)‖ ^ 2 := by
  rw [risk_eq]
  exact SourceCompiledGWord.error_account runtime (inventoryBound runtime + 1)
    word (query runtime word encode) decoder

omit [Fintype Code] [MeasurableSpace Code] [MeasurableSingletonClass Code] in
theorem entropy_nonnegative (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code) :
    0 ≤ SourceUniformFibreInformation.conditionalEntropy
      (inventoryBound runtime) (query runtime word encode) := by
  rw [← SourceUniformFibreInformation.image_conditional_entropy
    (inventoryBound runtime) (query runtime word encode)
    (fun actor : Actors runtime => actor) (fun _ _ same => same)
    (SourceUniformFibreVariance.source_positive (inventoryBound runtime))]
  exact SourceConditionalNext.conditionalEntropy_nonnegative _ _ _ _

theorem deficit_positive (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → Code)
    (decoder : Code → SourceJointClockGraph.Carrier)
    (short : Fintype.card Code < inventoryBound runtime + 1) :
    0 < risk runtime word encode decoder := by
  have hInfo := information_lower runtime word encode decoder
  have hCost := cost_deficit runtime word encode
  have hEnt := entropy_nonnegative runtime word encode
  have hSlope : 0 ≤ ((SourceCopyWordAffine.compile
    (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 := sq_nonneg _
  have hExp : 0 ≤
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
        (inventoryBound runtime) (query runtime word encode)) - 1) / 12 := by
    have h := Real.add_one_le_exp (2 * SourceUniformFibreInformation.conditionalEntropy
      (inventoryBound runtime) (query runtime word encode))
    nlinarith
  have hShort : (Fintype.card Code : ℝ) < inventoryBound runtime + 1 := by
    exact_mod_cast short
  have hDen : 0 < (inventoryBound runtime + 1 : ℝ) := by positivity
  have hMargin : 0 < ((inventoryBound runtime + 1 : ℝ) - Fintype.card Code) /
      (inventoryBound runtime + 1 : ℝ) := div_pos (by linarith) hDen
  nlinarith [mul_nonneg hSlope hExp]

omit [Fintype Code] [DecidableEq Code] [MeasurableSpace Code]
  [MeasurableSingletonClass Code] in
theorem canonical_risk_zero (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    risk runtime word (fun code => code) (SourceWordMinimalCode.decode runtime word) = 0 := by
  unfold risk query
  apply Finset.sum_eq_zero
  intro actor _
  rw [SourceWordMinimalCode.decode_actual]
  simp

theorem actual_copy_word_no_unit_free_risk
    (encode : SourceWordMinimalCode.WordImage (runtimeAt 3)
      [SourceWordDynamicNext.copyOne] → Unit)
    (decoder : Unit → SourceJointClockGraph.Carrier) :
    0 < risk (runtimeAt 3) [SourceWordDynamicNext.copyOne] encode decoder := by
  apply deficit_positive
  rw [inventory_bound, runtimeAt_state]
  norm_num

end
end SourceWordCodeRisk
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
