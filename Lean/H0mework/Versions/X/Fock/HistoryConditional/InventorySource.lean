import H0mework.Versions.X.Fock.HistoryConditional.VectorMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def values (bound : Nat) (index : Fin (bound + 1)) : SourceJointClockGraph.Carrier :=
  SourceCopyNativeModelStep.sourceValue ((history runtimeSeed bound).stageAt index).next

theorem values_retained (bound : Nat) (index : Fin (bound + 1)) :
    values (bound + 1) index.castSucc = values bound index := rfl

theorem material_retained (bound : Nat) (index : Fin (bound + 1)) :
    HEq ((history runtimeSeed (bound + 1)).stageAt index.castSucc) ((history runtimeSeed bound).stageAt index) := by
  rfl

def born (bound : Nat) : SourceJointClockGraph.Carrier := values (bound + 1) (Fin.last (bound + 1))

theorem born_material (bound : Nat) : born bound = SourceCopyNativeModelStep.sourceValue (runtimeAt (bound + 1)).tick.next := rfl

theorem values_original (runtime : LivingRuntimeState process) (index : SourceConditionalModel.Actors runtime) :
    values (inventoryBound runtime) index = SourceConditionalVector.realizeModel runtime (SourceConditionalModel.nextRead runtime index) :=
  ((SourceConditionalVector.realized_next runtime index).trans (SourceConditionalVector.actor_material runtime index)).symm

def observation (bound depth : Nat) : Fin (bound + 1) → Field parity :=
  SourceConditionalTransfer.fieldSample parity (runtimeSeed.advance (depth + 1)) bound

theorem observation_retained (bound depth : Nat) (index : Fin (bound + 1)) :
    observation (bound + 1) depth index.castSucc = observation bound depth index := rfl

theorem observation_original (runtime : LivingRuntimeState process) (depth : Nat) :
    observation (inventoryBound runtime) depth = SourceConditionalModel.dynamicRead runtime depth := rfl

theorem mean_count {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (bound : Nat) (value : Fin (bound + 1) → E) :
    ((bound + 1 : Nat) : ℂ) • SourceVectorMoment.mean (historyPMF bound) value = ∑ i, value i := by
  have nonzero : (bound : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero bound
  simp only [SourceVectorMoment.mean, Finset.smul_sum, smul_smul, historyPMF_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [mul_inv_cancel₀ nonzero, one_smul]

theorem mean_append (bound : Nat) :
    ((bound + 2 : Nat) : ℂ) • SourceVectorMoment.mean (historyPMF (bound + 1)) (values (bound + 1)) =
      ((bound + 1 : Nat) : ℂ) • SourceVectorMoment.mean (historyPMF bound) (values bound) + born bound := by
  change ((bound + 1 + 1 : Nat) : ℂ) • SourceVectorMoment.mean (historyPMF (bound + 1)) (values (bound + 1)) = _
  rw [mean_count, mean_count, Fin.sum_univ_castSucc]
  simp only [values_retained, born]

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
