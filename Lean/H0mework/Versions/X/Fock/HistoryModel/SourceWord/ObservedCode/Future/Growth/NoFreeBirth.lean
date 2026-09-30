import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.FixedErasure

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBitGrowth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- The old letter keeps the material action that generated it, even after a tick
    enlarges the legal inventory. -/
theorem carried_fresh_query (depth : Nat)
    (actor : Actors (runtimeAt (depth + 1))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
      (nextWordAt depth
        [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))]) actor =
      SourceWordObservedCode.readAt depth [] actor.val *
        SourceWordObservedCode.observe
          ((runtimeAt depth).tick.next.current.visit.current : Current) := by
  calc
    _ = SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth + 1)))
          (nextWordAt depth
            [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))])
          actor.val := SourceWordObservedCode.source_query_read _ _ _
    _ = SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
          (oldWordAt depth
            [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))])
          actor.val := old_next_read_at depth _ _
    _ = SourceWordObservedCode.readAt depth
          [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))]
          actor.val := transport_read_at _ _ _
    _ = _ := SourceWordFreshReceiver.fresh_read_all depth actor.val

def carriedAtThree :
    List (Fock.Letter (inventoryBound (runtimeAt 3) + 1)) :=
  nextWordAt 2 [(.inr (FamilyModel.Fock.newestIndex 2) : Fock.Letter 3)]

theorem carriedAtThree_erased (actor : Actors (runtimeAt 3)) :
    SourceWordObservedCode.sourceQuery (runtimeAt 3) carriedAtThree actor = 0 := by
  have action := carried_fresh_query 2 actor
  rw [SourceWordFreshReceiver.fresh_material_bit] at action
  have evenBit : ((2 + 2 : Nat) : ZMod 2) = 0 := by decide
  rw [evenBit, mul_zero] at action
  exact action

theorem freshAtThree_separates :
    SourceWordObservedCode.sourceQuery (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      (⟨0, by decide⟩ : Actors (runtimeAt 3)) ≠
    SourceWordObservedCode.sourceQuery (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      (⟨1, by decide⟩ : Actors (runtimeAt 3)) := by
  rw [SourceWordFreshReceiver.retained_at_three,
    SourceWordFreshReceiver.retained_at_three]
  decide

theorem fresh_bit_recovers_future (actor : Actors (runtimeAt 3)) :
    (fun tail => SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 3) + 1) tail
      (SourceWordObservedCode.sourceQuery (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3) actor)) =
      SourceWordFutureBit.futureRead (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3) actor :=
  (SourceWordFutureBit.future_read_bit _ _ _).symm

/-- The old future-tail code is one-valued at the generated next inventory,
    while the genuinely new material letter separates the same two actors. -/
theorem carried_future_cannot_recover_fresh
    (decode : (List (Fock.Letter (inventoryBound (runtimeAt 3) + 1)) → ZMod 2) →
      (List (Fock.Letter (inventoryBound (runtimeAt 3) + 1)) → ZMod 2)) :
    ¬ ∀ actor : Actors (runtimeAt 3),
      decode (SourceWordFutureBit.futureRead (runtimeAt 3) carriedAtThree actor) =
        SourceWordFutureBit.futureRead (runtimeAt 3)
          (SourceWordFreshReceiver.freshWord 3) actor := by
  intro recovers
  let left : Actors (runtimeAt 3) := ⟨0, by decide⟩
  let right : Actors (runtimeAt 3) := ⟨1, by decide⟩
  have oldSame : SourceWordFutureBit.futureRead (runtimeAt 3) carriedAtThree left =
      SourceWordFutureBit.futureRead (runtimeAt 3) carriedAtThree right :=
    (SourceWordFutureBit.future_kernel _ _ _ _).mpr
      ((carriedAtThree_erased left).trans (carriedAtThree_erased right).symm)
  have newSame : SourceWordFutureBit.futureRead (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3) left =
      SourceWordFutureBit.futureRead (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3) right :=
    (recovers left).symm.trans ((congrArg decode oldSame).trans (recovers right))
  exact freshAtThree_separates
    ((SourceWordFutureBit.future_kernel _ _ _ _).mp newSame)

/-- Encode the new acted G task using only the old letter's transported bit. -/
def carriedCode :
    SourceWordMinimalCode.WordImage (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) → ZMod 2 :=
  fun code => SourceWordObservedCode.sourceQuery (runtimeAt 3) carriedAtThree
    ((SourceWordMinimalCode.wordEquiv (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)).symm code)

theorem carriedCode_query (actor : Actors (runtimeAt 3)) :
    SourceWordCodeRisk.query (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) carriedCode actor = 0 := by
  simpa only [SourceWordCodeRisk.query, carriedCode, Equiv.symm_apply_apply]
    using carriedAtThree_erased actor

/-- The original source-weighted physical G consumer charges a strict price to
    recovering its fresh task from the old, erased future-tail code. -/
theorem carriedCode_original_G_risk (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    (3 / 4 : ℝ) ≤ SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) carriedCode decoder := by
  have queryConst : SourceWordCodeRisk.query (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) carriedCode =
      (fun _ => (0 : ZMod 2)) := by
    funext actor
    exact carriedCode_query actor
  have cost : SourceConditionalInventory.cost (inventoryBound (runtimeAt 3))
      (SourceWordCodeRisk.query (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3) carriedCode) = 3 := by
    rw [queryConst, SourceConditionalInventory.cost_eq]
    have outputSingleton : SourceUniformFibreVariance.outputs
        (inventoryBound (runtimeAt 3))
        (fun _ : Actors (runtimeAt 3) => (0 : ZMod 2)) = {0} := by
      ext bit
      simp only [SourceUniformFibreVariance.outputs, Finset.mem_image,
        Finset.mem_singleton]
      constructor
      · rintro ⟨actor, _, rfl⟩
        rfl
      · intro same
        subst bit
        exact ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, rfl⟩
    rw [outputSingleton, Finset.card_singleton, inventory_bound, runtimeAt_state]
    norm_num
  have info := SourceWordCodeRisk.information_lower (runtimeAt 3)
    (SourceWordFreshReceiver.freshWord 3) carriedCode decoder
  have entropy := SourceWordCodeRisk.entropy_nonnegative (runtimeAt 3)
    (SourceWordFreshReceiver.freshWord 3) carriedCode
  have expNonnegative : 0 ≤
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
        (inventoryBound (runtimeAt 3))
        (SourceWordCodeRisk.query (runtimeAt 3)
          (SourceWordFreshReceiver.freshWord 3) carriedCode)) - 1) / 12 := by
    have e := Real.add_one_le_exp (2 * SourceUniformFibreInformation.conditionalEntropy
      (inventoryBound (runtimeAt 3))
      (SourceWordCodeRisk.query (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3) carriedCode))
    nlinarith
  have slopeNonnegative : 0 ≤
      ((SourceCopyWordAffine.compile ((SourceWordFreshReceiver.freshWord 3).map
        SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 := sq_nonneg _
  rw [cost] at info
  have sourceSize : (inventoryBound (runtimeAt 3) + 1 : ℝ) = 4 := by
    rw [inventory_bound, runtimeAt_state]
    norm_num
  rw [sourceSize] at info
  nlinarith [mul_nonneg slopeNonnegative expNonnegative]

private theorem fresh_zero_supported :
    (0 : ZMod 2) ∈ ((historyPMF (inventoryBound (runtimeAt 3))).map
      (fun actor : Actors (runtimeAt 3) =>
        SourceWordObservedCode.readAt 3 [] actor.val *
          SourceWordObservedCode.observe
            ((runtimeAt 3).tick.next.current.visit.current : Current))).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨⟨0, by decide⟩, SourceUniformFibreVariance.source_positive _ _, ?_⟩
  rw [SourceWordFreshReceiver.fresh_material_bit]
  decide

/-- At the canonical d2→d3 successor, the newly legal letter's counted
    posterior and original G risk share d3's ledger and generated next. -/
theorem generated_next_consumes_carried_risk
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 3)
    runtimeAt 3 = (runtimeAt 2).tick.next ∧
    SourcePosteriorReadback.readWeight (runtimeAt 3)
      (SourceCountedPosterior.model (runtimeAt 3)
        (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 3) (nextNonunit 2) 0)
        (SourceWordObservedCode.table (runtimeAt 3) (nextNonunit 2)
          (SourceWordFreshReceiver.freshWord 3) 0) 0) =
      (fun actor => SourceConditionalHistory.conditional
        (historyPMF (inventoryBound (runtimeAt 3)))
        (fun index : Actors (runtimeAt 3) =>
          SourceWordObservedCode.readAt 3 [] index.val *
            SourceWordObservedCode.observe
              ((runtimeAt 3).tick.next.current.visit.current : Current))
        0 fresh_zero_supported actor) ∧
    HEq stage.wholeLedgerWriteBack
      ((runtimeAt 3).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt 3).current.visit.current) ∧
    stage.next.current = stage.activated.nextCurrent ∧
    (3 / 4 : ℝ) ≤ SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) carriedCode decoder := by
  dsimp only
  exact ⟨(next_runtime 2).symm,
    SourceWordFreshReceiver.fresh_complete_posterior 3 (nextNonunit 2) 0
      fresh_zero_supported,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 3)).factorizes.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 3)).factorizes.2.2.2,
    carriedCode_original_G_risk decoder⟩

end
end SourceWordFutureBitGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
