import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.NoFreeBirth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordEvenBirth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

def oldWord (depth : Nat) :
    List (Fock.Letter (inventoryBound (runtimeAt (depth + 1)) + 1)) :=
  SourceWordFutureBitGrowth.nextWordAt depth
    [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))]

def newWord (depth : Nat) :
    List (Fock.Letter (inventoryBound (runtimeAt (depth + 1)) + 1)) :=
  SourceWordFreshReceiver.freshWord (depth + 1)

theorem even_cast_zero (depth : Nat) (even : Even depth) :
    ((depth + 2 : Nat) : ZMod 2) = 0 := by
  rcases even with ⟨half, rfl⟩
  have two : (2 : ZMod 2) = 0 := by decide
  calc
    _ = (2 : ZMod 2) * (half : ZMod 2) + 2 := by push_cast; ring
    _ = 0 := by rw [two]; simp

theorem odd_next_cast_one (depth : Nat) (even : Even depth) :
    ((depth + 3 : Nat) : ZMod 2) = 1 := by
  rcases even with ⟨half, rfl⟩
  have two : (2 : ZMod 2) = 0 := by decide
  calc
    _ = (2 : ZMod 2) * (half : ZMod 2) + 3 := by push_cast; ring
    _ = 1 := by rw [two]; simp only [zero_mul, zero_add]; decide

theorem old_query_zero (depth : Nat) (even : Even depth)
    (actor : Actors (runtimeAt (depth + 1))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
      (oldWord depth) actor = 0 := by
  have action := SourceWordFutureBitGrowth.carried_fresh_query depth actor
  rw [SourceWordFreshReceiver.fresh_material_bit, even_cast_zero depth even,
    mul_zero] at action
  exact action

theorem new_query_native (depth : Nat) (even : Even depth)
    (actor : Actors (runtimeAt (depth + 1))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
      (newWord depth) actor =
      SourceWordObservedCode.readAt (depth + 1) [] actor.val := by
  rw [newWord, SourceWordFreshReceiver.fresh_query_all,
    SourceWordFreshReceiver.fresh_material_bit, odd_next_cast_one depth even,
    mul_one]

theorem old_new_material_distinct (depth : Nat) :
    ((runtimeAt depth).tick.next.current.visit.current : Current) ≠
      ((runtimeAt (depth + 1)).tick.next.current.visit.current : Current) := by
  change ((runtimeAt (depth + 1)).current.visit.current : Current) ≠
    ((runtimeAt (depth + 2)).current.visit.current : Current)
  intro same
  have scans := congrArg scanIndex same
  rw [runtimeAt_scanIndex, runtimeAt_scanIndex] at scans
  omega

def actorZero (depth : Nat) : Actors (runtimeAt (depth + 1)) :=
  ⟨0, by rw [inventory_bound, runtimeAt_state]; omega⟩

def actorOne (depth : Nat) : Actors (runtimeAt (depth + 1)) :=
  ⟨1, by rw [inventory_bound, runtimeAt_state]; omega⟩

theorem new_query_separates (depth : Nat) (even : Even depth) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
        (newWord depth) (actorZero depth) ≠
      SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
        (newWord depth) (actorOne depth) := by
  rw [new_query_native depth even, new_query_native depth even]
  change SourceWordObservedCode.observe
      (nativeStep ((runtimeAt 0).current.visit.current : Current)) ≠
    SourceWordObservedCode.observe
      (nativeStep ((runtimeAt 1).current.visit.current : Current))
  decide

theorem old_future_same (depth : Nat) (even : Even depth)
    (left right : Actors (runtimeAt (depth + 1))) :
    SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
      (oldWord depth) left =
    SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
      (oldWord depth) right :=
  (SourceWordFutureBit.future_kernel _ _ _ _).mpr
    ((old_query_zero depth even left).trans (old_query_zero depth even right).symm)

theorem new_future_separates (depth : Nat) (even : Even depth) :
    SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (newWord depth) (actorZero depth) ≠
      SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (newWord depth) (actorOne depth) := by
  intro same
  exact new_query_separates depth even
    ((SourceWordFutureBit.future_kernel _ _ _ _).mp same)

abbrev FutureResponse (depth : Nat) :=
  List (Fock.Letter (inventoryBound (runtimeAt (depth + 1)) + 1)) → ZMod 2

theorem old_future_cannot_recover_new (depth : Nat) (even : Even depth)
    (decode : FutureResponse depth → FutureResponse depth) :
    ¬ ∀ actor : Actors (runtimeAt (depth + 1)),
      decode (SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (oldWord depth) actor) =
      SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (newWord depth) actor := by
  intro recovers
  exact new_future_separates depth even
    ((recovers (actorZero depth)).symm.trans
      ((congrArg decode (old_future_same depth even (actorZero depth) (actorOne depth))).trans
        (recovers (actorOne depth))))

def oldCode (depth : Nat) :
    SourceWordMinimalCode.WordImage (runtimeAt (depth + 1)) (newWord depth) → ZMod 2 :=
  fun code => SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
    (oldWord depth)
    ((SourceWordMinimalCode.wordEquiv (runtimeAt (depth + 1))
      (newWord depth)).symm code)

theorem oldCode_query_zero (depth : Nat) (even : Even depth)
    (actor : Actors (runtimeAt (depth + 1))) :
    SourceWordCodeRisk.query (runtimeAt (depth + 1)) (newWord depth)
      (oldCode depth) actor = 0 := by
  simpa only [SourceWordCodeRisk.query, oldCode, Equiv.symm_apply_apply]
    using old_query_zero depth even actor

theorem oldCode_cost (depth : Nat) (even : Even depth) :
    SourceConditionalInventory.cost (inventoryBound (runtimeAt (depth + 1)))
      (SourceWordCodeRisk.query (runtimeAt (depth + 1))
        (newWord depth) (oldCode depth)) = depth + 1 := by
  have queryConst : SourceWordCodeRisk.query (runtimeAt (depth + 1))
      (newWord depth) (oldCode depth) = fun _ => (0 : ZMod 2) := by
    funext actor
    exact oldCode_query_zero depth even actor
  rw [queryConst, SourceConditionalInventory.cost_eq]
  have outputSingleton : SourceUniformFibreVariance.outputs
      (inventoryBound (runtimeAt (depth + 1)))
      (fun _ : Actors (runtimeAt (depth + 1)) => (0 : ZMod 2)) = {0} := by
    ext bit
    simp only [SourceUniformFibreVariance.outputs, Finset.mem_image,
      Finset.mem_singleton]
    constructor
    · rintro ⟨actor, _, rfl⟩
      rfl
    · intro same
      subst bit
      exact ⟨actorZero depth, Finset.mem_univ _, rfl⟩
  rw [outputSingleton, Finset.card_singleton, inventory_bound, runtimeAt_state]
  push_cast
  ring

theorem oldCode_original_G_risk (depth : Nat) (even : Even depth)
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    ((depth + 1 : Nat) : ℝ) / ((depth + 2 : Nat) : ℝ) ≤
      SourceWordCodeRisk.risk (runtimeAt (depth + 1)) (newWord depth)
        (oldCode depth) decoder := by
  have info := SourceWordCodeRisk.information_lower (runtimeAt (depth + 1))
    (newWord depth) (oldCode depth) decoder
  rw [oldCode_cost depth even] at info
  have denominator : (inventoryBound (runtimeAt (depth + 1)) : ℝ) + 1 =
      ((depth + 2 : Nat) : ℝ) := by
    rw [inventory_bound, runtimeAt_state]
    push_cast
    ring
  rw [denominator] at info
  have entropy := SourceWordCodeRisk.entropy_nonnegative (runtimeAt (depth + 1))
    (newWord depth) (oldCode depth)
  have expNonnegative : 0 ≤
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
        (inventoryBound (runtimeAt (depth + 1)))
        (SourceWordCodeRisk.query (runtimeAt (depth + 1))
          (newWord depth) (oldCode depth))) - 1) / 12 := by
    have e := Real.add_one_le_exp (2 * SourceUniformFibreInformation.conditionalEntropy
      (inventoryBound (runtimeAt (depth + 1)))
      (SourceWordCodeRisk.query (runtimeAt (depth + 1))
        (newWord depth) (oldCode depth)))
    nlinarith
  have slopeNonnegative : 0 ≤
      ((SourceCopyWordAffine.compile ((newWord depth).map
        SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 := sq_nonneg _
  norm_num only [Nat.cast_add, Nat.cast_one] at info ⊢
  exact (le_add_of_nonneg_right (mul_nonneg slopeNonnegative expNonnegative)).trans info

theorem even_two_control :
    SourceWordObservedCode.sourceQuery (runtimeAt 3) (oldWord 2)
        (actorOne 2) = 0 ∧
      SourceWordObservedCode.sourceQuery (runtimeAt 3) (newWord 2)
          (actorZero 2) ≠
        SourceWordObservedCode.sourceQuery (runtimeAt 3) (newWord 2)
          (actorOne 2) := by
  exact ⟨old_query_zero 2 (by decide) _, new_query_separates 2 (by decide)⟩

theorem odd_three_not_erased :
    SourceWordObservedCode.sourceQuery (runtimeAt 4) (oldWord 3)
      (actorOne 3) ≠ 0 := by
  have action := SourceWordFutureBitGrowth.carried_fresh_query 3 (actorOne 3)
  have material : SourceWordObservedCode.observe
      ((runtimeAt 3).tick.next.current.visit.current : Current) = 1 := by
    rw [SourceWordFreshReceiver.fresh_material_bit]
    decide
  rw [material, mul_one] at action
  have oldEq : SourceWordObservedCode.sourceQuery (runtimeAt 4) (oldWord 3)
      (actorOne 3) = SourceWordObservedCode.readAt 3 [] (actorOne 3).val := by
    simpa only [oldWord] using action
  rw [oldEq]
  change SourceWordObservedCode.observe
      (nativeStep ((runtimeAt 1).current.visit.current : Current)) ≠ 0
  decide

end
end SourceWordEvenBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
