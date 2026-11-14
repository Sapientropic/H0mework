import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Actor.Action
import SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import SaturationMonoid.GenericFoundation.Operations.Scalar.Complex

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyRawActionControls
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
namespace D
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Action
 (runtime rawSource raw_env action_raw_active increment_branch native_increment raw_inverse)
end D
namespace S
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
 (frameAt pointEnv actorClock birth F.Values F.Vars F.dynamicFeed C.continuous B.actual_action B.actual_next B.actual_compiles)
end S
namespace N
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
 (canonical recover complete_inverse C.mathRuntime)
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action
 (actualAction actualEffect actualAction_source)
end N
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
 (increment_actual character_source_read complete_source_word actual_source_receipt)
end O
abbrev oldEnv (depth count stage : Nat) := (S.frameAt depth count stage).rawRead.environment
abbrev delta (depth count stage : Nat) :=
 SourceOperationInquiry.Context.increment (D.runtime depth count) (D.rawSource depth count)
  ((D.runtime depth count).stateAt stage)
abbrev Words (depth count : Nat) := Formal ℤ (S.F.Values depth count) S.F.Vars true

theorem actual_source_action (depth count stage : Nat) : type_of% (D.action_raw_active depth count stage) :=
 D.action_raw_active depth count stage
theorem complete_image_inverse (depth count stage : Nat) : type_of% (D.raw_inverse depth count stage) :=
 D.raw_inverse depth count stage

theorem paid_zero (depth count stage : Nat)
 {paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law (S.frameAt depth count stage).registered.input.environment
   (S.frameAt depth count stage).registered.input.expression) (S.frameAt depth count stage).event.state}
 (actual : (S.frameAt depth count stage).action = .inr paid) : delta depth count stage = 0 := by
 dsimp only [delta]
 rw [D.increment_branch, actual]

theorem birth_effect (depth count ordinal : Nat) :
 (delta depth count (S.birth depth count ordinal)) false Unit.unit =
 N.actualEffect depth count (oldEnv depth count (S.birth depth count ordinal) false Unit.unit) := by
 dsimp only [delta, oldEnv]
 rw [D.native_increment, S.B.actual_action]

theorem native_effect_nonzero (depth count stage : Nat) :
 N.actualEffect depth count (oldEnv depth count stage false Unit.unit) ≠ 0 := by
 intro zero
 change N.actualAction depth count (oldEnv depth count stage false Unit.unit) -
  oldEnv depth count stage false Unit.unit = 0 at zero
 have same := sub_eq_zero.mp zero
 dsimp only [oldEnv] at same
 rw [D.raw_env] at same
 dsimp only [S.pointEnv] at same
 rw [N.actualAction_source] at same
 have full := congrArg (N.recover depth count) same
 rw [N.complete_inverse, N.complete_inverse, SourceOperationNative.sourceAction_point] at full
 let native := N.C.mathRuntime depth (S.actorClock depth count stage - 1)
 change Finsupp.single native.tick.next.state (1 : ℤ) = Finsupp.single native.state 1 at full
 have stateSame := Finsupp.single_left_injective (by decide : (1 : ℤ) ≠ 0) full
 have clockSame := congrArg ULift.down stateSame
 change native.state.down + 1 = native.state.down at clockSame
 omega

theorem paid_rejects_unconditional_effect (depth count stage : Nat)
 {paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law (S.frameAt depth count stage).registered.input.environment
   (S.frameAt depth count stage).registered.input.expression) (S.frameAt depth count stage).event.state}
 (actual : (S.frameAt depth count stage).action = .inr paid) :
 (delta depth count stage) false Unit.unit ≠
 N.actualEffect depth count (oldEnv depth count stage false Unit.unit) := by
 rw [paid_zero depth count stage actual]
 exact Ne.symm (native_effect_nonzero depth count stage)

theorem character_and_actual_delta (depth count offset bound : Nat) (word : Words depth count)
 (index : Fin (bound + 1)) :
 type_of% (O.character_source_read (S.F.dynamicFeed depth count) (S.C.continuous depth count) offset bound word index) ∧
 type_of% (D.increment_branch depth count (offset + index.val)) :=
 ⟨O.character_source_read (S.F.dynamicFeed depth count) (S.C.continuous depth count) offset bound word index,
  D.increment_branch depth count (offset + index.val)⟩

theorem original_full_fibre (depth count stage : Nat) : type_of%
 (O.complete_source_word (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage) :=
 O.complete_source_word (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage

theorem original_update_fibre (depth count stage : Nat)
 (left right : Formal ℤ (S.F.Values depth count) (ChangedVar S.F.Vars) true) : type_of%
 (SourceOperationScalarCochain.update_fibre_iff (R := ℤ) (oldEnv depth count stage) (delta depth count stage) left right) :=
 SourceOperationScalarCochain.update_fibre_iff (R := ℤ) (oldEnv depth count stage) (delta depth count stage) left right

theorem original_cochain (depth count stage : Nat)
 (word : ScalarRelationPresentation.PresentedCarrier ℤ
  ((SourceOperationScalarCochain.cochain (R := ℤ) (s := true) (oldEnv depth count stage) (delta depth count stage)).X 0)) : type_of%
 (SourceOperationScalarCochain.cochain_presented_comp_zero (R := ℤ) (oldEnv depth count stage) (delta depth count stage) word) :=
 SourceOperationScalarCochain.cochain_presented_comp_zero (R := ℤ) (oldEnv depth count stage) (delta depth count stage) word

theorem actual_root_receipt (depth count stage : Nat) : type_of%
 (O.actual_source_receipt (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage) :=
 O.actual_source_receipt (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage

theorem canonical_birth_next (depth count ordinal : Nat) : type_of%
 (S.B.actual_next (S.C.continuous depth count) (S.F.dynamicFeed depth count) ordinal) :=
 S.B.actual_next (S.C.continuous depth count) (S.F.dynamicFeed depth count) ordinal

theorem canonical_birth_compiles (depth count ordinal : Nat) : type_of%
 (S.B.actual_compiles (S.C.continuous depth count) (S.F.dynamicFeed depth count) ordinal) :=
 S.B.actual_compiles (S.C.continuous depth count) (S.F.dynamicFeed depth count) ordinal

#print axioms actual_source_action
#print axioms complete_image_inverse
#print axioms paid_zero
#print axioms birth_effect
#print axioms native_effect_nonzero
#print axioms paid_rejects_unconditional_effect
#print axioms character_and_actual_delta
#print axioms original_full_fibre
#print axioms original_update_fibre
#print axioms original_cochain
#print axioms actual_root_receipt
#print axioms canonical_birth_next
#print axioms canonical_birth_compiles
end SourcePolicyRawActionControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
