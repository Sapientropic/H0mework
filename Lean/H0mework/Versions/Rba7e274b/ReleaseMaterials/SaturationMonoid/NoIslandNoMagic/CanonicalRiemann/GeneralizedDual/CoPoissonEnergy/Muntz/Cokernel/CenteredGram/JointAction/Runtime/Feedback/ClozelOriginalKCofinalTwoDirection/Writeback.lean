import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalTwoDirection.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn)
end S
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (scalar pair nextCfg nativeAfterAdmission_grade)
end AS
namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
  (compiles generatedAction sourceEvent target_current target_root)
end Admission

local instance consumerGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
  (updated_total actual_writeback write_all)
end Dyn

private theorem native_updated_total
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
    WB.oldPaid packet.2.1.1 packet.2.2.1 + Native.nativeValue factory packet =
      (R.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
        (N.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment :=
  Dyn.updated_total factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down

private def generated_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :=
  Admission.generatedAction packet.2.1.1 packet.2.2.1
    (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
    (AS.pair factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
    (AS.nextCfg factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)

private theorem compiles_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (Admission.compiles packet.2.1.1 packet.2.2.1
      (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
      (AS.pair factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
      (AS.nextCfg factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) :=
  Admission.compiles packet.2.1.1 packet.2.2.1
    (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
    (AS.pair factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
    (AS.nextCfg factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)

private theorem whole_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (generated_at factory packet).target.firstDestination_heq :=
  (generated_at factory packet).target.firstDestination_heq

private theorem next_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (Admission.target_current packet.2.1.1 packet.2.2.1
      (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
      (AS.pair factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
      (AS.nextCfg factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)
      (Admission.sourceEvent packet.2.1.1 packet.2.2.1)) :=
  Admission.target_current _ _ _ _ _ _

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem parent_compiles (ordinal : Nat) : type_of%
    (compiles_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)) :=
  compiles_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)
theorem parent_whole (ordinal : Nat) : type_of%
    (whole_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)) :=
  whole_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)
theorem parent_next (ordinal : Nat) : type_of%
    (next_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)) :=
  next_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)
theorem action_compiles (ordinal : Nat) : type_of%
    (compiles_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  compiles_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)
theorem action_whole (ordinal : Nat) : type_of%
    (whole_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  whole_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)
theorem action_next (ordinal : Nat) : type_of%
    (next_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  next_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)

theorem actual_action_write (ordinal : Nat) :
    WB.oldPaid (actionPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal) +
      Native.nativeValue (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal) =
    (material observation nontrivial half depth ordinal).raw.eval
      (material observation nontrivial half depth ordinal).environment +
    (material observation nontrivial half depth ordinal).raw.effect
      (material observation nontrivial half depth ordinal).environment
      (material observation nontrivial half depth ordinal).increment :=
  (native_updated_total (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)).trans
    (Expr.eval_update (material observation nontrivial half depth ordinal).raw
      (material observation nontrivial half depth ordinal).environment
      (material observation nontrivial half depth ordinal).increment)

theorem actual_action_born_environment (ordinal : Nat) :
    (Native.sourceBorn (factory observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal)).2.1.1.activeEnvironment =
    AS.write (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal).1
      (actionPacket observation nontrivial half depth ordinal).2.1
      (configuration observation nontrivial half depth ordinal)
      (actionPacket observation nontrivial half depth ordinal).2.2.2.down
      ((material observation nontrivial half depth ordinal).raw.eval
        (N.input (material observation nontrivial half depth ordinal)).environment) :=
  (Native.born_environment (factory observation nontrivial half) _).trans
    (congrArg (AS.write (factory observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal).1
      (actionPacket observation nontrivial half depth ordinal).2.1
      (configuration observation nontrivial half depth ordinal)
      (actionPacket observation nontrivial half depth ordinal).2.2.2.down)
      (native_updated_total (factory observation nontrivial half) _))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
