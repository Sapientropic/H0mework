import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (scalar pair nextCfg write)
end AS
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid)
end WB
namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
  (compiles generatedAction sourceEvent target_current)
end Admission
namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
  (updated_total)
end Dyn
namespace Coll
export OriginalKFiniteWard (collapse_add collapse_sub)
end Coll
local instance writebackGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def returnAdmission (ordinal : Nat) :=
  Admission.generatedAction (returnPacket observation nontrivial half depth ordinal).2.1.1
    (configuration observation nontrivial half depth ordinal)
    (AS.scalar (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
      (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
      (returnPacket observation nontrivial half depth ordinal).2.2.2.down)
    (AS.pair (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
      (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
      (returnPacket observation nontrivial half depth ordinal).2.2.2.down)
    (AS.nextCfg (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
      (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
      (returnPacket observation nontrivial half depth ordinal).2.2.2.down)

theorem actual_return_compiles (ordinal : Nat) : type_of%
    (Admission.compiles (returnPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal)
      (AS.scalar (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
        (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (returnPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.pair (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
        (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (returnPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.nextCfg (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
        (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (returnPacket observation nontrivial half depth ordinal).2.2.2.down)) :=
  Admission.compiles _ _ _ _ _

theorem actual_return_whole (ordinal : Nat) : type_of%
    (returnAdmission observation nontrivial half depth ordinal).target.firstDestination_heq :=
  (returnAdmission observation nontrivial half depth ordinal).target.firstDestination_heq

theorem actual_return_next (ordinal : Nat) : type_of%
    (Admission.target_current (returnPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal)
      (AS.scalar (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
        (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (returnPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.pair (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
        (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (returnPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.nextCfg (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
        (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (returnPacket observation nontrivial half depth ordinal).2.2.2.down)
      (Admission.sourceEvent (returnPacket observation nontrivial half depth ordinal).2.1.1
        (configuration observation nontrivial half depth ordinal))) :=
  Admission.target_current _ _ _ _ _ _

def actualReturnWrite (ordinal : Nat) :=
  WB.oldPaid (returnPacket observation nontrivial half depth ordinal).2.1.1
    (configuration observation nontrivial half depth ordinal) +
  Native.nativeValue (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal)

def actualReturnWriteRead (ordinal : Nat) : Branches :=
  CF.collapseValue (returnPacket observation nontrivial half depth ordinal).1
    (actualReturnWrite observation nontrivial half depth ordinal)

theorem actual_return_write (ordinal : Nat) :
    actualReturnWrite observation nontrivial half depth ordinal =
      (material observation nontrivial half depth ordinal).raw.eval
        (material observation nontrivial half depth ordinal).environment +
      (material observation nontrivial half depth ordinal).raw.effect
        (material observation nontrivial half depth ordinal).environment
        (material observation nontrivial half depth ordinal).increment :=
  (Dyn.updated_total (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
    (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
    (returnPacket observation nontrivial half depth ordinal).2.2.2.down).trans
    (Expr.eval_update (material observation nontrivial half depth ordinal).raw _ _)

private theorem actual_material_value (ordinal : Nat) :
    (material observation nontrivial half depth ordinal).raw.eval
      (material observation nontrivial half depth ordinal).environment =
      (receipt observation nontrivial half depth ordinal).2.2.1 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot (returnPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal)).toAuthoritativeRoot
    (R.actionReader (returnPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal))
    (S.actualOccurrence (returnPacket observation nontrivial half depth ordinal).2.1.1)).symm

theorem actual_return_write_read (ordinal : Nat) :
    actualReturnWriteRead observation nontrivial half depth ordinal =
      actualReturnValue observation nontrivial half + actualReturnEffect observation nontrivial half depth ordinal := by
  unfold actualReturnWriteRead
  rw [actual_return_write, Coll.collapse_add, actual_material_value, actual_complete_source_value, actual_complete_source_effect]

theorem actual_return_born_environment (ordinal : Nat) :
    (Native.sourceBorn (returnFactory observation nontrivial half)
      (returnPacket observation nontrivial half depth ordinal)).2.1.1.activeEnvironment =
      AS.write (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal).1
        (returnPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (returnPacket observation nontrivial half depth ordinal).2.2.2.down
        (actualReturnWrite observation nontrivial half depth ordinal) :=
  Native.born_environment (returnFactory observation nontrivial half) _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
