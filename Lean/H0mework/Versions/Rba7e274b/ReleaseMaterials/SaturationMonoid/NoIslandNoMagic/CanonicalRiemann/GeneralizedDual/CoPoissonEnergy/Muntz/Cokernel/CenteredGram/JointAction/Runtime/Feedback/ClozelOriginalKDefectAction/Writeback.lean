import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDefectAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
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

abbrev configuration (ordinal : Nat) := (defectPacket observation nontrivial half depth ordinal).2.2.1

def defectAdmission (ordinal : Nat) :=
  Admission.generatedAction (defectPacket observation nontrivial half depth ordinal).2.1.1
    (configuration observation nontrivial half depth ordinal)
    (AS.scalar (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
      (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
      (defectPacket observation nontrivial half depth ordinal).2.2.2.down)
    (AS.pair (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
      (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
      (defectPacket observation nontrivial half depth ordinal).2.2.2.down)
    (AS.nextCfg (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
      (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
      (defectPacket observation nontrivial half depth ordinal).2.2.2.down)

theorem actual_defect_compiles (ordinal : Nat) : type_of%
    (Admission.compiles (defectPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal)
      (AS.scalar (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
        (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (defectPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.pair (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
        (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (defectPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.nextCfg (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
        (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (defectPacket observation nontrivial half depth ordinal).2.2.2.down)) :=
  Admission.compiles _ _ _ _ _

theorem actual_defect_whole (ordinal : Nat) : type_of%
    (defectAdmission observation nontrivial half depth ordinal).target.firstDestination_heq :=
  (defectAdmission observation nontrivial half depth ordinal).target.firstDestination_heq

theorem actual_defect_next (ordinal : Nat) : type_of%
    (Admission.target_current (defectPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal)
      (AS.scalar (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
        (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (defectPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.pair (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
        (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (defectPacket observation nontrivial half depth ordinal).2.2.2.down)
      (AS.nextCfg (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
        (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (defectPacket observation nontrivial half depth ordinal).2.2.2.down)
      (Admission.sourceEvent (defectPacket observation nontrivial half depth ordinal).2.1.1
        (configuration observation nontrivial half depth ordinal))) :=
  Admission.target_current _ _ _ _ _ _

def actualWrite (ordinal : Nat) :=
  WB.oldPaid (defectPacket observation nontrivial half depth ordinal).2.1.1
    (configuration observation nontrivial half depth ordinal) +
  Native.nativeValue (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal)

def actualWriteRead (ordinal : Nat) : Branches :=
  CF.collapseValue (defectPacket observation nontrivial half depth ordinal).1
    (actualWrite observation nontrivial half depth ordinal)

theorem actual_defect_write (ordinal : Nat) :
    actualWrite observation nontrivial half depth ordinal =
      (material observation nontrivial half depth ordinal).raw.eval
        (material observation nontrivial half depth ordinal).environment +
      (material observation nontrivial half depth ordinal).raw.effect
        (material observation nontrivial half depth ordinal).environment
        (material observation nontrivial half depth ordinal).increment :=
  (Dyn.updated_total (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
    (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
    (defectPacket observation nontrivial half depth ordinal).2.2.2.down).trans
    (Expr.eval_update (material observation nontrivial half depth ordinal).raw _ _)

private theorem actual_material_value (ordinal : Nat) :
    (material observation nontrivial half depth ordinal).raw.eval
      (material observation nontrivial half depth ordinal).environment =
      (receipt observation nontrivial half depth ordinal).2.2.1 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Root.baseRoot (defectPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal)).toAuthoritativeRoot
    (R.actionReader (defectPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal))
    (Root.actualOccurrence (defectPacket observation nontrivial half depth ordinal).2.1.1)).symm

theorem actual_defect_write_read (ordinal : Nat) :
    actualWriteRead observation nontrivial half depth ordinal =
      actualValue observation nontrivial half depth ordinal + actualEffect observation nontrivial half depth ordinal := by
  unfold actualWriteRead
  rw [actual_defect_write, Coll.collapse_add, actual_material_value, actual_defect_source_value, actual_complete_source_effect]

theorem actual_defect_born_environment (ordinal : Nat) :
    (Native.sourceBorn (defectFactory observation nontrivial half)
      (defectPacket observation nontrivial half depth ordinal)).2.1.1.activeEnvironment =
      AS.write (defectFactory observation nontrivial half) (defectPacket observation nontrivial half depth ordinal).1
        (defectPacket observation nontrivial half depth ordinal).2.1 (configuration observation nontrivial half depth ordinal)
        (defectPacket observation nontrivial half depth ordinal).2.2.2.down
        (actualWrite observation nontrivial half depth ordinal) :=
  Native.born_environment (defectFactory observation nontrivial half) _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
