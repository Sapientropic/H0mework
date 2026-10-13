import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
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
namespace Native
export OriginalKDefectAction.Native (nativeValue sourceBorn born_environment)
end Native
namespace Coll
export OriginalKFiniteWard (collapse_add collapse_sub)
end Coll
namespace SF
export OriginalKFiniteWard.SF (Factory)
end SF
local instance writebackGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

private def writeAt
    (producer : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
    PairValue (L.Value (PairValue C.Value) packet.1) () :=
  WB.oldPaid packet.2.1.1 packet.2.2.1 + Native.nativeValue producer packet

private theorem write_at_source
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
 writeAt producer packet = (R.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
  (N.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment :=
 Dyn.updated_total producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down

private theorem write_at_born
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
 (Native.sourceBorn producer packet).2.1.1.activeEnvironment =
  AS.write producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (writeAt producer packet) :=
 Native.born_environment producer packet

attribute [irreducible] writeAt

private def writeReadAt
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : Branches :=
 CF.collapseValue packet.1 (writeAt producer packet)

private theorem write_read_at
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
 writeReadAt producer packet =
 CF.collapseValue packet.1 (R.actionResultAt packet.2.1.1 packet.2.2.1 (Root.actualOccurrence packet.2.1.1)).2.2.1 +
 CF.collapseValue packet.1 ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.effect
  (R.actualMaterial packet.2.1.1 packet.2.2.1).environment (R.actualMaterial packet.2.1.1 packet.2.2.1).increment) := by
 have source : (R.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
  (R.actualMaterial packet.2.1.1 packet.2.2.1).environment =
  (R.actionResultAt packet.2.1.1 packet.2.2.1 (Root.actualOccurrence packet.2.1.1)).2.2.1 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
   (Root.baseRoot packet.2.1.1 packet.2.2.1).toAuthoritativeRoot (R.actionReader packet.2.1.1 packet.2.2.1)
   (Root.actualOccurrence packet.2.1.1)).symm
 have update := Expr.eval_update (R.actualMaterial packet.2.1.1 packet.2.2.1).raw
  (R.actualMaterial packet.2.1.1 packet.2.2.1).environment (R.actualMaterial packet.2.1.1 packet.2.2.1).increment
 have total := (write_at_source producer packet).trans update
 have collapsed := (congrArg (CF.collapseValue packet.1) total).trans
  (Coll.collapse_add packet.1 _ _)
 exact collapsed.trans (congrArg (fun old => old + CF.collapseValue packet.1
  ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.effect
   (R.actualMaterial packet.2.1.1 packet.2.2.1).environment (R.actualMaterial packet.2.1.1 packet.2.2.1).increment))
  (congrArg (CF.collapseValue packet.1) source))

attribute [irreducible] writeReadAt

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h : ℝ)


def admission :=
  Admission.generatedAction (actionPacket observation nontrivial half depth ordinal h).2.1.1
    (configuration observation nontrivial half depth ordinal h)
    (AS.scalar (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
      (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
      (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)
    (AS.pair (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
      (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
      (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)
    (AS.nextCfg (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
      (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
      (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)

theorem actual_orbit_compiles : type_of%
    (Admission.compiles (actionPacket observation nontrivial half depth ordinal h).2.1.1
      (configuration observation nontrivial half depth ordinal h)
      (AS.scalar (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
        (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
        (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)
      (AS.pair (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
        (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
        (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)
      (AS.nextCfg (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
        (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
        (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)) :=
  Admission.compiles _ _ _ _ _

theorem actual_orbit_whole : type_of%
    (admission observation nontrivial half depth ordinal h).target.firstDestination_heq :=
  (admission observation nontrivial half depth ordinal h).target.firstDestination_heq

theorem actual_orbit_next : type_of%
    (Admission.target_current (actionPacket observation nontrivial half depth ordinal h).2.1.1
      (configuration observation nontrivial half depth ordinal h)
      (AS.scalar (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
        (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
        (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)
      (AS.pair (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
        (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
        (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)
      (AS.nextCfg (factory observation nontrivial half depth ordinal h) (actionPacket observation nontrivial half depth ordinal h).1
        (actionPacket observation nontrivial half depth ordinal h).2.1 (configuration observation nontrivial half depth ordinal h)
        (actionPacket observation nontrivial half depth ordinal h).2.2.2.down)
      (Admission.sourceEvent (actionPacket observation nontrivial half depth ordinal h).2.1.1
        (configuration observation nontrivial half depth ordinal h))) :=
  Admission.target_current _ _ _ _ _ _

def actualValue : Branches :=
  sourceFields ((pairedAction h - ContinuousLinearMap.id ℂ BurnolPhysicalState.BurnolL2)
   (Source.value (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)))

def actualWriteRead : Branches :=
 writeReadAt (factory observation nontrivial half depth ordinal h)
  (actionPacket observation nontrivial half depth ordinal h)

theorem actual_orbit_write : type_of% (write_at_source
 (factory observation nontrivial half depth ordinal h)
 (actionPacket observation nontrivial half depth ordinal h)) :=
 write_at_source _ _

private theorem actual_material_value :
    (material observation nontrivial half depth ordinal h).raw.eval
      (material observation nontrivial half depth ordinal h).environment =
      (receipt observation nontrivial half depth ordinal h).2.2.1 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Root.baseRoot (actionPacket observation nontrivial half depth ordinal h).2.1.1
      (configuration observation nontrivial half depth ordinal h)).toAuthoritativeRoot
    (R.actionReader (actionPacket observation nontrivial half depth ordinal h).2.1.1
      (configuration observation nontrivial half depth ordinal h))
    (Root.actualOccurrence (actionPacket observation nontrivial half depth ordinal h).2.1.1)).symm

def actualPaidSourceTrace : Trace
 (material observation nontrivial half depth ordinal h).environment
 (material observation nontrivial half depth ordinal h).raw
 (.const (receipt observation nontrivial half depth ordinal h).2.2.1) := by
 have endpoint : (material observation nontrivial half depth ordinal h).state.1 =
  .const (receipt observation nontrivial half depth ordinal h).2.2.1 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression _ _ _
 rw [← endpoint]
 exact (material observation nontrivial half depth ordinal h).state.2

theorem actual_orbit_write_read :
 actualWriteRead observation nontrivial half depth ordinal h =
 actualValue observation nontrivial half h + actualEffect observation nontrivial half depth ordinal h := by
 have source := write_read_at (factory observation nontrivial half depth ordinal h)
  (actionPacket observation nontrivial half depth ordinal h)
 rw [actual_complete_corrected_source,actual_material_source_effect] at source
 exact source

theorem actual_orbit_born_environment : type_of% (write_at_born
 (factory observation nontrivial half depth ordinal h)
 (actionPacket observation nontrivial half depth ordinal h)) :=
 write_at_born _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
