import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Consumer
set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Source
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open Cursor.Native.Feed.Source
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme)
end A
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (nextBorn datum resultFace baseRoot actualOccurrence frames runtime base)
end Shared
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value resultAt)
end O
abbrev Frame (depth count : Nat) := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Values depth count) (Var := Vars) (sort := true)
/-- Decode only the source coordinate; retain the other current environment. -/
def environmentAt (depth count : Nat) (prior : Env (Values depth count) Vars)
 (value : C depth count) : Env (Values depth count) Vars :=
 fun target name => match target with | false => value | true => prior true name
def sourceRaw (depth count : Nat) (frame : Frame depth count) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (Values depth count)) (Var := Vars) (sort := true) :=
 ⟨pairEnvironment frame.rawRead.environment (frame.activeEnvironment - frame.rawRead.environment),
  liftExpr (programme depth count)⟩
def sourceResult (depth count : Nat) (frame : Frame depth count) :=
 O.resultAt (Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} _occurrence => sourceRaw depth count (A.epoch frame))
  (Shared.actualOccurrence frame)
def nextInventory (depth count : Nat) (frame : Frame depth count) :=
 let written := SourceOperationPaidRelations.exposure frame.paidRead.state.2
 some (match frame.inventory with
  | none => written
  | some prior => SourceHistoryCommon.seed prior written)
def nextPairInventory (depth count : Nat) (frame : Frame depth count) :=
 let written := SourceOperationPaidRelations.exposure (sourceResult depth count frame).2.1.2
 some (match frame.pairInventory with
  | none => written
  | some prior => SourceHistoryCommon.seed prior written)
def continuous (depth count : Nat) : A.Programme
 (PhysicalValue := Values depth count) (PhysicalVar := Vars) (sort := true) where
 LowVar := Vars
 datum frame := {
  component := none
  reader := fun {_current} _occurrence => sourceRaw depth count frame
  nextEnvironmentReadAt := some (fun {_current} _occurrence value =>
   environmentAt depth count frame.activeEnvironment (value.1 + value.2).1) }
 nextInventory := nextInventory depth count
 nextPairInventory := nextPairInventory depth count

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
