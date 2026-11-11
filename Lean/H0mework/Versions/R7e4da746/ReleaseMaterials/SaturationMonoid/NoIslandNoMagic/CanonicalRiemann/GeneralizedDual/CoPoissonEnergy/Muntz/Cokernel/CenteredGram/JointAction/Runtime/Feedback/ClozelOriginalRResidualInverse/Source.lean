import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalRResidualInverse.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalRResidualInverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace D
export OriginalKCombFirstFullSourceDynamics (factory packet)
end D
namespace CM
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (reader reader_pair reader_paid_raw reader_paid_environment queryFactory)
end CM
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery
 (programme query_action_raw action_original_raw result_action old_restriction)
end Q
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory cfg)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket template nextCfg stockCfg stock_action_reader nativeAfterAdmission bornAfterNative next_action_reader nextSeed)
end AS
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence datum baseRoot)
end S
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end I
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial)
end R
namespace Native
export ActualCofinalSourceAction (nativePacket native_packet_actual selected sourceBorn receiver_input receiver_ast born_environment)
end Native
local instance sourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)

-- Read the actual current material first; act on its complete literal programme.
def inverseReader (grade : Nat)
 (frame : A.M.Frame (Value := L.Value (PairValue C.Value) grade) (Var := C.Var) (sort := ()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : I.Occurrence frame (current := current)) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (L.Value (PairValue C.Value) grade)) (Var := C.Var) (sort := ()) :=
 let original := CM.reader frame supplied
 ⟨original.environment, .linear (inverseAt observation nontrivial half grade) original.expression⟩

def bareFactory : SF.Factory (PairValue C.Value) C.Var () :=
 { CM.queryFactory (D.factory observation nontrivial half) with
  datum := fun grade seed currentFrame =>
   { (CM.queryFactory (D.factory observation nontrivial half)).datum grade seed currentFrame with
    calculationReader := some (fun {_current} supplied => inverseReader observation nontrivial half grade currentFrame supplied) } }

def factory : SF.Factory (PairValue C.Value) C.Var () :=
 { bareFactory observation nontrivial half with
  datum := fun grade seed currentFrame =>
   (Q.programme (SF.cfg (bareFactory observation nontrivial half) grade seed)).datum currentFrame }

theorem bare_query_programme (grade : Nat)
 (seed : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Seed (PairValue C.Value) C.Var () grade) :
 SF.cfg (factory observation nontrivial half) grade seed =
 Q.programme (SF.cfg (bareFactory observation nontrivial half) grade seed) := rfl

theorem source_reader (grade : Nat)
 (seed : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Seed (PairValue C.Value) C.Var () grade)
 (frame : A.M.Frame (Value := L.Value (PairValue C.Value) grade) (Var := C.Var) (sort := ()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : I.Occurrence frame (current := current)) :
 R.actionReader frame (SF.cfg (factory observation nontrivial half) grade seed) supplied =
 inverseReader observation nontrivial half grade (A.epoch frame) supplied := rfl

theorem bare_query_action (grade : Nat)
 (seed : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Seed (PairValue C.Value) C.Var () grade)
 (currentFrame : A.M.Frame (Value := L.Value (PairValue C.Value) grade) (Var := C.Var) (sort := ())) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query currentFrame
  (SF.cfg (factory observation nontrivial half) grade seed)).raw =
 R.actionReader currentFrame (SF.cfg (factory observation nontrivial half) grade seed) (S.actualOccurrence currentFrame) := by
 rw [bare_query_programme]
 exact Q.query_action_raw _ _

theorem bare_query_receipt (grade : Nat)
 (seed : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Seed (PairValue C.Value) C.Var () grade)
 (currentFrame : A.M.Frame (Value := L.Value (PairValue C.Value) grade) (Var := C.Var) (sort := ())) :
 HEq (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace currentFrame
  (SF.cfg (factory observation nontrivial half) grade seed)).rootRead
  (R.actionResultAt currentFrame (SF.cfg (factory observation nontrivial half) grade seed) (S.actualOccurrence currentFrame)) := by
 rw [bare_query_programme]
 exact Q.result_action _ _

def HasInverseReader (grade : Nat)
 (programme : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()))
 (language : programme.LowVar = C.Var) : Prop :=
 ∀ (currentFrame : A.M.Frame (Value := L.Value (PairValue C.Value) grade) (Var := C.Var) (sort := ()))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
 (supplied : I.Occurrence currentFrame (current := current)),
 R.actionReader currentFrame (AS.stockCfg programme) supplied =
 Eq.mp (congrArg (fun variableFamily => RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (L.Value (PairValue C.Value) grade)) (Var := variableFamily) (sort := ())) language.symm)
  (inverseReader observation nontrivial half grade (A.epoch currentFrame) supplied)

theorem native_installed_reader
 (parent : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
 let native := AS.nativeAfterAdmission (factory observation nontrivial half) parent
 HasInverseReader observation nontrivial half native.1 native.2.2.1 native.2.2.2.down := by
 dsimp only
 rcases parent with ⟨grade, data, programme, ⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar = C.Var at sameVar
  cases sameVar
  intro currentFrame current supplied
  change R.actionReader currentFrame
   (AS.stockCfg (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.nextBase
    (factory observation nontrivial half) grade data ⟨C.Var,datum,inventory,pairInventory⟩ rfl)) supplied = _
  exact (AS.next_action_reader (factory observation nontrivial half) grade data
   ⟨C.Var,datum,inventory,pairInventory⟩ rfl currentFrame supplied).trans
   (source_reader observation nontrivial half (grade+1)
    (AS.nextSeed (factory observation nontrivial half) grade data ⟨C.Var,datum,inventory,pairInventory⟩ rfl)
    currentFrame supplied)

private theorem own_value
 (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
 (installed : HasInverseReader observation nontrivial half packet.1 packet.2.2.1 packet.2.2.2.down) :
 totalAt packet.1 (R.actionResultAt packet.2.1.1 packet.2.2.1
  (S.actualOccurrence packet.2.1.1)).2.2.1 =
 Prior.inverse observation nontrivial half (totalAt packet.1
  ((CM.reader (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).expression.eval
   (CM.reader (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).environment)) := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar = C.Var at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
   ⟨C.Var,datum,inventory,pairInventory⟩
  have reader := (AS.stock_action_reader data.1 cfg (S.actualOccurrence data.1)).symm.trans
   (installed data.1 (S.actualOccurrence data.1))
  have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
   (S.baseRoot data.1 cfg).toAuthoritativeRoot (R.actionReader data.1 cfg) (S.actualOccurrence data.1)
  have generated := paid.trans (congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value := PairValue (L.Value (PairValue C.Value) grade)) (Var := C.Var) (sort := ()) => raw.expression.eval raw.environment) reader)
  exact (congrArg (totalAt grade) generated).trans (inverseAt_total observation nontrivial half grade _)

variable (depth ordinal : Nat)
abbrev parentPacket := D.packet observation nontrivial half depth ordinal
def nativePacket := AS.nativeAfterAdmission (factory observation nontrivial half)
 (parentPacket observation nontrivial half depth ordinal)
abbrev configuration := (nativePacket observation nontrivial half depth ordinal).2.2.1
abbrev frame := (nativePacket observation nontrivial half depth ordinal).2.1.1
abbrev material := R.actualMaterial (frame observation nontrivial half depth ordinal)
 (configuration observation nontrivial half depth ordinal)
abbrev receipt := R.actionResultAt (frame observation nontrivial half depth ordinal)
 (configuration observation nontrivial half depth ordinal) (S.actualOccurrence (frame observation nontrivial half depth ordinal))

theorem actual_reader_installed : type_of%
 (native_installed_reader observation nontrivial half (parentPacket observation nontrivial half depth ordinal)) :=
 native_installed_reader observation nontrivial half (parentPacket observation nontrivial half depth ordinal)

theorem actual_inverse_residual_value : type_of%
 (own_value observation nontrivial half (nativePacket observation nontrivial half depth ordinal)
  (actual_reader_installed observation nontrivial half depth ordinal)) :=
 own_value observation nontrivial half (nativePacket observation nontrivial half depth ordinal)
  (actual_reader_installed observation nontrivial half depth ordinal)

attribute [irreducible] factory nativePacket

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalRResidualInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
