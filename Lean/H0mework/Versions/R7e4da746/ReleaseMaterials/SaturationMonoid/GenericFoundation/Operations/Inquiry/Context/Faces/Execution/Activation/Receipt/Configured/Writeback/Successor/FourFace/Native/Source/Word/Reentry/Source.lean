import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Source
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (request betaState reader originMaterialAt sourceOccurrence OriginMaterialAt generatedAction originInstallation)
end SN
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base baseRoot baseInstallation queryRoot queryLaw resultRoot resultLaw consumerRoot consumerLaw compilationLaw
   root visit actualOccurrence frames next nextBorn datum resultFace)
end S
namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
  (material component physical updatedSeed disposition raw installedReader programme writtenSeed)
end IP
namespace AS
export ActualNativeRelationTransport.AS (stockCfg stockScalar)
end AS
namespace AN
export ActualNativeRelationTransport (bornStock)
end AN
namespace C
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (World JointV)
end C
namespace R
export SourceGeneratedInquiryReceiptAction (packetAt actionReader actualMaterial registered)
end R
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured
  (targetAt generatedAction sourcePresentation targetPresentation successor_valid compiles whole_first target_next)
end CF
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt receipt_next receipt_compiles)
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read receipt_paid_prefix)
end Prefix
end Complete

variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target, AddCommGroup (V target)] {s : Sorts}
variable (frame : A.M.Frame (Value := PairValue V) (Var := X) (sort := s))
variable (base : A.Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := s))
variable (before : Inventory (V := V) (X := X) (s := s)) (oldEnvironment : Env V X)
variable (admissions : List (AdmissionReceipt.Admission before (AS.stockScalar frame base)))

private theorem state_congr
    {first second : A.M.Frame (Value := PairValue V) (Var := X) (sort := s)}
    (same : first = second) : HEq first.event.state second.event.state := by
  cases same
  exact HEq.rfl

abbrev betaRequest := SN.request frame base before oldEnvironment admissions

/-- Both source stocks are read from the same original decoder birth. -/
def scalarSource : Inventory (V := PairValue V) (X := X) (s := s) :=
  AN.bornStock frame base

def seed : Inventory (V := PairValue V) (X := X) (s := s) :=
  SourceHistoryCommon.seed (scalarSource frame base)
    (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
      (betaRequest frame base before oldEnvironment admissions).input.expression))

def initial : A.M.Frame (Value := PairValue V) (Var := X) (sort := s) where
  N := C.World frame.registered
  V := C.JointV frame.registered frame.packetAt
  old := SN.betaState frame base before oldEnvironment admissions
  registered := betaRequest frame base before oldEnvironment admissions
  packetAt := R.packetAt frame (AS.stockCfg base)
  environment := fun {_current} supplied => (SN.reader frame base before oldEnvironment admissions supplied).environment
  depth := 0
  inventory := some (seed frame base before oldEnvironment admissions)
  pairInventory := (AS.stockCfg base).nextPairInventory frame

theorem initial_registered : (initial frame base before oldEnvironment admissions).registered =
    betaRequest frame base before oldEnvironment admissions := rfl

theorem initial_target_lower :
    (initial frame base before oldEnvironment admissions).currentState.root.toAuthoritativeRoot.toLedgerRoot =
    (SN.generatedAction frame base before oldEnvironment admissions).target.targetRoot.toAuthoritativeRoot.toLedgerRoot := rfl

theorem initial_target_current :
    (initial frame base before oldEnvironment admissions).currentState.visit.current =
    (SN.generatedAction frame base before oldEnvironment admissions).target.targetVisit.current := rfl

variable (sourceFrame : A.M.Frame (Value := PairValue V) (Var := X) (sort := s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current sourceFrame.registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence sourceFrame (current := current))

/-- The original source occurrence and the supplied current occurrence stay separate. -/
structure SourceAt where
  original : SN.OriginMaterialAt frame base before (SN.sourceOccurrence frame base)
  currentMaterial : type_of% (IP.material (seed frame base before oldEnvironment admissions) sourceFrame supplied)

def materialAt : SourceAt frame base before oldEnvironment admissions sourceFrame supplied :=
  ⟨SN.originMaterialAt frame base before oldEnvironment admissions (SN.sourceOccurrence frame base),
   IP.material (seed frame base before oldEnvironment admissions) sourceFrame supplied⟩

def component : SourceNativeProjectionLaw
    (S.base sourceFrame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => SourceAt frame base before oldEnvironment admissions sourceFrame occurrence
  project := fun _ {_current} occurrence _ => materialAt frame base before oldEnvironment admissions sourceFrame occurrence

def sourceReader :=
  ((component frame base before oldEnvironment admissions sourceFrame).project PUnit.unit supplied PUnit.unit).currentMaterial.2.2.2.2.2.1

theorem reader_from_disposition : sourceReader frame base before oldEnvironment admissions sourceFrame supplied =
    IP.raw (seed frame base before oldEnvironment admissions) sourceFrame supplied := rfl

def programme : A.Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := s) :=
  { IP.programme (seed frame base before oldEnvironment admissions) with
    datum := fun sourceFrame => {
      component := some (component frame base before oldEnvironment admissions sourceFrame)
      reader := sourceReader frame base before oldEnvironment admissions sourceFrame } }

theorem actual_action_reader : R.actionReader sourceFrame (programme frame base before oldEnvironment admissions) supplied =
    IP.raw (seed frame base before oldEnvironment admissions) (A.epoch sourceFrame) supplied := rfl

def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (S.base sourceFrame).root.source.base (component frame base before oldEnvironment admissions (A.epoch sourceFrame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (S.baseRoot sourceFrame (programme frame base before oldEnvironment admissions)).source.base
    (S.queryLaw (A.epoch sourceFrame) (programme frame base before oldEnvironment admissions))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (S.queryRoot sourceFrame (programme frame base before oldEnvironment admissions)).source.base
    (S.resultLaw (A.epoch sourceFrame) (programme frame base before oldEnvironment admissions))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (S.resultRoot sourceFrame (programme frame base before oldEnvironment admissions)).source.base
    (S.consumerLaw (A.epoch sourceFrame) (programme frame base before oldEnvironment admissions))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (S.consumerRoot sourceFrame (programme frame base before oldEnvironment admissions)).source.base
    (S.compilationLaw (A.epoch sourceFrame) (programme frame base before oldEnvironment admissions)))

def face : SourceNativeRootSemanticFaceAt
    (S.root sourceFrame (programme frame base before oldEnvironment admissions))
    (S.visit sourceFrame (programme frame base before oldEnvironment admissions)) where
  projection := (installation frame base before oldEnvironment admissions sourceFrame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem installed_material : (face frame base before oldEnvironment admissions sourceFrame).rootRead =
    materialAt frame base before oldEnvironment admissions (A.epoch sourceFrame) (S.actualOccurrence sourceFrame) := rfl

theorem installed_paid_state :
    (face frame base before oldEnvironment admissions sourceFrame).rootRead.currentMaterial.1.paid.state =
    sourceFrame.event.state := rfl

abbrev selected := Complete.atReceipt (programme frame base before oldEnvironment admissions)
  (initial frame base before oldEnvironment admissions) 0

theorem selected_epoch : A.epoch (selected frame base before oldEnvironment admissions) =
    A.epoch (initial frame base before oldEnvironment admissions) := by
  apply Complete.Prefix.receipt_read _ _
    (fun stage => A.epoch (S.frames (initial frame base before oldEnvironment admissions)
      (programme frame base before oldEnvironment admissions) stage)) _ 0
  intro stage paid actual
  change A.epoch (S.next _ _) = _
  unfold S.next
  rw [actual]
  rfl

theorem selected_frame : selected frame base before oldEnvironment admissions =
    { initial frame base before oldEnvironment admissions with
      depth := (selected frame base before oldEnvironment admissions).depth } := by
  calc
    selected frame base before oldEnvironment admissions =
        { A.epoch (selected frame base before oldEnvironment admissions) with
          depth := (selected frame base before oldEnvironment admissions).depth } := rfl
    _ = { A.epoch (initial frame base before oldEnvironment admissions) with
          depth := (selected frame base before oldEnvironment admissions).depth } :=
      congrArg (fun sourceFrame : A.M.Frame (Value := PairValue V) (Var := X) (sort := s) =>
        {sourceFrame with depth := (selected frame base before oldEnvironment admissions).depth})
        (selected_epoch frame base before oldEnvironment admissions)
    _ = _ := rfl

theorem selected_raw : (selected frame base before oldEnvironment admissions).rawRead =
    (initial frame base before oldEnvironment admissions).rawRead := by
  have read := congrArg (fun sourceFrame : A.M.Frame (Value := PairValue V) (Var := X) (sort := s) => sourceFrame.rawRead)
    (selected_epoch frame base before oldEnvironment admissions)
  exact read

/-- This is the original CP339 target's actual registered-query occurrence. -/
def completedOriginFace : SourceNativeRootSemanticFaceAt
    (SN.generatedAction frame base before oldEnvironment admissions).target.targetRoot
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathVisit
      (SN.betaState frame base before oldEnvironment admissions)
      (betaRequest frame base before oldEnvironment admissions)
      (R.packetAt frame (AS.stockCfg base))
      (selected frame base before oldEnvironment admissions).depth) where
  projection := (SN.originInstallation frame base before oldEnvironment admissions).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem selected_state_is_original : HEq
    (selected frame base before oldEnvironment admissions).event.state
    (completedOriginFace frame base before oldEnvironment admissions).rootRead.state :=
  state_congr (selected_frame frame base before oldEnvironment admissions)

theorem installed_completed_state : HEq
    (face frame base before oldEnvironment admissions (selected frame base before oldEnvironment admissions)).rootRead.currentMaterial.1.paid.state
    (completedOriginFace frame base before oldEnvironment admissions).rootRead.state :=
  (heq_of_eq (installed_paid_state frame base before oldEnvironment admissions _)).trans
    (selected_state_is_original frame base before oldEnvironment admissions)

theorem selected_action : (selected frame base before oldEnvironment admissions).action =
    .inl (Complete.receipt (programme frame base before oldEnvironment admissions)
      (initial frame base before oldEnvironment admissions) 0).2.1 :=
  (Complete.receipt (programme frame base before oldEnvironment admissions)
    (initial frame base before oldEnvironment admissions) 0).2.2.2

/-- Each step uses the existing canonical row payment; execution cost is not the debt measure. -/
def paidPrefix (offset : Fin (Complete.receipt (programme frame base before oldEnvironment admissions)
    (initial frame base before oldEnvironment admissions) 0).1) :=
  let actual := Complete.Prefix.receipt_paid_prefix (programme frame base before oldEnvironment admissions)
    (initial frame base before oldEnvironment admissions) 0 offset
  SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.payment
    (programme frame base before oldEnvironment admissions)
    (S.frames (initial frame base before oldEnvironment admissions)
      (programme frame base before oldEnvironment admissions) (0 + offset.val)) actual.1 actual.2.down

theorem completed_trace_written (event)
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (selected frame base before oldEnvironment admissions).event.state.2).trace) :
    event ∈ (IP.updatedSeed (seed frame base before oldEnvironment admissions)
      (A.epoch (selected frame base before oldEnvironment admissions))
      (S.actualOccurrence (selected frame base before oldEnvironment admissions))).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present

end SourceInventoryExecutionFeed.SourceWordNative.Reentry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
