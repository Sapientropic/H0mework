import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Source

/-! The already executed complete payment inventory and orbit material are
one source coface. The existing engine activates its unchanged pair syntax. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
open RootInquiryCompletion SourceOperationEffects
namespace B
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end B
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (frames runtime root visit baseRoot queryRoot resultRoot consumerRoot base datum queryLaw resultLaw consumerLaw compilationLaw
   query state presentation actual_node actual_query actual_answer actual_next actualVisit actualOccurrence)
end S
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))

def materialLaw : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ =>
    MaterialAt (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence ×
      ReceiptAt (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence
  project := fun _ {_current} occurrence _ =>
    ⟨(SourceOperationInquiry.Context.Native.Orbit.Installation.component frame).project PUnit.unit occurrence PUnit.unit,
      receiptAt (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence⟩

def chargedProgramme : B.Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) where
  LowVar := Orbit.Var PhysicalVar
  datum frame := {
    component := some (materialLaw frame)
    reader := fun {_current} occurrence => ((materialLaw frame).project PUnit.unit occurrence PUnit.unit).1.pairRaw }

abbrev commonRoot := (S.base frame).root.toAuthoritativeRoot
abbrev commonReader := fun (_ : (commonRoot frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (S.actualVisit frame).current) =>
  (S.datum frame programme).reader (S.actualOccurrence frame)
abbrev chargedState (count : Nat) := O.Completion.state (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
  (S.actualVisit frame).current (commonReader frame) count

theorem charged_state (count : Nat) : chargedState frame count =
    state frame (S.actualOccurrence frame) count :=
  CofaceTransport.state_preserved (commonRoot frame) (S.actualVisit frame).current (commonReader frame)
    (materialLaw frame) count

theorem charged_whole (count : Nat) :
    HEq (O.whole (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame) (chargedState frame count))
      (O.whole (originRoot frame) (S.actualVisit frame).current (commonReader frame)
        (state frame (S.actualOccurrence frame) count)) := by
  exact CofaceTransport.whole_preserved (commonRoot frame) (S.actualVisit frame).current (commonReader frame)
    (materialLaw frame) _ _ (heq_of_eq (charged_state frame count))

theorem charged_patch (count : Nat) :
    HEq (RootGeneratedDebtActivationJointSource.OwnerFree.patch (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame) (chargedState frame count)).toLedgerWriteEvolution
      (RootGeneratedDebtActivationJointSource.OwnerFree.patch (originRoot frame)
        (S.actualVisit frame).current (commonReader frame) (state frame (S.actualOccurrence frame) count)).toLedgerWriteEvolution :=
  (heq_of_eq (RootGeneratedDebtActivationJointSource.OwnerFree.patch_fold
    (S.baseRoot frame chargedProgramme).toAuthoritativeRoot (S.actualVisit frame).current (commonReader frame)
      (chargedState frame count))).trans
    ((charged_whole frame count).trans
      (heq_of_eq (RootGeneratedDebtActivationJointSource.OwnerFree.patch_fold (originRoot frame)
        (S.actualVisit frame).current (commonReader frame) (state frame (S.actualOccurrence frame) count))).symm)

variable (initial : A.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev frames := S.frames initial chargedProgramme
abbrev runtime := S.runtime initial chargedProgramme

variable (frame : A.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (S.base frame).root.source.base (materialLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame chargedProgramme).source.base
    (S.queryLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) chargedProgramme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame chargedProgramme).source.base
    (S.resultLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) chargedProgramme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame chargedProgramme).source.base
    (S.consumerLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) chargedProgramme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame chargedProgramme).source.base
    (S.compilationLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) chargedProgramme))

def face : SourceNativeRootSemanticFaceAt (S.root frame chargedProgramme) (S.visit frame chargedProgramme) where
  projection := (installation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem query_charged : (S.query frame chargedProgramme).raw = (face frame).rootRead.2.raw := rfl

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
