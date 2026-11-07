import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Input
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.Evaluation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

/-- The policy reads the proposal and bound context from this source before
any actual-action target is generated. -/
def evaluation := Policy.evaluate claim
  (Abolition.Accounting.Root.Reentry.Frame.state claim (Input.native claim frame proposal))
  (readLaw claim (Input.native claim frame proposal))
  (readMembers claim (Input.native claim frame proposal))
  (Input.readProposal claim frame proposal)

theorem evaluation_eq : HEq (evaluation claim frame proposal) (Policy.evaluate claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members proposal) := by
  unfold evaluation
  rw [Input.old_state_is_literal,readLaw_eq,readMembers_eq,Input.readProposal_eq]
  exact HEq.rfl

namespace Gate

inductive Projection
  | evaluation | compilation

def component : SourceNativeProjectionLaw
    (Input.native claim frame proposal).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .evaluation => type_of% (Root.evaluation claim frame proposal)
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := frame.basis.U7) (calculus := frame.basis.calculus)
      (oldTheory := frame.root.toAuthoritativeRoot.source.lawSurface)
      frame.row PUnit.unit (ULift.up.{1,0} occurrence) .answered (Responsibility.Family.State claim)
  project := fun projection {_} _ _ => match projection with
    | .evaluation => Root.evaluation claim frame proposal
    | .compilation => .canonical (Abolition.Accounting.Root.Reentry.Frame.updated claim
      (Input.native claim frame proposal) (Root.evaluation claim frame proposal).executableWord)

def native : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim where
  V := frame.V
  root := (Input.native claim frame proposal).root.withProjectionCoface (component claim frame proposal)
  visit := frame.visit
  row := frame.row
  rowKey := frame.rowKey
  authority := (Input.native claim frame proposal).authority.withProjectionCoface (component claim frame proposal)
  finite := frame.finite
  occurrence_eq := frame.occurrence_eq
  open_fibres := frame.open_fibres
  basis := frame.basis
  actualLaw := frame.actualLaw
  members := frame.members
  contextFace := { projection := .inherited (Input.native claim frame proposal).contextFace.projection
                   active := (Input.native claim frame proposal).contextFace.active
                   classifier_eq := (Input.native claim frame proposal).contextFace.classifier_eq }
  context_heq := (Input.native claim frame proposal).context_heq

def evaluationFace : SourceNativeRootSemanticFaceAt (native claim frame proposal).root frame.visit :=
  { projection := .component Projection.evaluation,active := PUnit.unit,classifier_eq := rfl }

def readEvaluation : type_of% (Root.evaluation claim frame proposal) :=
  (evaluationFace claim frame proposal).rootRead

def executableWord : RawEvent Party Good Port Technology Instrument :=
  (readEvaluation claim frame proposal).executableWord

theorem readEvaluation_eq : readEvaluation claim frame proposal = Root.evaluation claim frame proposal := rfl

theorem executableWord_eq :
    executableWord claim frame proposal = (Root.evaluation claim frame proposal).executableWord := rfl

theorem executableWord_eq_original_evaluation : executableWord claim frame proposal =
    (Policy.evaluate claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal).executableWord := by
  change (Root.evaluation claim frame proposal).executableWord = _
  unfold Root.evaluation
  rw [Input.old_state_is_literal,readLaw_eq,readMembers_eq,Input.readProposal_eq]
  rfl

theorem original_row_is_literal : (native claim frame proposal).row = frame.row := rfl

theorem original_physical_state_is_literal :
    Abolition.Accounting.Root.Reentry.Frame.state claim (native claim frame proposal) =
      Abolition.Accounting.Root.Reentry.Frame.state claim frame := rfl

end Gate
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root
