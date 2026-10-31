import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Reply

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Innovation

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

inductive Projection
  | reply | compilation

private def replyComponent (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (Answer : Type) (answer : Answer) :
    SourceNativeProjectionLaw original.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .reply => Answer
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := original.basis.U7) (calculus := original.basis.calculus)
      (oldTheory := original.root.toAuthoritativeRoot.source.lawSurface)
      original.row PUnit.unit (ULift.up.{1,0} occurrence) .answered Answer
  project := fun projection {_} _ _ => match projection with
    | .reply => answer
    | .compilation => .canonical answer

def component := replyComponent claim (Root.Renewal.native claim frame proposal)
  (Reply claim frame proposal) (Refusal.reply claim frame proposal)

private def attach (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (face : SourceNativeProjectionLaw original.root.toAuthoritativeRoot.toLedgerRoot.source) :
    Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim where
  V := original.V
  root := original.root.withProjectionCoface face
  visit := original.visit
  row := original.row
  rowKey := original.rowKey
  authority := original.authority.withProjectionCoface face
  finite := original.finite
  occurrence_eq := original.occurrence_eq
  open_fibres := original.open_fibres
  basis := original.basis
  actualLaw := original.actualLaw
  members := original.members
  contextFace := { projection := .inherited original.contextFace.projection
                   active := original.contextFace.active
                   classifier_eq := original.contextFace.classifier_eq }
  context_heq := original.context_heq

private theorem attached_support_is_literal (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (face : SourceNativeProjectionLaw original.root.toAuthoritativeRoot.toLedgerRoot.source) :
    Abolition.Accounting.Root.Reentry.Frame.support claim (attach claim original face) =
      Abolition.Accounting.Root.Reentry.Frame.support claim original := rfl

private theorem state_of_literal_support
    (first second : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (same : Abolition.Accounting.Root.Reentry.Frame.support claim first =
      Abolition.Accounting.Root.Reentry.Frame.support claim second) :
    Abolition.Accounting.Root.Reentry.Frame.state claim first =
      Abolition.Accounting.Root.Reentry.Frame.state claim second := by
  have left := Option.some_get (Abolition.Accounting.Root.Reentry.Frame.active claim first)
  have right := Option.some_get (Abolition.Accounting.Root.Reentry.Frame.active claim second)
  exact Option.some.inj (left.trans ((congrArg Prod.snd same).trans right.symm))

def native : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim :=
  attach claim (Root.Renewal.native claim frame proposal) (component claim frame proposal)

def replyFace : SourceNativeRootSemanticFaceAt (native claim frame proposal).root (native claim frame proposal).visit :=
  { projection := .component Projection.reply,active := PUnit.unit,classifier_eq := rfl }

def readReply : Reply claim frame proposal := (replyFace claim frame proposal).rootRead

theorem the_compiler_reply_is_the_actual_source_face :
    readReply claim frame proposal = Refusal.reply claim frame proposal := rfl

theorem the_source_state_is_the_original_row :
    Abolition.Accounting.Root.Reentry.Frame.state claim (native claim frame proposal) =
      Abolition.Accounting.Root.Reentry.Frame.state claim frame :=
  state_of_literal_support claim _ _
    ((attached_support_is_literal claim (Root.Renewal.native claim frame proposal) (component claim frame proposal)).trans
      (Root.Installation.source_support_is_literal claim frame proposal))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Source
