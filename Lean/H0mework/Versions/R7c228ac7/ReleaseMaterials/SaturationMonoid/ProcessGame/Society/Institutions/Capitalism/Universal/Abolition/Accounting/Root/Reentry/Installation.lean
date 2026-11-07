import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Installation

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
  (frame : Frame (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

inductive Projection
  | input | compilation

def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .input => RawEvent Party Good Port Technology Instrument
    | .compilation => SourceNativeInquiryCompilationTokenAt
      (U7 := frame.basis.U7) (calculus := frame.basis.calculus)
      (oldTheory := frame.root.toAuthoritativeRoot.source.lawSurface)
      frame.row PUnit.unit (ULift.up.{1,0} occurrence) .answered (Responsibility.Family.State claim)
  project := fun projection {_} _ _ => match projection with
    | .input => word
    | .compilation => .canonical (Frame.updated claim frame word)

def native : Frame (oldN := oldN) claim where
  V := frame.V
  root := frame.root.withProjectionCoface (component claim frame word)
  visit := frame.visit
  row := frame.row
  rowKey := frame.rowKey
  authority := frame.authority.withProjectionCoface (component claim frame word)
  finite := frame.finite
  occurrence_eq := frame.occurrence_eq
  open_fibres := frame.open_fibres
  basis := frame.basis
  actualLaw := frame.actualLaw
  members := frame.members
  contextFace := { projection := .inherited frame.contextFace.projection
                   active := frame.contextFace.active
                   classifier_eq := frame.contextFace.classifier_eq }
  context_heq := frame.context_heq

/-- The compiler reads the one input face installed on this exact source root. -/
def readWord : RawEvent Party Good Port Technology Instrument :=
  (native claim frame word).root.toAuthoritativeRoot.source.projectionLaw.project
    (.component Projection.input) ((native claim frame word).root.emitted frame.visit.current) PUnit.unit

def program : SourceNativeInquiryCompilationProgramAt (native claim frame word).root frame.visit
    frame.basis.U7 frame.basis.calculus (native claim frame word).root.toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((native claim frame word).root.emitted frame.visit.current))
    frame.row (native claim frame word).authority where
  compile := fun _ => .actualAction (Reentry.generated claim (native claim frame word) (readWord claim frame word))

def state : RootInquiryStateAt
    (DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)) frame.V where
  root := (native claim frame word).root
  visit := frame.visit
  U7 := frame.basis.U7
  calculus := frame.basis.calculus
  Query := PUnit
  entryAt := fun _ => frame.row
  authorityAt := fun _ => (native claim frame word).authority
  compilationProgramAt := fun query => by cases query; exact program claim frame word
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .component Projection.compilation
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state claim frame word)⟩

def successor : Frame (oldN := oldN) claim :=
  nextFrame claim (native claim frame word) (readWord claim frame word)

theorem compilation_uses_the_original_roots_current_input_face :
    (state claim frame word).compileInquiry PUnit.unit =
      .actualAction (Reentry.generated claim (native claim frame word) (readWord claim frame word)) := rfl

theorem input_face_is_literal : readWord claim frame word = word := rfl

theorem successor_reads_the_actual_updated_row :
    Frame.state claim (successor claim frame word) =
      Responsibility.Family.State.advance claim (Frame.state claim frame) frame.actualLaw word := by
  unfold successor
  rw [next_frame_reads_the_actual_updated_state]
  rfl

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq (presentation claim frame word) PUnit.unit
      (Reentry.generated claim (native claim frame word) (readWord claim frame word)) rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq (presentation claim frame word) PUnit.unit
    (Reentry.generated claim (native claim frame word) (readWord claim frame word)) rfl

theorem actual_process_resumption_is_the_same_native_next :
    (RootInquiryProcessNode.answered (presentation claim frame word) PUnit.unit).erase =
      (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
        ⟨(successor claim frame word).V,(successor claim frame word).root.toAuthoritativeRoot,
          (successor claim frame word).visit⟩⟩ : AnyAuthoritativeRootCurrent) := by
  change (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
    (Reentry.generated claim (native claim frame word) (readWord claim frame word)).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun current =>
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),current⟩ : AnyAuthoritativeRootCurrent))
    (Reentry.generated claim (native claim frame word) (readWord claim frame word)).target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Installation
