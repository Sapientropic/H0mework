import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Target
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Component
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData.Builders

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (data : Continuation.FinancialData frame) (reader : Raw.Reader input depth count)
  (basis : Inquiry.Basis frame.N)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

def completeFrame := Raw.installCompleteFrame (nativeFrame frame registered)
  (data.born registered) reader (inquiryBasis frame registered basis)

theorem complete_old_projection_outcome_is_preserved
    (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((completeFrame frame data reader basis registered).root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (.inherited (.inl projection))
      ((completeFrame frame data reader basis registered).root.emitted (initial frame registered)))
      (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted origin)) := by
  have lifted := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (livingRoot frame registered).source.base
    (Raw.component (nativeFrame frame registered) (data.born registered) reader
      (inquiryBasis frame registered basis))).outcome_heq
      (emitted frame registered (initial frame registered)) (.inl projection)
  refine lifted.trans ?_
  change HEq ((projectionLaw frame registered).outcomeAt (.inl projection)
    (emitted frame registered (initial frame registered)))
    (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted origin))
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [projectionLaw, classify, initial]
  cases frame.root.toAuthoritativeRoot.source.projectionLaw.classify projection (frame.root.emitted origin) <;> rfl

variable (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (selected : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

/-- The same paid registration now chooses its complete next-input root
before first write. The financial step and whole-ledger target are unchanged. -/
def completeTargetAt
    (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeDebtAdmissionActualActionTargetAt frame.root visit event (frame.entry visit.current) authority :=
  { targetAt frame basis visit selected authority event with
    targetRoot := (completeFrame frame data reader basis selected).root
    oldProjection := fun projection => .inherited (.inl projection)
    oldProjection_injective := by
      intro left right same
      injection same with old
      exact Sum.inl.inj old
    oldOutcome_heq := complete_old_projection_outcome_is_preserved frame data reader basis selected
    canonical_targetNextVisit_eq := Ingress.next_is_the_same_generated_successor
      (completeFrame frame data reader basis selected).root
      (.finite (completeFrame frame data reader basis selected).root.toAuthoritativeRoot.toRoot.initialVisit)
      (firstSuccessor frame basis visit selected) }

def completeProgram : SourceNativeDebtAdmissionActualActionProgramAt frame.root visit (frame.entry visit.current) authority where
  targetAt := completeTargetAt frame data reader basis visit selected authority

theorem complete_target_preserves_the_original_paid_step
    (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    (completeTargetAt frame data reader basis visit selected authority event).stepEvent =
      (targetAt frame basis visit selected authority event).stepEvent := rfl

#print axioms completeProgram
#print axioms complete_target_preserves_the_original_paid_step

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
