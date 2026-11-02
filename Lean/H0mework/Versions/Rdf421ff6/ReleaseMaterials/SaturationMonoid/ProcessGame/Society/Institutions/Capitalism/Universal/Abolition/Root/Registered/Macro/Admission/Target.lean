import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Rows
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Readback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Next
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel

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
  (basis : Inquiry.Basis frame.N)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

def targetInitial := (activeFrame frame registered basis).root.toAuthoritativeRoot.toRoot.initialVisit

def initialOldRow (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current)) :=
  generatedRow frame registered basis (.finite (targetInitial frame basis visit registered))
    (oldEntry (law := registered.law) (state? := some .pending) entry)

def initialBornRow := generatedRow frame registered basis (.finite (targetInitial frame basis visit registered))
  (debtEntry (N := frame.N) (law := registered.law) (frame.sourceSupport visit.current) .pending)

def firstSuccessor := (activeFrame frame registered basis).successor (initial frame registered)

theorem first_support_is_the_same_native_admission :
    (firstSuccessor frame basis visit registered).targetOccurrence.1 =
      ((frame.successor visit.current).targetOccurrence.1, some registered.firstStep.target) := by
  have observed := successor_support frame registered (initial frame registered)
  apply observed.trans
  apply Prod.ext
  · exact (congrArg (fun occurrence => occurrence.1) (frame.target_occurrence visit.current)).symm
  · exact congrArg some (next_state frame registered EventAt.pending)

theorem first_destination_is_the_same_native_admission :
    HEq (firstSuccessor frame basis visit registered).ledgerEvolution.destination
      (DebtActivationLedger.jointStepLedgerEvolution (frame.successor visit.current).ledgerEvolution
        (frame.entry visit.current) registered.firstStep.step).destination :=
  (successor_destination frame registered (initial frame registered)).trans (first_destination_is_original_admission frame registered)

def targetAt (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeDebtAdmissionActualActionTargetAt frame.root visit event (frame.entry visit.current) authority := by
  rw [event.eq_generated]
  exact {
    law := registered.law
    sourceState := .pending
    stepEvent := registered.firstStep
    sourceSuccessor := frame.successor visit.current
    TargetV := V frame registered
    targetRoot := (activeFrame frame registered basis).root
    initialSupport_eq := rfl
    initialOldRow := initialOldRow frame basis visit registered
    initialBornRow := initialBornRow frame basis visit registered
    firstSuccessor := firstSuccessor frame basis visit registered
    firstSupport_eq := first_support_is_the_same_native_admission frame basis visit registered
    firstDestination_heq := first_destination_is_the_same_native_admission frame basis visit registered
    oldProjection := fun projection => .inherited (.inl projection)
    oldProjection_injective := by
      intro left right same
      injection same with old
      exact Sum.inl.inj old
    oldOutcome_heq := old_projection_outcome_is_preserved frame registered basis
    canonical_targetNextVisit_eq := Ingress.next_is_the_same_generated_successor
      (activeFrame frame registered basis).root (.finite (targetInitial frame basis visit registered))
      (firstSuccessor frame basis visit registered)
    Answer := Inquiry.Answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
    answer := Inquiry.answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame visit.current
    Receipt := fun _ => ULift.{3, 0} (PLift
      ((nativeFrame frame registered).account (firstSuccessor frame basis visit registered).targetCurrent = registered.admitted ∧
        ¬ Nonempty (registered.law.SettlementAt registered.firstStep.target)))
    receipt := ⟨⟨first_source_step_registers_the_same_original_debt frame registered,
      registered.issued.registration_does_not_claim_financial_settlement input depth count⟩⟩ }

def program : SourceNativeDebtAdmissionActualActionProgramAt frame.root visit (frame.entry visit.current) authority where
  targetAt := targetAt frame basis visit registered authority

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
