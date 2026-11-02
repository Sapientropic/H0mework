import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Compilation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open M14SourceGeneratedContributionMergeActionSource
open SourceNativeInquiryRuntime
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (positive : 0 < ProgrammeSource.registrationSize input)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)
  (initialZero : input.initial.claims = fun _ _ _ => 0)
  (sourceStart : Nat)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem the_programme_input_uses_the_existing_society_payment :
    (FreshPayment.span oldVisit sourceIndex boundary).targetPaymentOccurrence.rootOccurrence =
      (InputSource.root (Financial.Installation.Runtime.datum input)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (InputSource.visit (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary) :=
  FreshPayment.payment_is_exact_original_root_event oldVisit sourceIndex boundary

theorem the_original_external_root_consumes_the_source_selected_programme :
    CofaceRealizationResumptionAt
      (Financial.Installation.Runtime.originalInputCore input oldVisit sourceIndex boundary)
      (Financial.Installation.Runtime.runtime input positive oldVisit sourceIndex boundary initialZero) 0 ∧
    SequentialActualActionResumptionAt
      (Financial.Installation.Ingress.generated input 1)
      (Financial.Installation.Runtime.runtime input positive oldVisit sourceIndex boundary initialZero) 1 ∧
    (InputSource.frontier (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary).rooted.oldTargetEntry =
      (FreshPayment.frontier oldVisit sourceIndex boundary).rooted.oldTargetEntry ∧
    HEq (InputSource.frontier (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary).rooted.oldSuccessor
      (FreshPayment.frontier oldVisit sourceIndex boundary).rooted.oldSuccessor :=
  ⟨Financial.Installation.Runtime.actual_registered_core_is_consumed input positive oldVisit sourceIndex boundary initialZero,
    Financial.Installation.Runtime.actual_ingress_is_consumed input positive oldVisit sourceIndex boundary initialZero,
    InputSource.original_row_and_successor_preserved (Financial.Installation.Runtime.datum input)
      oldVisit sourceIndex boundary⟩

/-- The source-owned drain chooses a cut of the already running external
Payment process. No root, accounting state or execution receipt is an input. -/
theorem the_macro_source_is_an_actual_external_payment_cut :
    ((Financial.Installation.Runtime.runtime input positive oldVisit sourceIndex boundary initialZero).stateAt
      (Macro.Ingress.cut input 1 sourceStart + 2)).engine.node =
        .active ((Macro.Ingress.frame input 1 sourceStart).presentation input) :=
  Financial.Installation.Runtime.actual_account_node input positive oldVisit sourceIndex boundary initialZero
    (Macro.Ingress.cut input 1 sourceStart)

variable (datum : Macro.Ingress.Datum input 1 sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input 1 (Macro.Ingress.cut input 1 sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

/-- Installing the raw input changes only the query epoch of this exact
external cut. Its occurrence and all old rows remain the original ones. -/
theorem the_registered_macro_input_keeps_that_exact_external_occurrence :
    (Macro.Ingress.root (review := review) input 1 sourceStart datum prefixLimit renewalLimit
      ).toAuthoritativeRoot.toLedgerRoot =
        (Macro.Ingress.frame input 1 sourceStart).native.root.toAuthoritativeRoot.toLedgerRoot ∧
    Macro.Ingress.sourceEvent (review := review) input 1 sourceStart datum prefixLimit renewalLimit =
      (Macro.Ingress.frame input 1 sourceStart).native.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        ((Macro.Ingress.frame input 1 sourceStart).temporal input) ∧
    (Macro.Ingress.registeredInput (review := review) input 1 sourceStart datum prefixLimit renewalLimit).query.raw =
      datum.reader ((Macro.Ingress.frame input 1 sourceStart).native.root.emitted
        (Macro.Ingress.frame input 1 sourceStart).visit.current) :=
  ⟨rfl, rfl, rfl⟩

/-- The real external source cut is the premise of the existing no-fresh
whole-ledger action. Its installed compiler, rather than a caller equation,
selects that very action and its literal target-next visit. -/
theorem the_external_cut_generates_the_original_macro_action :
    (Macro.Ingress.state (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader).compileInquiry
      (Macro.Ingress.registeredInput (review := review) input 1 sourceStart datum prefixLimit renewalLimit).query =
        .actualAction (Macro.Ingress.generated (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader) ∧
    (Macro.Ingress.generated (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader).target.targetAnswerAndNext.nextCurrent =
      ⟨Macro.Accounting.V (review := review) input 1 (Macro.Ingress.cut input 1 sourceStart) prefixLimit renewalLimit
          1 (Macro.Ingress.cut input 1 sourceStart) Physical.initial
          (Macro.Ingress.proposal (review := review) input 1 sourceStart datum prefixLimit renewalLimit) 0,
        (Macro.Ingress.targetRoot (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot,
        Macro.Ingress.nextVisit (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader⟩ :=
  ⟨rfl, Macro.Ingress.actual_action_returns_the_literal_next_visit (review := review)
    input 1 sourceStart datum prefixLimit renewalLimit reader⟩

theorem an_unrelated_raw_source_cannot_impersonate_the_external_input
    (other : Macro.Ingress.Datum input 1 sourceStart)
    (different : datum.reader ((Macro.Ingress.frame input 1 sourceStart).native.root.emitted
        (Macro.Ingress.frame input 1 sourceStart).visit.current) ≠
      other.reader ((Macro.Ingress.frame input 1 sourceStart).native.root.emitted
        (Macro.Ingress.frame input 1 sourceStart).visit.current)) :
    (Macro.Ingress.registeredInput (review := review) input 1 sourceStart datum prefixLimit renewalLimit).query.raw ≠
      (Macro.Ingress.registeredInput (review := review) input 1 sourceStart other prefixLimit renewalLimit).query.raw :=
  different

#print axioms the_programme_input_uses_the_existing_society_payment
#print axioms the_original_external_root_consumes_the_source_selected_programme
#print axioms the_macro_source_is_an_actual_external_payment_cut
#print axioms the_registered_macro_input_keeps_that_exact_external_occurrence
#print axioms the_external_cut_generates_the_original_macro_action
#print axioms an_unrelated_raw_source_cannot_impersonate_the_external_input

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External
