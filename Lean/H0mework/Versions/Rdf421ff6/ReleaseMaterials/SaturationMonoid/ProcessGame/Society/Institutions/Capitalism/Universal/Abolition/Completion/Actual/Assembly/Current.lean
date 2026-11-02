import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite.NoCapture
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future.Preferred

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Macro.Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "count" => Macro.Ingress.cut input depth sourceStart
local notation "current" => Macro.Runtime.actualFrame (review := review)
  input depth sourceStart datum prefixLimit renewalLimit reader

/-- Every field concerns this one actual registered history. The public
fields require equality to its current, so no caller-selected frame, root,
actor census or finished future can fill a port. -/
structure CapitalTerminationAndFutureExpansionAt (tick : Nat) : Prop where
  noAbsorbingCapitalFinality :
    ¬ Finite.LegallyAdmittedAbsorbingCapitalism input depth sourceStart datum prefixLimit renewalLimit reader review tick
  forcedFiniteReview : type_of% (Finite.every_actual_current_has_a_finite_forced_review_cone
    input depth sourceStart datum prefixLimit renewalLimit reader review tick)
  actualEngineCurrent :
    (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + 1)).engine.node =
      .active (current tick).presentation
  wholeLedgerGeneratedNext : type_of% (Macro.Runtime.each_actual_attempt_has_the_original_complete_next
    (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
      (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + 1)))
  noAlternativeOffLedgerNext : ∀ occurrence : InputRuntime.Occurrence
      (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + 1)),
    occurrence.next.engine.node = .active (current (tick + 1)).presentation
  publicTail : ∀ (origin : Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit depth count)
      (admission : Functions.Revision.InitialAdmissionAt origin)
      (frame : Macro.Public.Runtime.Frame origin admission)
      (selected : current tick = .enacted origin admission frame) (steps : Nat)
      (word : RawEvent Party Good Port Technology Instrument),
    type_of% (Capital.ending_new_capital_relations_keeps_every_original_native_claim_and_history
      input depth sourceStart datum prefixLimit renewalLimit reader review frame tick selected steps word)
  publicCurrentAudit : ∀ (origin : Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit depth count)
      (admission : Functions.Revision.InitialAdmissionAt origin)
      (frame : Macro.Public.Runtime.Frame origin admission),
    current tick = .enacted origin admission frame →
      type_of% (Dividend.Root.the_existing_root_classifies_the_full_account_face_as_active frame) ∧
      type_of% (Dividend.Root.the_root_read_keeps_its_exact_current_window_and_full_native_account frame) ∧
      type_of% (Dividend.Root.the_installed_root_assessment_generates_strict_full_gain_or_its_original_issue frame)
  paidIndependentFuture : ∀ (origin : Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit depth count)
      (admission : Functions.Revision.InitialAdmissionAt origin)
      (frame : Macro.Public.Runtime.Frame origin admission)
      (selected : current tick = .enacted origin admission frame)
      (complete : ¬ frame.HasWork) (automatic : Macro.Runtime.originalProposal frame = .advance),
    type_of% (Future.every_actual_automatic_boundary_generates_paid_life_or_a_visible_unpaid_obstruction
      datum reader frame tick selected complete automatic)
  actualPreferredFuture : ∀ (origin : Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit depth count)
      (admission : Functions.Revision.InitialAdmissionAt origin)
      (frame : Macro.Public.Runtime.Frame origin admission)
      (selected : current tick = .enacted origin admission frame)
      (complete : ¬ frame.HasWork) (automatic : Macro.Runtime.originalProposal frame = .advance),
    type_of% (Future.the_actual_boundary_executes_a_strict_full_account_extension_whenever_the_source_has_one
      datum reader frame tick selected complete automatic)

theorem the_original_root_consumes_capital_termination_and_social_future_expansion (tick : Nat) :
    CapitalTerminationAndFutureExpansionAt input depth sourceStart datum prefixLimit renewalLimit reader review tick where
  noAbsorbingCapitalFinality := Finite.capitalism_cannot_obtain_a_legally_admitted_absorbing_finality
    input depth sourceStart datum prefixLimit renewalLimit reader review tick
  forcedFiniteReview := Finite.every_actual_current_has_a_finite_forced_review_cone
    input depth sourceStart datum prefixLimit renewalLimit reader review tick
  actualEngineCurrent := Macro.Runtime.run_is_the_original_registered_history (review := review)
    input depth sourceStart datum prefixLimit renewalLimit reader tick
  wholeLedgerGeneratedNext := Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := review)
    input depth sourceStart datum prefixLimit renewalLimit reader _
  noAlternativeOffLedgerNext := fun occurrence => Macro.Runtime.actual_next (review := review)
    input depth sourceStart datum prefixLimit renewalLimit reader tick _
    (Macro.Runtime.run_is_the_original_registered_history (review := review)
      input depth sourceStart datum prefixLimit renewalLimit reader tick) occurrence
  publicTail := fun _origin _admission frame selected steps word =>
    Capital.ending_new_capital_relations_keeps_every_original_native_claim_and_history
      input depth sourceStart datum prefixLimit renewalLimit reader review frame tick selected steps word
  publicCurrentAudit := fun _origin _admission frame _selected =>
    ⟨Dividend.Root.the_existing_root_classifies_the_full_account_face_as_active frame,
      Dividend.Root.the_root_read_keeps_its_exact_current_window_and_full_native_account frame,
      Dividend.Root.the_installed_root_assessment_generates_strict_full_gain_or_its_original_issue frame⟩
  paidIndependentFuture := fun _origin _admission frame selected complete automatic =>
    Future.every_actual_automatic_boundary_generates_paid_life_or_a_visible_unpaid_obstruction
      datum reader frame tick selected complete automatic
  actualPreferredFuture := fun _origin _admission frame selected complete automatic =>
    Future.the_actual_boundary_executes_a_strict_full_account_extension_whenever_the_source_has_one
      datum reader frame tick selected complete automatic

#print axioms the_original_root_consumes_capital_termination_and_social_future_expansion

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
