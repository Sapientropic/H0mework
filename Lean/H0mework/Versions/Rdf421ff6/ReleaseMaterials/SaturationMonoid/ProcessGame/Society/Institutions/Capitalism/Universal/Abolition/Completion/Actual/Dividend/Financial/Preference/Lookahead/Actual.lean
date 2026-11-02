import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Initial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Snapshot
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Adaptive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Lookahead.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Registered Source.Program Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

section Initial

variable {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  (package : Macro.Inquiry.Package (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition)
  (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root visit
    (package.frame.entry visit.current))
  (germ : Macro.Raw.GermAt package.source package.sourceData package.reader visit.current)

local notation "origin₀" => Enactment.Inquiry.contextAt package visit authority germ

theorem initial_source_selection_has_a_future_at_its_actual_first_snapshot
    (available : ∃ word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit
        (InitialAdmission.sourceSnapshot origin₀),
      Preference.Checks input depth count prefixLimit renewalLimit (InitialAdmission.sourceSnapshot origin₀) word ∧
        Preference.PostFeasible input depth count prefixLimit renewalLimit (InitialAdmission.sourceSnapshot origin₀) word) :
    ∃ plan, ∃ source : InitialAdmission.inspectPublic origin₀ = .accepted plan,
      InitialAdmission.select origin₀ = .admitted (.publicPlan plan source) ∧
      Available input depth count prefixLimit renewalLimit (origin₀).germ.snapshot.past
        (Macro.Public.Runtime.Frame.initial package visit authority germ (.publicPlan plan source)).snapshot := by
  obtain ⟨selection, preferred, future⟩ := Preference.an_available_complete_replacement_is_selected
    input depth count prefixLimit renewalLimit (InitialAdmission.sourceSnapshot origin₀) available
  obtain ⟨plan, source, chosen, _strict⟩ :=
    InitialAdmission.an_available_strict_plan_is_selected_before_the_old_authority origin₀ selection preferred
  obtain ⟨expected, produced, wordExact, _full⟩ :=
    PublicPlan.an_available_full_account_improvement_is_the_actual_public_plan input depth count
      prefixLimit renewalLimit (InitialAdmission.sourceSnapshot origin₀) selection preferred
  have same : plan = expected := PublicPlan.Outcome.accepted.inj (source.symm.trans produced)
  have rawExact : plan.rawWord = selection.rawWord := (congrArg PublicPlan.Plan.rawWord same).trans wordExact
  refine ⟨plan, source, chosen, ?_⟩
  rw [Macro.Public.Runtime.Frame.snapshot_is_the_literal_after]
  change Preference.PostFeasible input depth count prefixLimit renewalLimit
    (InitialAdmission.sourceSnapshot origin₀) plan.rawWord
  rw [rawExact]
  exact future

end Initial

section Renewal

variable {sourceStart : Nat}
  (datum : Macro.Ingress.Datum input depth sourceStart)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceStart))
  {origin : Context (input := input) (review := review) depth (Macro.Ingress.cut input depth sourceStart)
    prefixLimit renewalLimit depth (Macro.Ingress.cut input depth sourceStart)}
  {admission : InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
  (selected : Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick =
    .enacted origin admission frame)

include selected

theorem renewal_source_selection_has_a_future_at_its_actual_next_snapshot
    (complete : ¬ frame.HasWork) (automatic : Macro.Runtime.originalProposal frame = .advance)
    (available : ∃ word ∈ Adaptive.candidates input depth (Macro.Ingress.cut input depth sourceStart)
        prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot,
      Renewal.Checks input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot word ∧
      Renewal.PostFeasible input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot word) :
    ∃ plan, Adaptive.compile input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot = .accepted plan ∧
      frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.execute plan.rawWord)) ∧
      Available input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
        origin.germ.snapshot.past frame.next.snapshot := by
  obtain ⟨selection, preferred, future⟩ := Renewal.an_available_complete_extension_is_selected
    input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot available
  obtain ⟨plan, produced, wordExact, _strict⟩ := Adaptive.an_available_full_account_extension_is_the_actual_renewal_plan
    input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot selection preferred
  obtain ⟨actualPlan, actualSource, next, _account⟩ :=
    Macro.Runtime.the_actual_complete_source_executes_the_selected_period datum reader frame tick selected complete automatic
      ⟨selection.rawWord, selection.generated, selection.checked⟩
  have same : actualPlan = plan := Adaptive.Outcome.accepted.inj (actualSource.symm.trans produced)
  cases same
  refine ⟨plan, actualSource, next, ?_⟩
  rw [next]
  change Renewal.PostFeasible input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
    origin.germ.snapshot.past frame.snapshot plan.rawWord
  rw [wordExact]
  exact future

end Renewal

#print axioms initial_source_selection_has_a_future_at_its_actual_first_snapshot
#print axioms renewal_source_selection_has_a_future_at_its_actual_next_snapshot

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Lookahead.Runtime
