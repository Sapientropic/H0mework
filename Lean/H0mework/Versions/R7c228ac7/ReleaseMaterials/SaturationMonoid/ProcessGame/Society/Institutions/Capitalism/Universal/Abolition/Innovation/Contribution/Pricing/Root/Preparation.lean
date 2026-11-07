import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Submission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Resign

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (mechanism : Trials.Mechanism Party Good Port Technology Instrument)

def sourceInput :=
  { Public.Scope.checkInput source.native.input with
    localAttempts := fun raw => (Public.Scope.checkInput source.native.input).localAttempts raw ++
      source.control.remaining ++
      (Abolition.Functions.Revision.Adaptive.consumedProposals source.native.actual.snapshot).flatten }

omit [DecidableEq Technology] in
theorem the_actual_remaining_programme_is_in_the_quote_catalogue
    (request : Request Party Good Port Technology Instrument) (original : request ∈ source.control.remaining) :
    request ∈ Material.Migration.sourceAlphabet (sourceInput source) source.raw := by
  simp only [Material.Migration.sourceAlphabet,sourceInput,List.mem_append]
  tauto

abbrev ScheduleAt := Source.Schedule (sourceInput source) source.raw source.members mechanism.code.actionLimit mechanism

structure Prepared where
  private mk ::
  schedule : ScheduleAt source mechanism
  nonempty : natureDomain schedule.programme ≠ []
  allBranches : ∀ nature ∈ natureDomain schedule.programme,
    Source.branchChecks schedule mechanism.investmentPort nature

inductive Preparation : Type
  | providerBlocked (failures : ∀ word ∈ Material.Migration.sourceWords (sourceInput source) source.raw mechanism.code.actionLimit,
      Outside.Issue (sourceInput source) source.raw source.members word)
  | payerBlocked (failures : ∀ word ∈ Material.Migration.sourceWords (sourceInput source) source.raw mechanism.code.actionLimit,
      Outside.Issue (sourceInput source) source.raw source.members word)
  | noForecast (schedule : ScheduleAt source mechanism) (empty : natureDomain schedule.programme = [])
  | riskBlocked (schedule : ScheduleAt source mechanism) (nature : schedule.programme.QuotedNature)
      (original : nature ∈ natureDomain schedule.programme)
      (failed : ¬ Source.branchChecks schedule mechanism.investmentPort nature)
  | ready (prepared : Prepared source mechanism)

/-- Preparation has no actual-nature input. Every quote is generated on the
current root's own law, raw state, actor census and source execution budget. -/
def prepare : Preparation source mechanism :=
  match Source.compileSchedule (sourceInput source) source.raw source.members mechanism.code.actionLimit mechanism with
  | .providerBlocked failures => .providerBlocked failures
  | .payerBlocked failures => .payerBlocked failures
  | .ready schedule =>
      if empty : natureDomain schedule.programme = [] then .noForecast schedule empty
      else match Source.preflight schedule mechanism.investmentPort with
      | .failure nature original failed => .riskBlocked schedule nature original failed
      | .clear allBranches => .ready ⟨schedule,empty,allBranches⟩

omit [DecidableEq Technology] in
theorem the_quote_reads_the_same_active_law_and_complete_actual_census :
    (sourceInput source).law = source.native.handlerFace.rootRead ∧
      source.members = Abolition.Root.Epoch.Interface.Actors.PublicCensus.parties source.native.input source.native.depth
        source.native.count source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.actual.snapshot :=
  ⟨rfl,rfl⟩

theorem the_proposed_initial_stock_cannot_refill_the_original_quote
    (prepared : Prepared source mechanism) :
    prepared.schedule.programme.code.initial = source.raw ∧
      prepared.schedule.programme.code.law = source.native.handlerFace.rootRead := ⟨rfl,rfl⟩

theorem preparation_has_no_unwitnessed_outside_or_loading_parameter
    (prepared : Prepared source mechanism) :
    prepared.schedule.provider.word ∈ Material.Migration.sourceWords (sourceInput source) source.raw mechanism.code.actionLimit ∧
      prepared.schedule.payer.word ∈ Material.Migration.sourceWords (sourceInput source) source.raw mechanism.code.actionLimit ∧
      (type_of% prepared.schedule.provider.checked) ∧ (type_of% prepared.schedule.payer.checked) :=
  ⟨prepared.schedule.provider.generated,prepared.schedule.payer.generated,
    prepared.schedule.provider.checked,prepared.schedule.payer.checked⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
