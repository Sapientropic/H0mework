import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Gate
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Eligibility
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Protection

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual (Script Input ReceiptAnswers)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ExposureGuard

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

def openContinuation : Probe (fun _ : Script Party Good Port Technology Instrument => True) :=
  fun _ => some ⟨trivial⟩

def originalVisit (loss : Reparation.Actual.Occurrence seed community) :
    Visit seed community (Occurrence.history loss) (fun _ => True) :=
  Visit.start (Occurrence.originState loss) (Occurrence.originState_origins loss) trivial

variable {anchor : Script Party Good Port Technology Instrument}
  (prior : Visit seed community anchor (fun _ => True)) (answers : ReceiptAnswers seed)
  (request : Input Party Good Port Technology Instrument)

abbrev selected :=
  prior.verdict answers (damageGate community) openContinuation request

/-- This is the least restriction on original authority that forbids
every new actual coercive loss at the selected material position. -/
theorem the_guard_forwards_exactly_the_safe_original_requests :
    request ∈ (selected prior answers request).emitted ↔
      Occurrence.EligibleAt community answers anchor prior.history request := by
  constructor
  · intro admitted
    exact ⟨((selected prior answers request).every_emitted_input_is_lawful request admitted).1,
      selected_input_has_no_actual_damage _ request admitted⟩
  · intro safe
    have exactRequest := the_original_gate_keeps_every_safe_admissible_input
      (community := community) (check := openContinuation) safe.1 safe.2 rfl
    unfold selected Visit.verdict
    rw [Visit.roster, exactRequest]
    exact List.mem_singleton_self _

private def selectedState :=
  Occurrence.writeAfter answers prior.state (selected prior answers request).emitted

/-- Both the original decision and its exact effect are written on the
native successor. The original dual-signed allocator consumes every
selected material position before this disposition is read. -/
def record :=
  Installation.Core.publish (selectedState prior answers request) (selected prior answers request) true

def next : Visit seed community anchor (fun _ => True) :=
  let disposition := selected prior answers request
  ⟨prior.history ++ disposition.emitted, prior.original.trans (List.prefix_append _ _),
    (record prior answers request).state,
    Occurrence.writeAfter_origins answers prior.state prior.origins disposition.emitted, trivial⟩

theorem next_reads_the_actual_original_disposition :
    (record prior answers request).read = selected prior answers request :=
  rfl

theorem next_keeps_exactly_the_original_loss_addresses :
    (next prior answers request).state.stack.balances.map Prod.fst = prior.state.stack.balances.map Prod.fst := by
  rw [(next prior answers request).origins, prior.origins]
  exact the_selected_suffix_preserves_all_original_loss_addresses (selected prior answers request)

theorem next_is_the_whole_write_at_the_native_successor :
    let prepared := selectedState prior answers request
    let action := Installation.Core.action prepared (selected prior answers request) true
    (⟨prepared.world, action.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      (next prior answers request).state.resident.erase :=
  Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _

theorem any_safe_original_admission_is_contained_in_the_guard
    (other : Input Party Good Port Technology Instrument → Prop)
    (lawful : ∀ input, other input → Occurrence.EligibleAt community answers anchor prior.history input)
    (permits : other request) :
    request ∈ (selected prior answers request).emitted :=
  (the_guard_forwards_exactly_the_safe_original_requests prior answers request).mpr (lawful request permits)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Protection
