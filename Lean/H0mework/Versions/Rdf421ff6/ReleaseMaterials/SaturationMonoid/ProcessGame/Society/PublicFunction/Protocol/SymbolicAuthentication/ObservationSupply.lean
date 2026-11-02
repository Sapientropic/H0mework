import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SupplyMenu

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ObservationSupply

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (law : StageReception.Law code) (start : Cursor code) (installed : List (Rule code))

def word (site : Fin code.sites) (signal : Fin code.signals) (rank : Nat) :=
  (SupplyMenu.supply (code := code) rank site).toList ++
    LocalRequestAuthentication.work vocabulary law start installed site signal

-- This is a source-menu restoration test, not a certificate of consensus.
def Restores (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (requests : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) : Prop :=
  (∀ item ∈ code.law.rawItems current requests, code.law.Valid item.before item.request) ∧
    ∀ request ∈ code.actions, code.law.Valid (code.law.next current requests) request
instance (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (requests : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    Decidable (Restores (code := code) current requests) := by unfold Restores; infer_instance

def accepts (site : Fin code.sites) (signal : Fin code.signals) (rank : Nat) : Bool :=
  decide (LocalRequestAuthentication.work vocabulary law start installed site signal ≠ [] ∧
    (SupplyMenu.supply (code := code) rank site).isSome ∧
    word vocabulary law start installed site signal rank ∈ words code.actions code.actionLimit) &&
  !(LocalRequestAuthentication.fibre vocabulary start installed site signal).isEmpty &&
  (LocalRequestAuthentication.fibre vocabulary start installed site signal).all fun entry =>
    decide (Restores (code := code) (EventStep.seed entry.cursor).current
      (word vocabulary law start installed site signal rank))

def select (site : Fin code.sites) (signal : Fin code.signals) : Option Nat :=
  (List.range (code.actions.length + 1)).find? (accepts vocabulary law start installed site signal)

def work (site : Fin code.sites) (signal : Fin code.signals) :=
  match select vocabulary law start installed site signal with
  | none => []
  | some rank => word vocabulary law start installed site signal rank

theorem selection_is_uniform_on_the_entire_local_observation
    (site : Fin code.sites) (left right : Fin code.signals) (same : left = right) :
    select vocabulary law start installed site left = select vocabulary law start installed site right :=
  congrArg (select vocabulary law start installed site) same

theorem chosen_word_restores_every_compatible_source_state
    (site : Fin code.sites) (signal : Fin code.signals) (rank : Nat)
    (chosen : select vocabulary law start installed site signal = some rank)
    (entry : RequestLocalDomain.Entry (code := code))
    (compatible : entry ∈ LocalRequestAuthentication.fibre vocabulary start installed site signal) :
    Restores (code := code) (EventStep.seed entry.cursor).current
      (word vocabulary law start installed site signal rank) := by
  have checked := List.find?_some chosen
  simp only [accepts, Bool.and_eq_true] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.2 entry compatible)

theorem chosen_word_is_supported (site : Fin code.sites) (signal : Fin code.signals) (rank : Nat)
    (chosen : select vocabulary law start installed site signal = some rank) :
    LocalRequestAuthentication.work vocabulary law start installed site signal ≠ [] ∧
      (SupplyMenu.supply (code := code) rank site).isSome ∧
      word vocabulary law start installed site signal rank ∈ words code.actions code.actionLimit := by
  have checked := List.find?_some chosen
  simp only [accepts, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1.1

theorem work_supported (site : Fin code.sites) (signal : Fin code.signals) :
    work vocabulary law start installed site signal ∈ words code.actions code.actionLimit := by
  unfold work
  cases chosen : select vocabulary law start installed site signal with
  | none => exact (mem_words_iff _ _ _).mpr (by simp)
  | some rank => exact (chosen_word_is_supported vocabulary law start installed site signal rank chosen).2.2

def protocol : Rule code where
  work := ⟨fun key _ => work vocabulary law start installed key.1 key.2, by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact work_supported vocabulary law start installed key.1 key.2⟩
  events := fun key _ => if work vocabulary law start installed key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

theorem every_compiled_rule_is_source_generated :
    protocol vocabulary law start installed ∈ rules code := every_rule_is_source_generated code _

theorem unready_records_cannot_generate_a_supply_word (site : Fin code.sites) (signal : Fin code.signals)
    (unready : code.memoryReady signal ≠ true) : work vocabulary law start installed site signal = [] := by
  have unreadable : RequestReadback.localRead (code := code) signal = none := by
    simp [RequestReadback.localRead, unready]
  have absent := RequestResponse.missing_local_content_produces_no_work site signal unreadable
  have original : LocalRequestAuthentication.work vocabulary law start installed site signal = [] := by
    simp only [LocalRequestAuthentication.work, absent, ite_self]
  have denied : select vocabulary law start installed site signal = none := by
    apply List.find?_eq_none.mpr
    intro rank _
    simp only [accepts, original, ne_eq, not_true_eq_false, false_and, decide_false, Bool.false_and,
      Bool.false_eq_true, not_false_eq_true]
  simp only [work, denied]

theorem an_owned_activation_submits_the_selected_local_word (cursor : Cursor code)
    (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material cursor (protocol vocabulary law start installed) rival) = some site) :
    (StageTrace.material cursor (protocol vocabulary law start installed) rival).submitted =
      work vocabulary law start installed site ((EventStep.seed cursor).frame.inbox site) := by
  rw [(StageTrace.an_owned_activation_submits_its_selected_work _ _ rival site owned).2]
  change (if code.memoryReady _ then work vocabulary law start installed site _ else []) = _
  split
  · rfl
  · exact (unready_records_cannot_generate_a_supply_word vocabulary law start installed site _ (by assumption)).symm

theorem actual_selected_word_restores_the_actual_source_menu
    (stages : List (EventHistory.Stage (code := code))) (site : Fin code.sites) (rank : Nat)
    (chosen : select vocabulary law start (stages.map Prod.fst) site
      (RetainedIntent.memory start stages site) = some rank) :
    Restores (code := code) (EventStep.seed (EventHistory.execute start stages)).current
      (word vocabulary law start (stages.map Prod.fst) site (RetainedIntent.memory start stages site) rank) := by
  obtain ⟨entry, generated, matched, _⟩ := RequestLocalDomain.actual_prefix_coverage vocabulary start stages
  have compatible : entry ∈ LocalRequestAuthentication.fibre vocabulary start (stages.map Prod.fst) site
      (RetainedIntent.memory start stages site) :=
    List.mem_filter.mpr ⟨generated, by simp only [LocalRequestAuthentication.reading, matched.state, beq_self_eq_true]⟩
  have restored := chosen_word_restores_every_compatible_source_state vocabulary law start _ site _ rank chosen entry compatible
  simpa only [matched.state] using restored

theorem a_selected_actual_activation_pays_the_whole_word_and_restores_the_source_menu
    (stages : List (EventHistory.Stage (code := code))) (rival : Opponent code)
    (site : Fin code.sites) (rank : Nat)
    (chosen : select vocabulary law start (stages.map Prod.fst) site
      (RetainedIntent.memory start stages site) = some rank)
    (owned : StageTrace.activation (StageTrace.material (EventHistory.execute start stages)
      (protocol vocabulary law start (stages.map Prod.fst)) rival) = some site) :
    Restores (code := code) (EventStep.seed (EventHistory.execute start stages)).current
      (StageTrace.material (EventHistory.execute start stages)
        (protocol vocabulary law start (stages.map Prod.fst)) rival).submitted := by
  rw [an_owned_activation_submits_the_selected_local_word vocabulary law start _ _ rival site owned]
  simp only [work, chosen]
  exact actual_selected_word_restores_the_actual_source_menu vocabulary law start stages site rank chosen

theorem a_nonempty_actual_word_keeps_the_paid_statement_and_own_supply
    (stages : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (needed : work vocabulary law start (stages.map Prod.fst) site (RetainedIntent.memory start stages site) ≠ []) :
    ∃ rank request,
      select vocabulary law start (stages.map Prod.fst) site (RetainedIntent.memory start stages site) = some rank ∧
      SupplyMenu.supply (code := code) rank site = some request ∧ request ∈ code.actions ∧
      request.signer = code.siteParty site ∧
      (∃ body ∈ RequestAttestation.ledger vocabulary start stages,
        RequestReadback.localRead (code := code) (RetainedIntent.memory start stages site) = some body.request ∧
        body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current) := by
  unfold work at needed
  cases chosen : select vocabulary law start (stages.map Prod.fst) site (RetainedIntent.memory start stages site) with
  | none => simp only [chosen] at needed; contradiction
  | some rank =>
    have checked := chosen_word_is_supported vocabulary law start _ site _ rank chosen
    obtain ⟨request, supplied⟩ := Option.isSome_iff_exists.mp checked.2.1
    have source := SupplyMenu.supply_has_its_actual_source_and_signer rank site request supplied
    exact ⟨rank, request, rfl, supplied, source.1, source.2.1,
      LocalRequestAuthentication.nonempty_work_requires_an_actual_owned_paid_source_statement
        vocabulary law start stages site checked.1⟩

theorem own_execution_is_invariant_under_hidden_history
    (ownerStart : Nat) (first second : Opponent code) (history : History) (past : Events code)
    (left right : code.Frame) (site : Fin code.sites)
    (owned : Distributed.Recall.Information.Agency.ownerAt code ownerStart history.length = some site)
    (same : left.inbox site = right.inbox site) :
    driver code ownerStart (protocol vocabulary law start installed) first history past left =
      driver code ownerStart (protocol vocabulary law start installed) second history past right :=
  own_action_uses_only_its_actual_local_record code ownerStart _ first second history past left right site owned same

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ObservationSupply
