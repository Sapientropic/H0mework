import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceValidity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalSupply

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code) (observed : List (EventHistory.Stage (code := code)))

def isOwnTransfer (site : Fin code.sites)
    (request : RequestAttestation.Request (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) : Bool :=
  decide (request.signer = code.siteParty site) && match request.operation with
    | .transfer sender _ _ => decide (sender = code.siteParty site)
    | _ => false

def supply (site : Fin code.sites) := code.actions.find? (isOwnTransfer site)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem supply_has_its_source_and_own_signer (site : Fin code.sites) (request)
    (made : supply site = some request) :
    request ∈ code.actions ∧ request.signer = code.siteParty site ∧
      ∃ recipient goods, request.operation = .transfer (code.siteParty site) recipient goods := by
  have supported := List.mem_of_find?_eq_some made
  have selected := List.find?_some made
  simp only [isOwnTransfer, Bool.and_eq_true, decide_eq_true_eq] at selected
  refine ⟨supported, selected.1, ?_⟩
  cases kind : request.operation <;> simp_all

def input (site : Fin code.sites) :=
  LocalRequestAuthentication.work vocabulary law start (observed.map Prod.fst) site
    (RetainedIntent.memory start observed site)

theorem nonempty_input_is_an_actual_owned_paid_source_statement (site : Fin code.sites)
    (needed : input vocabulary law start observed site ≠ []) :
    ∃ body ∈ RequestAttestation.ledger vocabulary start observed,
      RequestReadback.localRead (code := code) (RetainedIntent.memory start observed site) = some body.request ∧
      body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start observed)).current :=
  LocalRequestAuthentication.nonempty_work_requires_an_actual_owned_paid_source_statement vocabulary law start observed site needed

private theorem input_ready (site : Fin code.sites)
    (needed : input vocabulary law start observed site ≠ []) :
    code.memoryReady (RetainedIntent.memory start observed site) = true := by
  by_contra missing
  have noRead : RequestReadback.localRead (code := code) (RetainedIntent.memory start observed site) = none := by
    simp [RequestReadback.localRead, missing]
  have noWork := RequestResponse.missing_local_content_produces_no_work site _ noRead
  simp only [input, LocalRequestAuthentication.work, noWork, ite_self] at needed
  exact needed rfl

def work (site : Fin code.sites) (reading : Fin code.signals) :=
  let original := input vocabulary law start observed site
  let repaired := (supply site).toList ++ original
  if reading = RetainedIntent.memory start observed site ∧ original ≠ [] ∧ (supply site).isSome ∧
      repaired ∈ words code.actions code.actionLimit then repaired else []

theorem work_supported (site : Fin code.sites) (reading : Fin code.signals) :
    work vocabulary law start observed site reading ∈ words code.actions code.actionLimit := by
  dsimp only [work]
  split
  · exact ‹_ ∧ _ ∧ _ ∧ _›.2.2.2
  · exact (mem_words_iff _ _ _).mpr (by simp)

theorem nonempty_work_has_original_paid_content_and_source_supply
    (site : Fin code.sites) (reading : Fin code.signals)
    (needed : work vocabulary law start observed site reading ≠ []) :
    reading = RetainedIntent.memory start observed site ∧
    input vocabulary law start observed site ≠ [] ∧
    ∃ request, supply site = some request ∧ request ∈ code.actions ∧
      request.signer = code.siteParty site ∧
      work vocabulary law start observed site reading =
        request :: input vocabulary law start observed site := by
  dsimp only [work] at needed ⊢
  split at needed <;> try contradiction
  rename_i checked
  obtain ⟨request, made⟩ := Option.isSome_iff_exists.mp checked.2.2.1
  refine ⟨checked.1, checked.2.1, request, made,
    (supply_has_its_source_and_own_signer site request made).1,
    (supply_has_its_source_and_own_signer site request made).2.1, ?_⟩
  rw [if_pos checked]
  simp only [made, Option.toList_some, List.singleton_append]

def policy : code.Policy := fun key _ => work vocabulary law start observed key.1 key.2

def protocol : Rule code where
  work := ⟨policy vocabulary law start observed, by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact work_supported vocabulary law start observed key.1 key.2⟩
  events := fun key _ => if work vocabulary law start observed key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

theorem actual_supply_uses_only_the_local_word
    (cursor : Cursor code) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material cursor (protocol vocabulary law start observed) rival) = some site) :
    (StageTrace.material cursor (protocol vocabulary law start observed) rival).submitted =
      work vocabulary law start observed site ((EventStep.seed cursor).frame.inbox site) := by
  rw [(StageTrace.an_owned_activation_submits_its_selected_work _ _ _ site owned).2]
  change (if code.memoryReady _ then work vocabulary law start observed site _ else []) = _
  split
  · rfl
  · rename_i unready
    dsimp only [work]
    split
    · rename_i checked
      have ready := input_ready vocabulary law start observed site checked.2.1
      rw [checked.1, ready] at unready
      contradiction
    · rfl

def supplyStages (rival : Opponent code) :=
  List.replicate (min (2 * code.sites) (EventStep.seed (EventHistory.execute start observed)).remaining)
    (protocol vocabulary law start observed, rival)
def middle (rival : Opponent code) := observed ++ supplyStages vocabulary law start observed rival
def serviceStages (entry : List (EventHistory.Stage (code := code))) (rival : Opponent code) :=
  List.replicate (min (2 * code.sites)
    (EventStep.seed (EventHistory.execute start (middle vocabulary law start observed rival))).remaining)
    (RetainedIntent.protocol vocabulary encoding law start entry, rival)
def produce (entry : List (EventHistory.Stage (code := code))) (rival : Opponent code) :=
  middle vocabulary law start observed rival ++ serviceStages vocabulary encoding law start observed entry rival

theorem exact_source_service_clock (entry : List (EventHistory.Stage (code := code))) (rival : Opponent code) :
    observed <+: produce vocabulary encoding law start observed entry rival ∧
    (produce vocabulary encoding law start observed entry rival).length ≤ observed.length + 4 * code.sites := by
  constructor
  · exact (List.prefix_append _ _).trans (List.prefix_append _ _)
  · simp only [produce, middle, supplyStages, serviceStages, List.length_append, List.length_replicate]
    have first := Nat.min_le_left (2 * code.sites) (EventStep.seed (EventHistory.execute start observed)).remaining
    have second := Nat.min_le_left (2 * code.sites)
      (EventStep.seed (EventHistory.execute start (middle vocabulary law start observed rival))).remaining
    dsimp only [middle, supplyStages] at second
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalSupply
