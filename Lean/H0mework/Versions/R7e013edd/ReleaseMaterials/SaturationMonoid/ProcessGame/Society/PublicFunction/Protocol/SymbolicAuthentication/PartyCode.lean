import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyControls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCode
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction
open Repayment.Recovery (Good)
open WholePartyLift
abbrev OldCode := Code OldParty Good OldPort OldState Unit
abbrev NewCode := Code WholeCursorLaw.Party Good WholeCursorLaw.Port NewState Unit

def unstate (whole : NewState) : OldState :=
  ⟨whole.technology,whole.version,whole.holder.bind WholeCursorLaw.party?,
    whole.offered.bind WholeCursorLaw.party?,whole.last.bind WholePartySource.command?⟩

theorem unstate_state (old : OldState) : unstate (state old) = old := by
  cases old with
  | mk technology version holder offered last =>
    cases holder <;> cases offered <;> cases last with
    | none => rfl
    | some cmd => cases cmd <;> rfl

def operation? : Operation WholeCursorLaw.Party Good NewState Unit → Option (Operation OldParty Good OldState Unit)
  | .produce actor => return .produce (← WholeCursorLaw.party? actor)
  | .transfer sender recipient goods => return .transfer (← WholeCursorLaw.party? sender) (← WholeCursorLaw.party? recipient) goods
  | .use actor goods purpose => return .use (← WholeCursorLaw.party? actor) goods purpose
  | .issue code debtor creditor quantity => return .issue code (← WholeCursorLaw.party? debtor) (← WholeCursorLaw.party? creditor) quantity
  | .assign code debtor sender recipient quantity => return .assign code (← WholeCursorLaw.party? debtor) (← WholeCursorLaw.party? sender) (← WholeCursorLaw.party? recipient) quantity
  | .settle code debtor creditor quantity => return .settle code (← WholeCursorLaw.party? debtor) (← WholeCursorLaw.party? creditor) quantity
  | .revise actor target => if state (unstate target) = target then return .revise (← WholeCursorLaw.party? actor) (unstate target) else none
  | .present => some .present

-- Off-image actors, ports and mandate targets are rejected, rather than given an old identity.
def decode (whole : WholeCursorLaw.Action) : Option OldAction := do
  return ⟨← WholeCursorLaw.party? whole.signer,← whole.consents.mapM WholeCursorLaw.party?,
    ← WholeCursorLaw.port? whole.purpose,← whole.gates.mapM WholeCursorLaw.port?,← operation? whole.operation⟩

theorem decode_request (old : OldAction) : decode (request old) = some old := by
  rcases old with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> simp [decode,request,operation,operation?,WholeCursorLaw.party?,WholeCursorLaw.port?,
    List.mapM_map,Function.comp_def,mapM_some,unstate_state]

def unword (whole : List WholeCursorLaw.Action) := whole.filterMap decode

theorem unword_word (word : List OldAction) : unword (word.map request) = word := by
  simp [unword,List.filterMap_map,decode_request]

def word? (whole : List WholeCursorLaw.Action) := whole.mapM decode

theorem word_word (word : List OldAction) : word? (word.map request) = some word := by
  simp [word?,List.mapM_map,Function.comp_def,decode_request,mapM_some]

def history? (whole : List (List WholeCursorLaw.Action)) := whole.mapM word?

theorem history_history (history : List (List OldAction)) :
    history? (history.map (List.map request)) = some history := by
  simp [history?,List.mapM_map,Function.comp_def,word_word,mapM_some]

def event {sites : Nat} : Event OldParty Good OldPort OldState Unit sites →
    Event WholeCursorLaw.Party Good WholeCursorLaw.Port NewState Unit sites
  | .adversary old => .adversary (request old)
  | .send sender recipient => .send sender recipient
  | .deliver address => .deliver address
  | .activate site => .activate site

def event? {sites : Nat} : Event WholeCursorLaw.Party Good WholeCursorLaw.Port NewState Unit sites →
    Option (Event OldParty Good OldPort OldState Unit sites)
  | .adversary whole => return .adversary (← decode whole)
  | .send sender recipient => some (.send sender recipient)
  | .deliver address => some (.deliver address)
  | .activate site => some (.activate site)

theorem event_event {sites : Nat} (old : Event OldParty Good OldPort OldState Unit sites) : event? (event old) = some old := by
  cases old <;> simp [event?,event,decode_request]

def events? {sites : Nat} (events : List (Event WholeCursorLaw.Party Good WholeCursorLaw.Port NewState Unit sites)) := events.mapM event?

theorem events_events {sites : Nat} (old : List (Event OldParty Good OldPort OldState Unit sites)) :
    events? (old.map event) = some old := by
  simp [events?,List.mapM_map,Function.comp_def,event_event,mapM_some]

def snapshot (whole : LocalSnapshot WholeCursorLaw.Party Good Unit) : LocalSnapshot OldParty Good Unit :=
  ⟨whole.stock,fun instrument actor => whole.liabilities instrument (.inl actor),
    fun instrument actor => whole.claims instrument (.inl actor),whole.clock,whole.round⟩

def task (old : PublicTaskSpec OldParty Good) : PublicTaskSpec WholeCursorLaw.Party Good :=
  ⟨old.slots.map (fun slot => ⟨.inl slot.bearer,slot.goods,slot.purpose⟩),old.earliest,old.deadline,by
    obtain ⟨slot,member,requirement,present,positive⟩ := old.demand
    exact ⟨⟨.inl slot.bearer,slot.goods,slot.purpose⟩,List.mem_map.mpr ⟨slot,member,rfl⟩,requirement,present,positive⟩⟩

def code (old : OldCode) (outside : Good → ℚ) : NewCode where
  law := newLaw
  initial := current old.initial outside
  bootstrap := old.bootstrap.map request
  task := task old.task
  actions := old.actions.map request
  actionLimit := old.actionLimit
  sites := old.sites
  signals := old.signals
  initialSignal := old.initialSignal
  siteParty := fun site => .inl (old.siteParty site)
  readLocal := fun site whole => old.readLocal site (snapshot whole)
  memoryReady := old.memoryReady
  afterSend := old.afterSend
  afterDelivery := old.afterDelivery
  afterAction := fun site signal whole => match word? whole with
    | some word => old.afterAction site signal word
    | none => signal
  sendCost := fun sender recipient => (old.sendCost sender recipient).map request
  deliveryCost := fun recipient => (old.deliveryCost recipient).map request
  historyAlphabet := old.historyAlphabet.map (List.map request)
  historyLimit := old.historyLimit
  eventAlphabet := old.eventAlphabet.map event
  eventLimit := old.eventLimit
  eligible := fun whole => match events? whole with | some events => old.eligible events | none => false
  parties := old.parties.map Sum.inl ++ [.inr ()]
  goods := old.goods
  instruments := old.instruments
  parties_cover := by
    intro actor
    cases actor with
    | inl actor => exact List.mem_append_left _ (List.mem_map.mpr ⟨actor,old.parties_cover actor,rfl⟩)
    | inr actor => cases actor;exact List.mem_append_right _ List.mem_cons_self
  goods_cover := old.goods_cover
  instruments_cover := old.instruments_cover

variable (old : OldCode) (outside : Good → ℚ)

def policy (p : old.Policy) : (code old outside).Policy := fun key inside => (p key inside).map request

theorem generated (p : old.Policy) (member : p ∈ old.policies) : policy old outside p ∈ (code old outside).policies := by
  apply (code old outside).every_local_policy_is_enumerated
  intro key inside
  obtain ⟨bounded,supported⟩ := (mem_words_iff _ _ _).mp ((List.mem_pi _ _).mp member key inside)
  exact (mem_words_iff _ _ _).mpr ⟨by simpa [policy,code] using bounded,
    fun action present => by
      obtain ⟨original,inside,rfl⟩ := List.mem_map.mp present
      exact List.mem_map.mpr ⟨original,supported original inside,rfl⟩⟩

theorem paid (same : old.law = oldLaw) (here : OldCurrent) (word : List OldAction) :
    (∀ item ∈ newLaw.rawItems (current here outside) (word.map request), newLaw.Valid item.before item.request) ↔
      ∀ item ∈ old.law.rawItems here word, old.law.Valid item.before item.request := by
  rw [same]
  change (∀ item ∈ (newLaw.execute (current here outside) 0 (word.map request)).items, _) ↔ _
  rw [WholePartyExecution.execute]
  simp only [List.forall_mem_map,WholePartyExecution.item,WholePartyLift.valid,RawLaw.rawItems]

theorem historyCurrent (same : old.law = oldLaw) (history : List (List OldAction)) :
    (code old outside).historyCurrent (history.map (List.map request)) = current (old.historyCurrent history) outside := by
  have fold : ∀ (history : List (List OldAction)) here,
      (history.map (List.map request)).foldl newLaw.next (current here outside) =
        current (history.foldl oldLaw.next here) outside := by
    intro history here
    induction history generalizing here with
    | nil => rfl
    | cons head tail ih => simp only [List.map_cons,List.foldl_cons,WholePartyExecution.next,ih]
  change (history.map (List.map request)).foldl newLaw.next
    (newLaw.next (current old.initial outside) ([].map request)) =
      current (history.foldl old.law.next (old.law.next old.initial [])) outside
  rw [same,WholePartyExecution.next,fold]

theorem historyLegal (same : old.law = oldLaw) (here : OldCurrent) (history : List (List OldAction)) :
    (code old outside).historyLegal (current here outside) (history.map (List.map request)) = old.historyLegal here history := by
  induction history generalizing here with
  | nil => rfl
  | cons head tail ih =>
      change (decide (∀ item ∈ newLaw.rawItems (current here outside) (head.map request),newLaw.Valid item.before item.request) &&
        (code old outside).historyLegal (newLaw.next (current here outside) (head.map request)) (tail.map (List.map request))) = _
      rw [WholePartyExecution.next,← same,ih]
      exact congrArg (fun b => b && old.historyLegal (old.law.next here head) tail)
        (Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using paid old outside same here head))

theorem publicPrefix : (code old outside).publicPrefix = old.publicPrefix.map (List.map request) := by
  simp only [Code.publicPrefix,code,List.map_eq_nil_iff]
  split <;> rfl

theorem histories (same : old.law = oldLaw) (history : List (List OldAction)) (member : history ∈ old.histories) :
    history.map (List.map request) ∈ (code old outside).histories := by
  change history ∈ ((sequences old.historyAlphabet old.historyLimit).filter
    (old.historyLegal (old.historyCurrent old.publicPrefix))).map (fun hidden => old.publicPrefix ++ hidden) at member
  obtain ⟨hidden,inHidden,shape⟩ := List.mem_map.mp member
  subst history
  obtain ⟨supported,legal⟩ := List.mem_filter.mp inHidden
  obtain ⟨bounded,inside⟩ := (mem_sequences_iff _ _ _).mp supported
  apply List.mem_map.mpr
  refine ⟨hidden.map (List.map request),List.mem_filter.mpr ⟨?_,?_⟩,?_⟩
  · exact (mem_sequences_iff _ _ _).mpr ⟨by simpa [code] using bounded,fun word present => by
      obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
      exact List.mem_map.mpr ⟨original,inside original member,rfl⟩⟩
  · rw [publicPrefix,historyCurrent old outside same,historyLegal old outside same]
    exact legal
  · rw [publicPrefix,List.map_append]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCode
