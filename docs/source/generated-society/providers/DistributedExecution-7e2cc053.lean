import SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Selection
import SaturationMonoid.ProcessGame.Society.PublicFunction.Compiler

/-! Distributed finite event programs. Sending takes a reading at the actual
send cut. Delivery may occur later, in any order and repeatedly. Activation
reads only that site's delivered signal. The source interpreter remains the
only mechanism that changes material inventory or financial claims. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed

open Institutions.Capitalism.Universal.Source.Program

universe u
variable {α : Type u}

def sequences (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun a => (sequences alphabet n).map (List.cons a))

theorem mem_sequences_iff (alphabet : List α) (n : Nat) (word : List α) :
    word ∈ sequences alphabet n ↔ word.length ≤ n ∧ ∀ a ∈ word, a ∈ alphabet := by
  induction n generalizing word with
  | zero => cases word <;> simp [sequences]
  | succ n ih =>
    cases word with
    | nil => simp [sequences]
    | cons a tail =>
      simp only [sequences, List.mem_cons, List.cons_ne_nil, false_or,
        List.mem_flatMap, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨head, inside, rest, generated, sameHead, sameTail⟩
        subst head; subst rest
        obtain ⟨bounded, supported⟩ := (ih tail).mp generated
        exact ⟨Nat.succ_le_succ bounded, by simpa using And.intro inside supported⟩
      · rintro ⟨bounded, supported⟩
        exact ⟨a, supported a (Or.inl rfl), tail,
          (ih tail).mpr ⟨Nat.le_of_succ_le_succ bounded, fun b h => supported b (Or.inr h)⟩, rfl, rfl⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

inductive Event (Party Good Port Technology Instrument : Type) (sites : Nat) where
  | adversary (request : Request Party Good Port Technology Instrument)
  | send (sender recipient : Fin sites)
  | deliver (address : Nat)
  | activate (site : Fin sites)

structure LocalSnapshot (Party Good Instrument : Type) where
  stock : Good → ℚ
  liabilities : Instrument → Party → ℚ
  claims : Instrument → Party → ℚ
  clock : ℚ
  round : Nat

structure Code (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  law : RawLaw Party Good Port Technology Instrument
  initial : RawCurrent Party Good Technology Instrument
  /-- Original requests interpreted by the source before any hidden history. -/
  bootstrap : RawEvent Party Good Port Technology Instrument := []
  task : PublicTaskSpec Party Good
  actions : List (Request Party Good Port Technology Instrument)
  actionLimit : Nat
  sites : Nat
  signals : Nat
  initialSignal : Fin signals
  siteParty : Fin sites → Party
  readLocal : Fin sites → LocalSnapshot Party Good Instrument → Fin signals
  memoryReady : Fin signals → Bool := fun _ => true
  /-- Local protocol memory changes only after its own paid read, paid receipt,
  or attempted action. Defaults retain the original memoryless protocol. -/
  afterSend : Fin sites → Fin sites → Fin signals → Fin signals → Fin signals := fun _ _ old _ => old
  afterDelivery : Fin sites → Fin sites → Fin signals → Fin signals → Fin signals := fun _ _ _ signal => signal
  afterAction : Fin sites → Fin signals → RawEvent Party Good Port Technology Instrument → Fin signals := fun _ old _ => old
  sendCost : Fin sites → Fin sites → RawEvent Party Good Port Technology Instrument := fun _ _ => []
  deliveryCost : Fin sites → RawEvent Party Good Port Technology Instrument := fun _ => []
  historyAlphabet : List (RawEvent Party Good Port Technology Instrument)
  historyLimit : Nat
  eventAlphabet : List (Event Party Good Port Technology Instrument sites)
  eventLimit : Nat
  eligible : List (Event Party Good Port Technology Instrument sites) → Bool
  parties : List Party
  goods : List Good
  instruments : List Instrument
  parties_cover : ∀ p, p ∈ parties
  goods_cover : ∀ g, g ∈ goods
  instruments_cover : ∀ i, i ∈ instruments

namespace Code

variable (code : Code Party Good Port Technology Instrument)

abbrev Key := Fin code.sites × Fin code.signals

def keys : List code.Key := (List.finRange code.sites).product (List.finRange code.signals)

theorem key_mem (key : code.Key) : key ∈ code.keys := by
  exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩

abbrev Policy := ∀ key ∈ code.keys, RawEvent Party Good Port Technology Instrument

def policies : List code.Policy := List.pi code.keys (fun _ => words code.actions code.actionLimit)

def action (policy : code.Policy) (site : Fin code.sites) (signal : Fin code.signals) :=
  if code.memoryReady signal then policy (site, signal) (code.key_mem _) else []

theorem every_local_policy_is_enumerated (policy : code.Policy)
    (supported : ∀ key inside, policy key inside ∈ words code.actions code.actionLimit) :
    policy ∈ code.policies := (List.mem_pi _ _).mpr supported

structure Packet where
  sender : Fin code.sites
  recipient : Fin code.sites
  signal : Fin code.signals
  sentAfter : Nat

structure Frame where
  word : RawEvent Party Good Port Technology Instrument
  sent : List code.Packet
  inbox : Fin code.sites → Fin code.signals
  localLegal : Bool

def start : code.Frame := ⟨[], [], fun _ => code.initialSignal, true⟩

def rawAt (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame) :=
  (code.law.execute initial 0 frame.word).final

def snapshot (site : Fin code.sites) (current : RawCurrent Party Good Technology Instrument) :
    LocalSnapshot Party Good Instrument :=
  ⟨current.stock (code.siteParty site), fun i p => current.claims i (code.siteParty site) p,
    fun i p => current.claims i p (code.siteParty site), current.clock, current.round⟩

theorem local_sensor_reads_only_its_own_snapshot (site : Fin code.sites)
    (first second : RawCurrent Party Good Technology Instrument)
    (stock : first.stock (code.siteParty site) = second.stock (code.siteParty site))
    (liabilities : (fun i p => first.claims i (code.siteParty site) p) =
      (fun i p => second.claims i (code.siteParty site) p))
    (claims : (fun i p => first.claims i p (code.siteParty site)) =
      (fun i p => second.claims i p (code.siteParty site)))
    (clock : first.clock = second.clock) (round : first.round = second.round) :
    code.readLocal site (code.snapshot site first) = code.readLocal site (code.snapshot site second) := by
  unfold snapshot
  rw [stock, liabilities, claims, clock, round]

def step (policy : code.Policy) (initial : RawCurrent Party Good Technology Instrument)
    (frame : code.Frame) : Event Party Good Port Technology Instrument code.sites → code.Frame
  | .adversary request => { frame with word := frame.word ++ [request] }
  | .send sender recipient =>
      let fee := code.sendCost sender recipient
      let paid := decide (∀ item ∈ code.law.rawItems (code.rawAt initial frame) fee,
        code.law.Valid item.before item.request)
      { frame with
        word := frame.word ++ fee
        localLegal := frame.localLegal && paid
        sent := if paid then frame.sent ++
          [⟨sender, recipient, code.readLocal sender (code.snapshot sender (code.rawAt initial frame)), frame.word.length⟩]
          else frame.sent
        inbox := if paid then (fun site => if site = sender then
          code.afterSend sender recipient (frame.inbox sender)
            (code.readLocal sender (code.snapshot sender (code.rawAt initial frame))) else frame.inbox site)
          else frame.inbox }
  | .deliver address => match frame.sent[address]? with
      | none => frame
      | some packet =>
          let fee := code.deliveryCost packet.recipient
          let paid := decide (∀ item ∈ code.law.rawItems (code.rawAt initial frame) fee,
            code.law.Valid item.before item.request)
          { frame with
            word := frame.word ++ fee
            localLegal := frame.localLegal && paid
            inbox := if paid then (fun site =>
              if site = packet.recipient then code.afterDelivery packet.recipient packet.sender
                (frame.inbox site) packet.signal else frame.inbox site) else frame.inbox }
  | .activate site =>
      let word := code.action policy site (frame.inbox site)
      { frame with
        word := frame.word ++ word
        inbox := fun other => if other = site then code.afterAction site (frame.inbox site) word else frame.inbox other
        localLegal := frame.localLegal && code.memoryReady (frame.inbox site) && decide (∀ item ∈ code.law.rawItems (code.rawAt initial frame) word,
          code.law.Valid item.before item.request) }

def replay (policy : code.Policy) (initial : RawCurrent Party Good Technology Instrument)
    (events : List (Event Party Good Port Technology Instrument code.sites)) : code.Frame :=
  events.foldl (code.step policy initial) code.start

theorem adversary_attempt_has_exact_raw_effect (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (request : Request Party Good Port Technology Instrument) :
    code.rawAt initial (code.step policy initial frame (.adversary request)) =
      code.law.step (code.rawAt initial frame) request := by
  change (code.law.execute initial 0 (frame.word ++ [request])).final = _
  rw [code.law.execute_append]
  rfl

theorem invalid_adversary_attempt_is_retained_but_has_no_material_effect (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (request : Request Party Good Port Technology Instrument)
    (refused : ¬ code.law.Valid (code.rawAt initial frame) request) :
    (code.step policy initial frame (.adversary request)).word = frame.word ++ [request] ∧
      code.rawAt initial (code.step policy initial frame (.adversary request)) = code.rawAt initial frame := by
  exact ⟨rfl, (code.adversary_attempt_has_exact_raw_effect policy initial frame request).trans
    (by simp only [RawLaw.step, if_neg refused])⟩

/-- Neither current global stock nor another mailbox is an activation input. -/
theorem same_delivered_signal_same_action (policy : code.Policy) (site : Fin code.sites)
    (first second : code.Frame) (same : first.inbox site = second.inbox site) :
    code.action policy site (first.inbox site) = code.action policy site (second.inbox site) :=
  congrArg (code.action policy site) same

theorem send_is_an_actual_local_reading (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (sender recipient : Fin code.sites)
    (paid : ∀ item ∈ code.law.rawItems (code.rawAt initial frame) (code.sendCost sender recipient),
      code.law.Valid item.before item.request) :
    (code.step policy initial frame (.send sender recipient)).sent = frame.sent ++
      [⟨sender, recipient, code.readLocal sender (code.snapshot sender (code.rawAt initial frame)), frame.word.length⟩] := by
  simp only [step, decide_eq_true paid, if_true]

theorem paid_send_updates_only_its_own_memory (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (sender recipient : Fin code.sites)
    (paid : ∀ item ∈ code.law.rawItems (code.rawAt initial frame) (code.sendCost sender recipient),
      code.law.Valid item.before item.request) :
    (code.step policy initial frame (.send sender recipient)).inbox sender =
      code.afterSend sender recipient (frame.inbox sender)
        (code.readLocal sender (code.snapshot sender (code.rawAt initial frame))) := by
  simp only [step, decide_eq_true paid, if_true]

theorem unpaid_send_cannot_update_memory_or_packets (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (sender recipient : Fin code.sites)
    (unpaid : ¬ ∀ item ∈ code.law.rawItems (code.rawAt initial frame) (code.sendCost sender recipient),
      code.law.Valid item.before item.request) :
    (code.step policy initial frame (.send sender recipient)).inbox = frame.inbox ∧
      (code.step policy initial frame (.send sender recipient)).sent = frame.sent := by
  simp only [step, decide_eq_false unpaid, Bool.false_eq_true, if_false, and_self]

theorem delivery_reads_only_an_already_sent_packet (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (address : Nat) (packet : code.Packet) (present : frame.sent[address]? = some packet)
    (paid : ∀ item ∈ code.law.rawItems (code.rawAt initial frame) (code.deliveryCost packet.recipient),
      code.law.Valid item.before item.request) :
    (code.step policy initial frame (.deliver address)).inbox packet.recipient =
      code.afterDelivery packet.recipient packet.sender (frame.inbox packet.recipient) packet.signal := by
  simp only [step, present, decide_eq_true paid, if_true]

def historyCurrent (history : List (RawEvent Party Good Port Technology Instrument)) :=
  history.foldl code.law.next (code.law.next code.initial [])

def historyLegal : RawCurrent Party Good Technology Instrument →
    List (RawEvent Party Good Port Technology Instrument) → Bool
  | _, [] => true
  | current, word :: rest => decide (∀ item ∈ code.law.rawItems current word,
      code.law.Valid item.before item.request) && historyLegal (code.law.next current word) rest

@[simp] def publicPrefix := if code.bootstrap = [] then [] else [code.bootstrap]

/-- Public original attempts are interpreted even when refused. Only the
hidden suffix is screened for legality after their actual effects. -/
def histories := ((sequences code.historyAlphabet code.historyLimit).filter
  (code.historyLegal (code.historyCurrent code.publicPrefix))).map
    (fun history => code.publicPrefix ++ history)

theorem public_prefix_is_an_actual_generated_history : code.publicPrefix ∈ code.histories := by
  apply List.mem_map.mpr
  refine ⟨[], List.mem_filter.mpr ⟨?_, rfl⟩, List.append_nil _⟩
  exact (mem_sequences_iff _ _ _).mpr ⟨Nat.zero_le _, fun _ member => (List.not_mem_nil member).elim⟩

def scripts := (sequences code.eventAlphabet code.eventLimit).filter code.eligible

abbrev Scenario := List (RawEvent Party Good Port Technology Instrument) ×
  List (Event Party Good Port Technology Instrument code.sites)

def scenarios : List code.Scenario := code.histories.product code.scripts

theorem every_legal_history_and_eligible_deviation_is_replayed
    (history : List (RawEvent Party Good Port Technology Instrument))
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (historyBound : history.length ≤ code.historyLimit)
    (historySupport : ∀ word ∈ history, word ∈ code.historyAlphabet)
    (legal : code.historyLegal (code.historyCurrent code.publicPrefix) history = true)
    (eventBound : events.length ≤ code.eventLimit)
    (eventSupport : ∀ event ∈ events, event ∈ code.eventAlphabet)
    (eligible : code.eligible events = true) : (code.publicPrefix ++ history, events) ∈ code.scenarios := by
  apply List.mem_product.mpr
  exact ⟨List.mem_map.mpr ⟨history, List.mem_filter.mpr
    ⟨(mem_sequences_iff _ _ _).mpr ⟨historyBound, historySupport⟩, legal⟩, rfl⟩,
    List.mem_filter.mpr ⟨(mem_sequences_iff _ _ _).mpr ⟨eventBound, eventSupport⟩, eligible⟩⟩

def executed (policy : code.Policy) (scenario : code.Scenario) :=
  code.replay policy (code.historyCurrent scenario.1) scenario.2

def feasible (policy : code.Policy) : Prop := ∀ scenario ∈ code.scenarios,
  (code.executed policy scenario).localLegal = true ∧
    ServiceAdequate code.law (code.historyCurrent scenario.1) code.task (code.executed policy scenario).word

instance (policy : code.Policy) : Decidable (code.feasible policy) := by unfold feasible; infer_instance

/-- The opponent may adapt to the complete event frame, including previous
actions and packets. This is stronger than restricting it to a local view. -/
abbrev Adversary := code.Frame → { event : Event Party Good Port Technology Instrument code.sites //
  event ∈ code.eventAlphabet }

def adversarialWord (policy : code.Policy) (initial : RawCurrent Party Good Technology Instrument)
    (opponent : code.Adversary) : Nat → code.Frame → List (Event Party Good Port Technology Instrument code.sites)
  | 0, _ => []
  | n + 1, frame =>
      let event := opponent frame
      event.val :: adversarialWord policy initial opponent n (code.step policy initial frame event.val)

theorem every_adaptive_adversary_generates_a_supported_word (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (opponent : code.Adversary)
    (count : Nat) (frame : code.Frame) :
    (code.adversarialWord policy initial opponent count frame).length = count ∧
      ∀ event ∈ code.adversarialWord policy initial opponent count frame, event ∈ code.eventAlphabet := by
  induction count generalizing frame with
  | zero => exact ⟨rfl, by simp [adversarialWord]⟩
  | succ count ih =>
    obtain ⟨length, supported⟩ := ih (code.step policy initial frame (opponent frame).val)
    constructor
    · simp only [adversarialWord, List.length_cons, length]
    · intro event inside
      rcases List.mem_cons.mp inside with same | later
      · exact same ▸ (opponent frame).property
      · exact supported event later

theorem feasible_against_every_adaptive_adversary (policy : code.Policy)
    (accepted : code.feasible policy)
    (history : List (RawEvent Party Good Port Technology Instrument)) (original : history ∈ code.histories)
    (opponent : code.Adversary) (count : Nat) (bounded : count ≤ code.eventLimit)
    (eligible : code.eligible (code.adversarialWord policy (code.historyCurrent history) opponent count code.start) = true) :
    let events := code.adversarialWord policy (code.historyCurrent history) opponent count code.start
    (code.replay policy (code.historyCurrent history) events).localLegal = true ∧
      ServiceAdequate code.law (code.historyCurrent history) code.task
        (code.replay policy (code.historyCurrent history) events).word := by
  dsimp only
  obtain ⟨length, supported⟩ := code.every_adaptive_adversary_generates_a_supported_word policy
    (code.historyCurrent history) opponent count code.start
  apply accepted (history, code.adversarialWord policy (code.historyCurrent history) opponent count code.start)
  apply List.mem_product.mpr
  exact ⟨original, List.mem_filter.mpr ⟨(mem_sequences_iff _ _ _).mpr ⟨by omega, supported⟩, eligible⟩⟩

end Code
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed
