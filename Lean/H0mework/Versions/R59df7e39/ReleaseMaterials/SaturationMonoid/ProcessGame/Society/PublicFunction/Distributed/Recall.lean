import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Observation

/-! Source-generated finite local recall. Paid readings, addressed receipts and
own attempted words generate lossless local memory and the existing finite
policy domain. Overflow retains an explicit obstruction and blocks work. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : Code Party Good Port Technology Instrument)

inductive LocalNotice (Word : Type) (sites signals : Nat) where
  | sent (recipient : Fin sites) (signal : Fin signals)
  | received (sender : Fin sites) (signal : Fin signals)
  | attempted (word : Word)
  deriving DecidableEq

abbrev Notice := LocalNotice (RawEvent Party Good Port Technology Instrument) base.sites base.signals

def alphabet : List (Notice base) :=
  ((List.finRange base.sites).product (List.finRange base.signals)).flatMap
    (fun pair => [.sent pair.1 pair.2, .received pair.1 pair.2]) ++
    (words base.actions base.actionLimit).map LocalNotice.attempted

def memories (capacity : Nat) := sequences (alphabet base) capacity

def width (capacity : Nat) := base.signals + (memories base capacity).length + 1

def encode (capacity : Nat) (history : List (Notice base)) : Fin (width base capacity) :=
  ⟨base.signals + (memories base capacity).idxOf history, by
    have := List.idxOf_le_length (l := memories base capacity) (a := history)
    unfold width
    omega⟩

def overflow (capacity : Nat) : Fin (width base capacity) :=
  ⟨base.signals + (memories base capacity).length, by unfold width; omega⟩

def decode (capacity : Nat) (state : Fin (width base capacity)) : Option (List (Notice base)) :=
  if base.signals ≤ state.val then (memories base capacity)[state.val - base.signals]? else none

theorem decode_encode (capacity : Nat) (history : List (Notice base))
    (generated : history ∈ memories base capacity) :
    decode base capacity (encode base capacity history) = some history := by
  simp only [decode, encode, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
  exact List.getElem?_idxOf generated

omit [DecidableEq Port] [DecidableEq Technology] in
theorem decode_overflow (capacity : Nat) :
    decode base capacity (overflow base capacity) = none := by
  simp [decode, overflow]

def remember (capacity : Nat) (state : Fin (width base capacity)) (notice : Notice base) :
    Fin (width base capacity) :=
  match decode base capacity state with
  | none => overflow base capacity
  | some history => encode base capacity (history ++ [notice])

theorem actual_notice_extends_the_entire_local_history (capacity : Nat)
    (history : List (Notice base)) (notice : Notice base)
    (generated : history ∈ memories base capacity)
    (room : history.length < capacity) (supported : notice ∈ alphabet base) :
    decode base capacity (remember base capacity (encode base capacity history) notice) =
      some (history ++ [notice]) := by
  rw [remember, decode_encode base capacity history generated]
  apply decode_encode
  obtain ⟨bounded, inside⟩ := (mem_sequences_iff _ _ _).mp generated
  apply (mem_sequences_iff _ _ _).mpr
  constructor
  · simpa using (show history.length + 1 ≤ capacity by omega)
  · intro atom member
    rcases List.mem_append.mp member with old | fresh
    · exact inside atom old
    · exact (List.mem_singleton.mp fresh) ▸ supported

theorem exhausted_memory_is_an_explicit_obstruction (capacity : Nat)
    (history : List (Notice base)) (notice : Notice base)
    (generated : history ∈ memories base capacity) (full : history.length = capacity) :
    remember base capacity (encode base capacity history) notice = overflow base capacity := by
  rw [remember, decode_encode base capacity history generated]
  have absent : history ++ [notice] ∉ memories base capacity := by
    intro member
    have := ((mem_sequences_iff _ _ _).mp member).1
    simp only [List.length_append, List.length_singleton, full] at this
    omega
  simp only [encode, overflow, List.idxOf_eq_length_iff.mpr absent]

theorem overflow_never_silently_restarts (capacity : Nat) (notice : Notice base) :
    remember base capacity (overflow base capacity) notice = overflow base capacity := by
  rw [remember, decode_overflow]

def sensor (capacity : Nat) (signal : Fin base.signals) : Fin (width base capacity) :=
  ⟨signal.val, by have := signal.isLt; unfold width; omega⟩

def signal (capacity : Nat) (packet : Fin (width base capacity)) : Fin base.signals :=
  if inside : packet.val < base.signals then ⟨packet.val, inside⟩ else base.initialSignal

omit [DecidableEq Port] [DecidableEq Technology] in
theorem sensor_packet_preserves_the_actual_reading (capacity : Nat) (value : Fin base.signals) :
    signal base capacity (sensor base capacity value) = value := by
  simp only [signal, sensor, value.isLt, ↓reduceDIte]

abbrev lift (capacity : Nat) : Code Party Good Port Technology Instrument :=
  { base with
    signals := width base capacity
    initialSignal := encode base capacity []
    memoryReady := fun state => (decode base capacity state).isSome
    readLocal := fun site snapshot => sensor base capacity (base.readLocal site snapshot)
    afterSend := fun _ recipient old reading =>
      remember base capacity old (.sent recipient (signal base capacity reading))
    afterDelivery := fun _ sender old reading =>
      remember base capacity old (.received sender (signal base capacity reading))
    afterAction := fun _ old word => remember base capacity old (.attempted word) }

theorem lifting_preserves_the_original_physical_and_historical_domain (capacity : Nat) :
    (lift base capacity).law = base.law ∧
      (lift base capacity).initial = base.initial ∧
      (lift base capacity).histories = base.histories ∧
      (lift base capacity).eventAlphabet = base.eventAlphabet ∧
      (lift base capacity).sendCost = base.sendCost ∧
      (lift base capacity).deliveryCost = base.deliveryCost  := by
  have legal : ∀ current history, (lift base capacity).historyLegal current history = base.historyLegal current history := by
    intro current history
    induction history generalizing current with
    | nil => rfl
    | cons word rest ih =>
        change (decide (∀ item ∈ base.law.rawItems current word, base.law.Valid item.before item.request) &&
          (lift base capacity).historyLegal (base.law.next current word) rest) = _
        rw [ih]
        rfl
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
  have same : (lift base capacity).historyLegal = base.historyLegal := funext fun current => funext (legal current)
  simp only [Code.histories, same]
  rfl

theorem every_full_memory_strategy_is_generated (capacity : Nat)
    (strategy : (lift base capacity).Policy)
    (supported : ∀ key inside, strategy key inside ∈ words base.actions base.actionLimit) :
    strategy ∈ (lift base capacity).policies :=
  (lift base capacity).every_local_policy_is_enumerated strategy supported

def tabulate (capacity : Nat)
    (programme : Fin base.sites → List (Notice base) → RawEvent Party Good Port Technology Instrument) :
    (lift base capacity).Policy := fun key _ =>
  match decode base capacity key.2 with
  | none => []
  | some history => programme key.1 history

theorem every_supported_history_programme_is_actually_tabulated (capacity : Nat)
    (programme : Fin base.sites → List (Notice base) → RawEvent Party Good Port Technology Instrument)
    (supported : ∀ site history, history ∈ memories base capacity →
      programme site history ∈ words base.actions base.actionLimit) :
    tabulate base capacity programme ∈ (lift base capacity).policies := by
  apply every_full_memory_strategy_is_generated
  intro key _
  unfold tabulate
  cases reading : decode base capacity key.2 with
  | none => exact (mem_words_iff _ _ _).mpr (by simp)
  | some history =>
      apply supported
      unfold decode at reading
      split at reading
      · exact List.mem_of_getElem? reading
      · contradiction

theorem tabulated_programme_reads_the_complete_actual_history (capacity : Nat)
    (programme : Fin base.sites → List (Notice base) → RawEvent Party Good Port Technology Instrument)
    (site : Fin base.sites) (history : List (Notice base)) (generated : history ∈ memories base capacity) :
    (lift base capacity).action (tabulate base capacity programme) site (encode base capacity history) =
      programme site history := by
  simp only [Code.action, decode_encode base capacity history generated, Option.isSome_some,
    ↓reduceIte, tabulate]

theorem indistinguishable_local_histories_produce_the_same_action (capacity : Nat)
    (strategy : (lift base capacity).Policy) (site : Fin base.sites)
    (first second : List (Notice base)) (same : first = second) :
    (lift base capacity).action strategy site (encode base capacity first) =
      (lift base capacity).action strategy site (encode base capacity second) := by rw [same]

theorem activation_records_its_own_actual_attempt (capacity : Nat)
    (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (frame : (lift base capacity).Frame) (site : Fin base.sites) :
    ((lift base capacity).step strategy initial frame (.activate site)).inbox site =
      remember base capacity (frame.inbox site)
        (.attempted ((lift base capacity).action strategy site (frame.inbox site))) := by
  simp [Code.step, lift]

theorem paid_read_records_the_actual_local_sensor (capacity : Nat)
    (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (frame : (lift base capacity).Frame) (sender recipient : Fin base.sites)
    (paid : ∀ item ∈ base.law.rawItems ((lift base capacity).rawAt initial frame)
      (base.sendCost sender recipient), base.law.Valid item.before item.request) :
    ((lift base capacity).step strategy initial frame (.send sender recipient)).inbox sender =
      remember base capacity (frame.inbox sender)
        (.sent recipient (base.readLocal sender (base.snapshot sender ((lift base capacity).rawAt initial frame)))) := by
  have update := (lift base capacity).paid_send_updates_only_its_own_memory strategy initial frame sender recipient paid
  change _ = remember base capacity (frame.inbox sender) (.sent recipient _) at update
  simpa only [signal, sensor, Fin.isLt, ↓reduceDIte, Code.snapshot, lift] using update

theorem unpaid_read_cannot_generate_information (capacity : Nat)
    (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (frame : (lift base capacity).Frame) (sender recipient : Fin base.sites)
    (unpaid : ¬ ∀ item ∈ base.law.rawItems ((lift base capacity).rawAt initial frame)
      (base.sendCost sender recipient), base.law.Valid item.before item.request) :
    ((lift base capacity).step strategy initial frame (.send sender recipient)).inbox = frame.inbox ∧
      ((lift base capacity).step strategy initial frame (.send sender recipient)).sent = frame.sent := by
  exact (lift base capacity).unpaid_send_cannot_update_memory_or_packets strategy initial frame sender recipient unpaid

theorem paid_receipt_records_origin_and_signal (capacity : Nat)
    (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (frame : (lift base capacity).Frame) (address : Nat)
    (packet : (lift base capacity).Packet) (present : frame.sent[address]? = some packet)
    (paid : ∀ item ∈ base.law.rawItems ((lift base capacity).rawAt initial frame)
      (base.deliveryCost packet.recipient), base.law.Valid item.before item.request) :
    ((lift base capacity).step strategy initial frame (.deliver address)).inbox packet.recipient =
      remember base capacity (frame.inbox packet.recipient)
        (.received packet.sender (signal base capacity packet.signal)) := by
  exact (lift base capacity).delivery_reads_only_an_already_sent_packet strategy initial frame address packet present paid


def notice (capacity : Nat) (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (frame : (lift base capacity).Frame)
    (event : Event Party Good Port Technology Instrument base.sites)
    (site : Fin base.sites) : Option (Notice base) :=
  match event with
  | .adversary _ => none
  | .send sender recipient =>
      if site = sender ∧ ∀ item ∈ base.law.rawItems ((lift base capacity).rawAt initial frame)
        (base.sendCost sender recipient), base.law.Valid item.before item.request then
        some (.sent recipient (base.readLocal sender (base.snapshot sender ((lift base capacity).rawAt initial frame))))
      else none
  | .deliver address => match frame.sent[address]? with
      | none => none
      | some packet =>
          if site = packet.recipient ∧ ∀ item ∈ base.law.rawItems ((lift base capacity).rawAt initial frame)
            (base.deliveryCost packet.recipient), base.law.Valid item.before item.request then
            some (.received packet.sender (signal base capacity packet.signal))
          else none
  | .activate actor => if site = actor then
      some (.attempted ((lift base capacity).action strategy actor (frame.inbox actor))) else none

theorem actual_step_records_exactly_the_local_notice (capacity : Nat)
    (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (frame : (lift base capacity).Frame)
    (event : Event Party Good Port Technology Instrument base.sites) (site : Fin base.sites) :
    ((lift base capacity).step strategy initial frame event).inbox site =
      match notice base capacity strategy initial frame event site with
      | none => frame.inbox site
      | some observed => remember base capacity (frame.inbox site) observed := by
  cases event with
  | adversary request => rfl
  | activate actor =>
      by_cases same : site = actor
      · subst site; simp only [Code.step, notice, ↓reduceIte]
      · simp only [Code.step, notice, same, ↓reduceIte]
  | send sender recipient =>
      by_cases paid : ∀ item ∈ base.law.rawItems ((lift base capacity).rawAt initial frame)
          (base.sendCost sender recipient), base.law.Valid item.before item.request
      · by_cases same : site = sender
        · subst site
          simp only [notice]
          rw [if_pos ⟨True.intro, paid⟩]
          exact paid_read_records_the_actual_local_sensor base capacity strategy initial frame sender recipient paid
        · simp only [notice, same, false_and, ↓reduceIte]
          simp only [Code.step, decide_eq_true paid, ↓reduceIte, same]
      · simp only [notice, paid, and_false, ↓reduceIte]
        exact congrFun (unpaid_read_cannot_generate_information base capacity strategy initial frame sender recipient paid).1 site
  | deliver address =>
      cases found : frame.sent[address]? with
      | none => simp only [Code.step, notice, found]
      | some packet =>
          by_cases paid : ∀ item ∈ base.law.rawItems ((lift base capacity).rawAt initial frame)
              (base.deliveryCost packet.recipient), base.law.Valid item.before item.request
          · by_cases same : site = packet.recipient
            · subst site
              simp only [notice, found, true_and, if_pos paid]
              exact paid_receipt_records_origin_and_signal base capacity strategy initial frame address packet found paid
            · simp only [notice, found, same, false_and, ↓reduceIte]
              simp only [Code.step, found, decide_eq_true paid, ↓reduceIte, same]
          · simp only [notice, found, paid, and_false, ↓reduceIte]
            simp only [Code.step, found, decide_eq_false paid, Bool.false_eq_true, ↓reduceIte]

def transcript (capacity : Nat) (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument) :
    (lift base capacity).Frame → List (Event Party Good Port Technology Instrument base.sites) →
    Fin base.sites → List (Notice base)
  | _, [], _ => []
  | frame, event :: rest, site =>
      (notice base capacity strategy initial frame event site).toList ++
        transcript capacity strategy initial ((lift base capacity).step strategy initial frame event) rest site

theorem transcript_length (capacity : Nat) (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : (lift base capacity).Frame)
    (events : List (Event Party Good Port Technology Instrument base.sites)) (site : Fin base.sites) :
    (transcript base capacity strategy initial frame events site).length ≤ events.length := by
  induction events generalizing frame with
  | nil => exact Nat.le_refl _
  | cons event rest ih =>
      simp only [transcript, List.length_append, List.length_cons]
      have next := ih ((lift base capacity).step strategy initial frame event)
      cases notice base capacity strategy initial frame event site <;> simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_singleton] <;> omega

private theorem supported_action (capacity : Nat) (strategy : (lift base capacity).Policy)
    (generated : strategy ∈ (lift base capacity).policies) (site : Fin base.sites)
    (state : Fin (width base capacity)) :
    (lift base capacity).action strategy site state ∈ words base.actions base.actionLimit := by
  have supported := (List.mem_pi _ _).mp generated (site, state) ((lift base capacity).key_mem _)
  unfold Code.action
  split
  · exact supported
  · exact (mem_words_iff _ _ _).mpr (by simp)

theorem notice_is_generated (capacity : Nat) (strategy : (lift base capacity).Policy)
    (generated : strategy ∈ (lift base capacity).policies)
    (initial : RawCurrent Party Good Technology Instrument) (frame : (lift base capacity).Frame)
    (event : Event Party Good Port Technology Instrument base.sites) (site : Fin base.sites) :
    ∀ observed ∈ (notice base capacity strategy initial frame event site).toList, observed ∈ alphabet base := by
  have sent_supported : ∀ recipient signal, LocalNotice.sent recipient signal ∈ alphabet base := by
    intro recipient signal
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨(recipient, signal), List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩, by simp⟩
  have received_supported : ∀ sender signal, LocalNotice.received sender signal ∈ alphabet base := by
    intro sender signal
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨(sender, signal), List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩, by simp⟩
  cases event with
  | adversary request => simp [notice]
  | send sender recipient =>
      simp only [notice]; split <;> simp_all
  | deliver address =>
      simp only [notice]; split
      · simp
      · split <;> simp_all
  | activate actor =>
      simp only [notice]; split
      · intro observed member
        have same := List.mem_singleton.mp member
        subst observed
        exact List.mem_append_right _ (List.mem_map.mpr ⟨_, supported_action base capacity strategy generated actor (frame.inbox actor), rfl⟩)
      · simp

theorem transcript_is_generated_from_actual_notices (capacity : Nat)
    (strategy : (lift base capacity).Policy) (generated : strategy ∈ (lift base capacity).policies)
    (initial : RawCurrent Party Good Technology Instrument) (frame : (lift base capacity).Frame)
    (events : List (Event Party Good Port Technology Instrument base.sites))
    (bounded : events.length ≤ capacity) (site : Fin base.sites) :
    transcript base capacity strategy initial frame events site ∈ memories base capacity := by
  apply (mem_sequences_iff _ _ _).mpr
  refine ⟨le_trans (transcript_length base capacity strategy initial frame events site) bounded, ?_⟩
  clear bounded
  induction events generalizing frame with
  | nil => simp [transcript]
  | cons event rest ih =>
      intro observed member
      rcases List.mem_append.mp member with head | tail
      · exact notice_is_generated base capacity strategy generated initial frame event site observed head
      · exact ih ((lift base capacity).step strategy initial frame event) observed tail

private theorem faithful_from (capacity : Nat) (strategy : (lift base capacity).Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (events : List (Event Party Good Port Technology Instrument base.sites))
    (frame : (lift base capacity).Frame) (site : Fin base.sites) (prior : List (Notice base))
    (exact_memory : frame.inbox site = encode base capacity prior)
    (generated : prior ++ transcript base capacity strategy initial frame events site ∈ memories base capacity) :
    (events.foldl ((lift base capacity).step strategy initial) frame).inbox site =
      encode base capacity (prior ++ transcript base capacity strategy initial frame events site) := by
  induction events generalizing frame prior with
  | nil => simpa only [List.foldl_nil, transcript, List.append_nil] using exact_memory
  | cons event rest ih =>
      simp only [List.foldl_cons]
      have prior_generated : prior ∈ memories base capacity := by
        obtain ⟨bounded, supported⟩ := (mem_sequences_iff _ _ _).mp generated
        apply (mem_sequences_iff _ _ _).mpr
        exact ⟨by simp only [List.length_append] at bounded; omega,
          fun atom inside => supported atom (List.mem_append_left _ inside)⟩
      rw [transcript] at generated ⊢
      cases observed : notice base capacity strategy initial frame event site with
      | none =>
          simp only [observed, Option.toList_none, List.nil_append] at generated ⊢
          apply ih _ prior _ generated
          rw [actual_step_records_exactly_the_local_notice, observed]
          exact exact_memory
      | some atom =>
          simp only [observed, Option.toList_some, ← List.append_assoc] at generated ⊢
          apply ih _ (prior ++ [atom]) _ generated
          rw [actual_step_records_exactly_the_local_notice, observed, exact_memory]
          simp only [remember, decode_encode base capacity prior prior_generated]

theorem every_bounded_actual_prefix_keeps_perfect_local_recall (capacity : Nat)
    (strategy : (lift base capacity).Policy) (generated : strategy ∈ (lift base capacity).policies)
    (initial : RawCurrent Party Good Technology Instrument)
    (events : List (Event Party Good Port Technology Instrument base.sites))
    (bounded : events.length ≤ capacity) (site : Fin base.sites) :
    decode base capacity (((lift base capacity).replay strategy initial events).inbox site) =
      some (transcript base capacity strategy initial (lift base capacity).start events site) := by
  have supported := transcript_is_generated_from_actual_notices base capacity strategy generated initial
    (lift base capacity).start events bounded site
  have faithful := faithful_from base capacity strategy initial events (lift base capacity).start site [] rfl
    (by simpa only [List.nil_append] using supported)
  unfold Code.replay
  rw [faithful]
  simpa only [List.nil_append] using decode_encode base capacity _ supported

theorem actual_indistinguishable_prefixes_force_the_same_next_work (capacity : Nat)
    (strategy : (lift base capacity).Policy) (generated : strategy ∈ (lift base capacity).policies)
    (first second : RawCurrent Party Good Technology Instrument)
    (firstEvents secondEvents : List (Event Party Good Port Technology Instrument base.sites))
    (first_bound : firstEvents.length ≤ capacity) (second_bound : secondEvents.length ≤ capacity)
    (site : Fin base.sites)
    (indistinguishable : transcript base capacity strategy first (lift base capacity).start firstEvents site =
      transcript base capacity strategy second (lift base capacity).start secondEvents site) :
    (lift base capacity).action strategy site (((lift base capacity).replay strategy first firstEvents).inbox site) =
      (lift base capacity).action strategy site (((lift base capacity).replay strategy second secondEvents).inbox site) := by
  have first_history := transcript_is_generated_from_actual_notices base capacity strategy generated first
    (lift base capacity).start firstEvents first_bound site
  have second_history := transcript_is_generated_from_actual_notices base capacity strategy generated second
    (lift base capacity).start secondEvents second_bound site
  have first_memory := faithful_from base capacity strategy first firstEvents (lift base capacity).start site [] rfl
    (by simpa only [List.nil_append] using first_history)
  have second_memory := faithful_from base capacity strategy second secondEvents (lift base capacity).start site [] rfl
    (by simpa only [List.nil_append] using second_history)
  unfold Code.replay
  rw [first_memory, second_memory, List.nil_append, List.nil_append, indistinguishable]

theorem exhausted_memory_cannot_authorize_further_work (capacity : Nat)
    (strategy : (lift base capacity).Policy) (site : Fin base.sites) :
    (lift base capacity).action strategy site (overflow base capacity) = [] := by
  simp only [Code.action, decode_overflow, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall
