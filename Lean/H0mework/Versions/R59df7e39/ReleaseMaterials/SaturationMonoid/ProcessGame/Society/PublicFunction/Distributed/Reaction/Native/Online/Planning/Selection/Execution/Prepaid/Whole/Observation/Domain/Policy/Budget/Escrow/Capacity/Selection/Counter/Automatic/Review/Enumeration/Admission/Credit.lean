import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Admission
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Admission.Credit
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}

structure Tag (all : Candidates source catalogue) where
  who : Ready all
  term : Admission.Term who
  row : Admission.Row who
structure Packet (all : Candidates source catalogue) where
  tag : Tag all
  receipt : Admission.Receipt tag.who tag.term tag.row
inductive Log (all : Candidates source catalogue) where
  | silent
  | credit (tag : Tag all) (ordinal : Nat)
  | tested (packet : Packet all)
inductive Mark (all : Candidates source catalogue) where
  | idle
  | held (tag : Tag all) (count : Nat)
def Mark.count : Mark all → Nat
  | .idle => 0
  | .held _ count => count
inductive Rule : Mark all → Log all → Mark all → Prop where
  | fresh (before after : Mark all) (cold : after.count = 0) : Rule before .silent after
  | credit (tag : Tag all) (ordinal : Nat) : Rule (.held tag ordinal) (.credit tag ordinal) (.held tag (ordinal+1))
  | settle (packet : Packet all) (before after : Mark all)
      (paid : before = .held packet.tag packet.receipt.prepaid) (next : after = .idle) : Rule before (.tested packet) after

def mark (who : Ready all) (term : Admission.Term who) : Admission.State who term → Mark all
  | .reserving row _ _ _ _ _ prepaid _ => .held ⟨who,term,row⟩ prepaid
  | _ => .idle
def log (who : Ready all) (term : Admission.Term who) : Admission.Event who term → Log all
  | .credit row ordinal => .credit ⟨who,term,row⟩ ordinal
  | .tested row receipt => .tested ⟨⟨who,term,row⟩,receipt⟩
  | _ => .silent

theorem step_rule (who : Ready all) {term : Admission.Term who}
    {before after : Admission.State who term} {event : Admission.Event who term}
    (observed : Admission.step who before = some (after,event)) :
    Rule (mark who term before) (log who term event) (mark who term after) := by
  cases before with
  | waiting todo within passed =>
    cases todo <;> cases Option.some.inj observed
    all_goals exact .fresh _ _ rfl
  | finishing row rest within passed cursor =>
    dsimp only [Admission.step] at observed;split at observed
    all_goals cases Option.some.inj observed
    all_goals exact .fresh _ _ rfl
  | quoting row rest within passed cursor remaining balanced =>
    dsimp only [Admission.step] at observed;split at observed
    · cases Option.some.inj observed;exact .fresh _ _ rfl
    · cases remaining <;> cases Option.some.inj observed
      all_goals exact .fresh _ _ rfl
  | reserving row rest within passed allowance remaining prepaid balanced =>
    cases remaining with
    | succ remaining => cases Option.some.inj observed;exact .credit _ _
    | zero =>
      dsimp only [Admission.step] at observed;split at observed
      all_goals cases Option.some.inj observed
      all_goals dsimp only [mark,log]
      all_goals exact .settle _ _ _ rfl rfl
  | approved | refused => cases observed

def credits (tag : Tag all) (count : Nat) : List (Log all) := (List.range count).map (.credit tag)
theorem credits_length (tag : Tag all) (count : Nat) : (credits tag count).length = count := by simp [credits]
theorem credits_succ (tag : Tag all) (count : Nat) : credits tag (count+1) = credits tag count++[.credit tag count] := by
  simp [credits,List.range_succ]
def Bank (events : List (Log all)) : Mark all → Prop
  | .idle => True
  | .held tag count => ∃ before,events = before++credits tag count
def Segment (events : List (Log all)) (position : Nat) (packet : Packet all) : Prop :=
  ∃ before after,events = before++credits packet.tag packet.receipt.prepaid++[.tested packet]++after ∧
    position = before.length+packet.receipt.prepaid
def Funded (events : List (Log all)) : Prop :=
  ∀ position packet,events[position]? = some (.tested packet) → Segment events position packet

theorem rule_extends_bank {before after : Mark all} {event : Log all} (rule : Rule before event after)
    (events : List (Log all)) (bank : Bank events before) : Bank (events++[event]) after := by
  cases rule with
  | fresh before after cold =>
    cases after with
    | idle => trivial
    | held tag count =>
      change count = 0 at cold
      subst count
      exact ⟨events++[.silent],by simp [credits]⟩
  | credit tag ordinal =>
    obtain ⟨past,same⟩ := bank
    exact ⟨past,by rw [same,credits_succ,List.append_assoc]⟩
  | settle packet before after paid next => rw [next];trivial

theorem rule_extends_funding {before after : Mark all} {event : Log all} (rule : Rule before event after)
    (events : List (Log all)) (bank : Bank events before) (funded : Funded events) : Funded (events++[event]) := by
  intro position packet observed
  by_cases old : position < events.length
  · rw [List.getElem?_append_left old] at observed
    obtain ⟨past,tail,same,at_position⟩ := funded position packet observed
    exact ⟨past,tail++[event],by rw [same];simp only [List.append_assoc],at_position⟩
  · have at_end : events.length ≤ position := by omega
    rw [List.getElem?_append_right at_end] at observed
    have last : position-events.length = 0 := by
      have inside := (List.getElem?_eq_some_iff.mp observed).1
      simp only [List.length_singleton] at inside
      omega
    have same_event : event = .tested packet := by simpa only [last,List.getElem?_cons_zero,Option.some.injEq] using observed
    have exact_position : position = events.length := by omega
    cases rule with
    | fresh => cases same_event
    | credit => cases same_event
    | settle actual before after paid next =>
      cases same_event
      rw [paid] at bank
      obtain ⟨past,same⟩ := bank
      refine ⟨past,[],?_,?_⟩
      · rw [same];simp only [List.append_nil]
      · rw [exact_position,same,List.length_append,credits_length]

inductive Trace : Mark all → Mark all → List (Log all) → Prop where
  | nil (before : Mark all) : Trace before before []
  | step {before middle after : Mark all} {event : Log all} {rest : List (Log all)}
      (rule : Rule before event middle) (later : Trace middle after rest) : Trace before after (event::rest)

theorem Trace.extends {before after : Mark all} {events : List (Log all)} (trace : Trace before after events)
    (past : List (Log all)) (bank : Bank past before) (funded : Funded past) :
    Bank (past++events) after ∧ Funded (past++events) := by
  induction trace generalizing past with
  | nil => simpa only [List.append_nil] using And.intro bank funded
  | @step before middle after event rest rule later ih =>
    have next := ih (past++[event]) (rule_extends_bank rule past bank) (rule_extends_funding rule past bank funded)
    simpa only [List.append_assoc,List.singleton_append] using next

theorem Trace.funded {after : Mark all} {events : List (Log all)} (trace : Trace (.idle : Mark all) after events) : Funded events := by
  have empty : Funded ([] : List (Log all)) := by intro position packet impossible;simp at impossible
  simpa only [List.nil_append] using (trace.extends [] trivial empty).2

theorem Segment.credit_at {events : List (Log all)} {position : Nat} {packet : Packet all}
    (segment : Segment events position packet) (offset : Fin packet.receipt.prepaid) :
    packet.receipt.prepaid ≤ position ∧ position < events.length ∧
    events[position-packet.receipt.prepaid+offset.val]? = some (.credit packet.tag offset.val) := by
  obtain ⟨past,tail,rfl,rfl⟩ := segment
  have source : (credits packet.tag packet.receipt.prepaid)[offset.val]? = some (.credit packet.tag offset.val) := by
    simp [credits,offset.isLt]
  constructor
  · omega
  constructor
  · simp only [List.length_append,credits_length,List.length_singleton];omega
  · have index : past.length+packet.receipt.prepaid-packet.receipt.prepaid+offset.val = past.length+offset.val := by omega
    rw [index,List.append_assoc,List.append_assoc,List.getElem?_append_right (by omega)]
    have index2 : past.length+offset.val-past.length = offset.val := by omega
    rw [index2,List.getElem?_append_left (by simpa only [credits_length] using offset.isLt)]
    exact source

theorem Segment.bounds {events : List (Log all)} {position : Nat} {packet : Packet all}
    (segment : Segment events position packet) : packet.receipt.prepaid ≤ position ∧ position < events.length := by
  obtain ⟨past,tail,rfl,rfl⟩ := segment
  simp only [List.length_append,credits_length,List.length_singleton]
  omega

theorem Segment.tested_at {events : List (Log all)} {position : Nat} {packet : Packet all}
    (segment : Segment events position packet) : events[position]? = some (.tested packet) := by
  obtain ⟨past,tail,rfl,rfl⟩ := segment
  have index : past.length+packet.receipt.prepaid = (past++credits packet.tag packet.receipt.prepaid).length := by simp [credits_length]
  rw [index,List.append_assoc (past++credits packet.tag packet.receipt.prepaid),List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- A later reservation cannot pass through any earlier receipt event. -/
theorem Segment.separate {events : List (Log all)} {first second : Nat} {left right : Packet all}
    (paidLeft : Segment events first left) (paidRight : Segment events second right) (ordered : first < second) :
    first < second-right.receipt.prepaid := by
  by_contra overlaps
  have rightBound := paidRight.bounds
  have offsetBound : first-(second-right.receipt.prepaid) < right.receipt.prepaid := by omega
  let offset : Fin right.receipt.prepaid := ⟨first-(second-right.receipt.prepaid),offsetBound⟩
  have paid := (paidRight.credit_at offset).2.2
  have index : second-right.receipt.prepaid+offset.val = first := by dsimp only [offset];omega
  rw [index,paidLeft.tested_at] at paid
  cases paid

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Admission.Credit
