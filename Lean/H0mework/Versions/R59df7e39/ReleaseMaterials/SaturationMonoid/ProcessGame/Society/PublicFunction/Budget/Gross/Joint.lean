import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Flows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross.Joint

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- A positive reading of one original request in its original material unit. -/
structure Ticket (axes : List (Party × Good)) where
  request : Request Party Good Port Technology Instrument
  axis : Party × Good
  source : axis ∈ axes
  amount : ℚ
  positive : 0 < amount
  original : charge law axis.1 axis.2 request = some amount

def read (axes : List (Party × Good))
    (request : Request Party Good Port Technology Instrument) : Option (Ticket law axes) :=
  axes.attach.findSome? fun axis =>
    match known : charge law axis.val.1 axis.val.2 request with
    | none => none
    | some amount => if positive : 0 < amount then
        some ⟨request,axis.val,axis.property,amount,positive,known⟩ else none

def debit (axes : List (Party × Good)) (tickets : List (Ticket law axes))
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : ℚ :=
  (tickets.map fun ticket => Gross.debit law ticket.axis.1 ticket.axis.2 items / ticket.amount).sum

def cap (axes : List (Party × Good)) (tickets : List (Ticket law axes))
    (budget : Party × Good → ℚ) : Nat :=
  Nat.ceil ((tickets.map fun ticket => budget ticket.axis / ticket.amount).sum)

variable {law} {axes : List (Party × Good)}

omit [DecidableEq Instrument] in
theorem read_retains_the_original_request
    (request : Request Party Good Port Technology Instrument) (ticket : Ticket law axes)
    (generated : read law axes request = some ticket) : ticket.request = request := by
  unfold read at generated
  obtain ⟨axis,_,found⟩ := List.exists_of_findSome?_eq_some generated
  split at found
  · contradiction
  · split at found
    · exact congrArg Ticket.request (Option.some.inj found).symm
    · contradiction

omit [DecidableEq Instrument] in
theorem a_missing_reading_retains_its_exact_source_axes
    (request : Request Party Good Port Technology Instrument)
    (absent : read law axes request = none) :
    ∀ axis ∈ axes, ¬ Costly law axis.1 axis.2 request := by
  unfold read at absent
  intro axis inside
  have missing := List.findSome?_eq_none_iff.mp absent ⟨axis,inside⟩ (List.mem_attach _ _)
  cases known : charge law axis.1 axis.2 request with
  | none => simp only [Costly,known,not_false_eq_true]
  | some amount =>
    have nonpositive : ¬ 0 < amount := by
      intro positive
      split at missing <;> simp_all
    simpa only [Costly,known] using nonpositive

structure Coverage (law : RawLaw Party Good Port Technology Instrument)
    (axes : List (Party × Good))
    (actions : List (Request Party Good Port Technology Instrument)) where
  tickets : List (Ticket law axes)
  generated : tickets = actions.filterMap (read law axes)
  covered : ∀ request ∈ actions, ∃ ticket ∈ tickets, ticket.request = request

inductive Outcome (law : RawLaw Party Good Port Technology Instrument)
    (axes : List (Party × Good))
    (actions : List (Request Party Good Port Technology Instrument)) where
  | positive (readings : Coverage law axes actions)
  | unresolved (request : Request Party Good Port Technology Instrument)
      (original : request ∈ actions) (absent : read law axes request = none)
      (all_source_axes : ∀ axis ∈ axes, ¬ Costly law axis.1 axis.2 request)

def generate (actions : List (Request Party Good Port Technology Instrument)) : Outcome law axes actions :=
  match Distributed.inspect (fun request => (read law axes request).isSome = true) actions with
  | .accepted all => .positive
      { tickets := actions.filterMap (read law axes)
        generated := rfl
        covered := by
          intro request original
          have present := all request original
          cases known : read law axes request with
          | none => simp only [known,Option.isSome_none,Bool.false_eq_true] at present
          | some ticket =>
            exact ⟨ticket,List.mem_filterMap.mpr ⟨request,original,known⟩,
              read_retains_the_original_request request ticket known⟩ }
  | .rejected request original broken =>
      have absent : read law axes request = none := by
        cases known : read law axes request with
        | none => rfl
        | some ticket => exact False.elim (broken (by simp only [known,Option.isSome_some]))
      .unresolved request original absent (a_missing_reading_retains_its_exact_source_axes request absent)

omit [DecidableEq Instrument] in
private theorem debit_nil (tickets : List (Ticket law axes)) : debit law axes tickets [] = 0 := by
  simp [debit,Gross.debit,RawLaw.totalDebit]

omit [DecidableEq Instrument] in
private theorem debit_cons (tickets : List (Ticket law axes))
    (item : ExecutionItem Party Good Port Technology Instrument)
    (rest : List (ExecutionItem Party Good Port Technology Instrument)) :
    debit law axes tickets (item::rest) =
      (tickets.map fun ticket => flowCost ticket.axis.1 ticket.axis.2
        (law.actualDebit item.before item.request) / ticket.amount).sum + debit law axes tickets rest := by
  induction tickets with
  | nil => simp [debit]
  | cons ticket tickets ih =>
    simp only [debit,List.map_cons,List.sum_cons] at *
    rw [Gross.debit_cons,add_div]
    linarith

omit [DecidableEq Instrument] in
private theorem each_legal_item_pays_one
    (tickets : List (Ticket law axes))
    (item : ExecutionItem Party Good Port Technology Instrument)
    (covered : ∃ ticket ∈ tickets, ticket.request = item.request)
    (legal : law.Valid item.before item.request) :
    1 ≤ (tickets.map fun ticket => flowCost ticket.axis.1 ticket.axis.2
      (law.actualDebit item.before item.request) / ticket.amount).sum := by
  obtain ⟨ticket,inside,same⟩ := covered
  have exactAmount := charge_is_the_original_material_amount law ticket.axis.1 ticket.axis.2
    ticket.request ticket.amount ticket.original item.before
  rw [same] at exactAmount
  have paid : flowCost ticket.axis.1 ticket.axis.2 (law.actualDebit item.before item.request) /
      ticket.amount = 1 := by
    rw [RawLaw.actualDebit,if_pos legal,exactAmount,div_self (ne_of_gt ticket.positive)]
  rw [← paid]
  apply List.single_le_sum
  · intro amount member
    obtain ⟨other,_,rfl⟩ := List.mem_map.mp member
    exact div_nonneg (Institutions.Capitalism.Universal.Source.Material.paid_nonnegative law item other.axis.1 other.axis.2)
      other.positive.le
  · exact List.mem_map.mpr ⟨ticket,inside,rfl⟩

theorem every_legal_covered_word_pays_its_dimensionless_count
    (tickets : List (Ticket law axes))
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (covered : ∀ request ∈ word, ∃ ticket ∈ tickets, ticket.request = request)
    (legal : ∀ item ∈ law.rawItems current word,law.Valid item.before item.request) :
    (word.length : ℚ) ≤ debit law axes tickets (law.rawItems current word) := by
  have items (entries : List (ExecutionItem Party Good Port Technology Instrument))
      (covered : ∀ item ∈ entries, ∃ ticket ∈ tickets, ticket.request = item.request)
      (legal : ∀ item ∈ entries,law.Valid item.before item.request) :
      (entries.length : ℚ) ≤ debit law axes tickets entries := by
    induction entries with
    | nil => simp only [List.length_nil,Nat.cast_zero,debit_nil,le_refl]
    | cons item rest ih =>
      have head := each_legal_item_pays_one tickets item (covered item List.mem_cons_self) (legal item List.mem_cons_self)
      have tail := ih (fun other inside => covered other (List.mem_cons_of_mem _ inside))
        (fun other inside => legal other (List.mem_cons_of_mem _ inside))
      rw [debit_cons]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith
  have rawCovered : ∀ item ∈ law.rawItems current word, ∃ ticket ∈ tickets, ticket.request = item.request := by
    intro item inside
    apply covered
    have requests := law.inventory_requests_exact current 0 word
    exact requests ▸ List.mem_map.mpr ⟨item,inside,rfl⟩
  simpa only [RawLaw.rawItems,law.inventory_length] using items (law.rawItems current word) rawCovered legal

theorem every_joint_bounded_raw_word_is_enumerated
    (tickets : List (Ticket law axes))
    (actions : List (Request Party Good Port Technology Instrument))
    (budget : Party × Good → ℚ)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (coverage : ∀ request ∈ actions, ∃ ticket ∈ tickets, ticket.request = request)
    (supported : ∀ request ∈ word,request ∈ actions)
    (legal : ∀ item ∈ law.rawItems current word,law.Valid item.before item.request)
    (affordable : ∀ ticket ∈ tickets, Gross.debit law ticket.axis.1 ticket.axis.2 (law.rawItems current word) ≤ budget ticket.axis) :
    word ∈ words actions (cap law axes tickets budget) := by
  apply (mem_words_iff _ _ _).mpr
  refine ⟨?_,supported⟩
  have paid := every_legal_covered_word_pays_its_dimensionless_count tickets current word
    (fun request member => coverage request (supported request member)) legal
  have cost : debit law axes tickets (law.rawItems current word) ≤
      (tickets.map fun ticket => budget ticket.axis / ticket.amount).sum := by
    unfold debit
    apply List.sum_le_sum
    intro ticket inside
    exact div_le_div_of_nonneg_right (affordable ticket inside) ticket.positive.le
  have total := paid.trans cost
  exact_mod_cast total.trans (Nat.le_ceil _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross.Joint
