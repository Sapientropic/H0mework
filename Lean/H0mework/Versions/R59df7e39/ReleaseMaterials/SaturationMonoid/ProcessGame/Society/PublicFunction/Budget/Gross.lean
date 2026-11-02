import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Selection
import Mathlib.Data.Rat.Floor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument) (party : Party) (good : Good)

def flowCost (flow : Flow Party Good) : ℚ :=
  flowAt flow party good

/-- Stateful production/revision costs retain their unresolved primitive request. -/
def staticDebit (request : Request Party Good Port Technology Instrument) : Option (Flow Party Good) :=
  match request.operation with
  | .use bearer bundle _ | .transfer bearer _ bundle => some (locate bearer bundle)
  | .settle instrument debtor _ quantity =>
      some (locate debtor [(law.settlementUnit instrument,quantity*law.settlementRate instrument)])
  | .issue _ _ _ _ | .assign _ _ _ _ _ | .present => some []
  | .produce _ | .revise _ _ => none

def charge (request : Request Party Good Port Technology Instrument) : Option ℚ :=
  (staticDebit law request).map (flowCost party good)

def Costly (request : Request Party Good Port Technology Instrument) : Prop :=
  match charge law party good request with | none => False | some amount => 0 < amount

instance (request : Request Party Good Port Technology Instrument) :
    Decidable (Costly law party good request) := by unfold Costly; split <;> infer_instance

private def floor : List ℚ → ℚ
  | [] => 1
  | amount :: rest => min amount (floor rest)

private theorem floor_positive (amounts : List ℚ) (positive : ∀ amount ∈ amounts,0 < amount) :
    0 < floor amounts := by
  induction amounts with
  | nil => exact zero_lt_one
  | cons amount rest ih =>
    exact lt_min (positive amount List.mem_cons_self) (ih fun other inside => positive other (List.mem_cons_of_mem _ inside))

private theorem floor_le_member (amounts : List ℚ) (amount : ℚ) (inside : amount ∈ amounts) :
    floor amounts ≤ amount := by
  induction amounts with
  | nil => simp only [List.not_mem_nil] at inside
  | cons first rest ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst amount; exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih later)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem static_debit_is_the_original_debit (request : Request Party Good Port Technology Instrument)
    (flow : Flow Party Good) (known : staticDebit law request = some flow)
    (current : RawCurrent Party Good Technology Instrument) : law.debit current request = flow := by
  cases operation : request.operation <;> simp_all [staticDebit,RawLaw.debit]

omit [DecidableEq Instrument] in
theorem charge_is_the_original_material_amount (request : Request Party Good Port Technology Instrument)
    (amount : ℚ) (known : charge law party good request = some amount)
    (current : RawCurrent Party Good Technology Instrument) : flowCost party good (law.debit current request) = amount := by
  unfold charge at known
  cases present : staticDebit law request with
  | none => simp [present] at known
  | some flow =>
    have exactAmount : flowCost party good flow = amount := by simpa only [present,Option.map_some,Option.some.injEq] using known
    rw [static_debit_is_the_original_debit law request flow present current,exactAmount]

variable (actions : List (Request Party Good Port Technology Instrument))

structure Floor where
  epsilon : ℚ
  generated : epsilon = floor (actions.filterMap (charge law party good))
  positive : 0 < epsilon
  readings : ∀ request ∈ actions, ∃ amount, charge law party good request = some amount ∧ epsilon ≤ amount

def produce (costly : ∀ request ∈ actions,Costly law party good request) : Floor law party good actions := by
  refine ⟨floor (actions.filterMap (charge law party good)),rfl,?_,?_⟩
  · apply floor_positive
    intro amount inside
    obtain ⟨request,member,known⟩ := List.mem_filterMap.mp inside
    have positive := costly request member
    simpa only [Costly,known] using positive
  · intro request member
    have positive := costly request member
    cases known : charge law party good request with
    | none => simp only [Costly,known] at positive
    | some amount => exact ⟨amount,rfl,floor_le_member _ _ (List.mem_filterMap.mpr ⟨request,member,known⟩)⟩

inductive Outcome where
  | positive (result : Floor law party good actions)
  | unresolved (request : Request Party Good Port Technology Instrument) (original : request ∈ actions)
      (broken : ¬ Costly law party good request)

def generate : Outcome law party good actions :=
  match Distributed.inspect (Costly law party good) actions with
  | .accepted all => .positive (produce law party good actions all)
  | .rejected request original broken => .unresolved request original broken

def ReadLower (epsilon : ℚ) (request : Request Party Good Port Technology Instrument) : Prop :=
  match charge law party good request with | none => False | some amount => epsilon ≤ amount

instance (epsilon : ℚ) (request : Request Party Good Port Technology Instrument) :
    Decidable (ReadLower law party good epsilon request) := by unfold ReadLower; split <;> infer_instance

def verify (epsilon : ℚ) : Bool := decide (0 < epsilon ∧ ∀ request ∈ actions,ReadLower law party good epsilon request)

omit [DecidableEq Instrument] in
theorem every_generated_floor_has_independent_review (result : Floor law party good actions) :
    verify law party good actions result.epsilon = true := by
  simp only [verify,decide_eq_true_eq]
  refine ⟨result.positive,?_⟩
  intro request inside
  obtain ⟨amount,known,lower⟩ := result.readings request inside
  simp only [ReadLower,known,lower]

def debit (items : List (ExecutionItem Party Good Port Technology Instrument)) : ℚ :=
  law.totalDebit items party good

omit [DecidableEq Instrument] in
theorem debit_cons (item : ExecutionItem Party Good Port Technology Instrument)
    (rest : List (ExecutionItem Party Good Port Technology Instrument)) :
    debit law party good (item::rest) =
      flowCost party good (law.actualDebit item.before item.request) + debit law party good rest := by
  rfl

namespace Floor
variable {law party good actions} (result : Floor law party good actions)

def cap (budget : ℚ) : Nat := Nat.ceil (budget/result.epsilon)

theorem every_legal_supported_word_pays_for_its_length
    (current : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (supported : ∀ request ∈ word,request ∈ actions)
    (legal : ∀ item ∈ law.rawItems current word,law.Valid item.before item.request) :
    (word.length : ℚ)*result.epsilon ≤ debit law party good (law.rawItems current word) := by
  have items (entries : List (ExecutionItem Party Good Port Technology Instrument))
      (supported : ∀ item ∈ entries,item.request ∈ actions)
      (legal : ∀ item ∈ entries,law.Valid item.before item.request) :
      (entries.length : ℚ)*result.epsilon ≤ debit law party good entries := by
    induction entries with
    | nil => simp [debit,RawLaw.totalDebit]
    | cons item rest ih =>
      obtain ⟨amount,known,lower⟩ := result.readings item.request (supported item List.mem_cons_self)
      have exactAmount := charge_is_the_original_material_amount law party good item.request amount known item.before
      rw [debit_cons,RawLaw.actualDebit,if_pos (legal item List.mem_cons_self),exactAmount]
      have tail := ih (fun other member => supported other (List.mem_cons_of_mem _ member))
        (fun other member => legal other (List.mem_cons_of_mem _ member))
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith
  have rawSupported : ∀ item ∈ law.rawItems current word,item.request ∈ actions := by
    intro item member
    exact supported item.request (by
      have requests := law.inventory_requests_exact current 0 word
      exact requests ▸ List.mem_map.mpr ⟨item,member,rfl⟩)
  have bound := items (law.rawItems current word) rawSupported legal
  simpa only [RawLaw.rawItems,law.inventory_length] using bound

theorem every_cost_bounded_raw_word_is_enumerated
    (budget : ℚ) (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (supported : ∀ request ∈ word,request ∈ actions)
    (legal : ∀ item ∈ law.rawItems current word,law.Valid item.before item.request)
    (affordable : debit law party good (law.rawItems current word) ≤ budget) :
    word ∈ words actions (result.cap budget) := by
  apply (mem_words_iff _ _ _).mpr
  refine ⟨?_,supported⟩
  have paid := (result.every_legal_supported_word_pays_for_its_length current word supported legal).trans affordable
  have divided : (word.length : ℚ) ≤ budget/result.epsilon := (le_div_iff₀ result.positive).mpr paid
  exact_mod_cast divided.trans (Nat.le_ceil (budget/result.epsilon))

end Floor
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross
