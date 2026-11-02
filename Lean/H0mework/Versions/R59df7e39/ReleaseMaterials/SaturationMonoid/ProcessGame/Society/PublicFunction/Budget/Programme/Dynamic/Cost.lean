import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic.Technology
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross.Joint

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic.Cost

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

def axes : List (Party × Good) := code.parties.flatMap fun party => code.goods.map fun good => (party,good)

private def snapshot (technology : Technology) : RawCurrent Party Good Technology Instrument :=
  ⟨fun _ _ => 0,fun _ _ _ => 0,technology,0,0⟩

def amountAt (technology : Technology) (request : Request Party Good Port Technology Instrument)
    (axis : Party × Good) : ℚ := flowAt (code.law.debit (snapshot technology) request) axis.1 axis.2

theorem the_technology_reading_is_the_original_material_debit
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (axis : Party × Good) :
    amountAt code current.technology request axis = flowAt (code.law.debit current request) axis.1 axis.2 := by
  cases request.operation <;> rfl

structure Reading where
  request : Request Party Good Port Technology Instrument
  technology : Technology
  axis : Party × Good
  source_axis : axis ∈ axes code
  amount : ℚ
  positive : 0 < amount
  original : amountAt code technology request axis = amount

def read (request : Request Party Good Port Technology Instrument) (technology : Technology) :
    Option {reading : Reading code // reading.request = request ∧ reading.technology = technology} :=
  (axes code).attach.findSome? fun axis =>
    if positive : 0 < amountAt code technology request axis.val then
      some ⟨⟨request,technology,axis.val,axis.property,_,positive,rfl⟩,rfl,rfl⟩ else none

def pairs (menu : List Technology) : List (Request Party Good Port Technology Instrument × Technology) :=
  code.actions.flatMap fun request => menu.map fun technology => (request,technology)

def tickets (menu : List Technology) : List (Reading code) :=
  (pairs code menu).filterMap fun pair => (read code pair.1 pair.2).map Subtype.val

structure Coverage (menu : List Technology) where
  readings : List (Reading code)
  generated : readings = tickets code menu
  covered : ∀ request ∈ code.actions,∀ technology ∈ menu,
    ∃ reading ∈ readings,reading.request = request ∧ reading.technology = technology

inductive Outcome (menu : List Technology) where
  | positive (coverage : Coverage code menu)
  | unresolved (request : Request Party Good Port Technology Instrument) (technology : Technology)
      (source_request : request ∈ code.actions) (source_technology : technology ∈ menu)
      (absent : read code request technology = none)

def generate (menu : List Technology) : Outcome code menu :=
  match inspect (fun pair : Request Party Good Port Technology Instrument × Technology =>
      (read code pair.1 pair.2).isSome = true) (pairs code menu) with
  | .accepted all => .positive
    { readings := tickets code menu
      generated := rfl
      covered := by
        intro request original technology reachable
        have pair : (request,technology) ∈ pairs code menu :=
          List.mem_flatMap.mpr ⟨request,original,List.mem_map.mpr ⟨technology,reachable,rfl⟩⟩
        have present := all _ pair
        cases known : read code request technology with
        | none => simp only [known,Option.isSome_none,Bool.false_eq_true] at present
        | some reading =>
          exact ⟨reading.val,List.mem_filterMap.mpr ⟨(request,technology),pair,by rw [known];rfl⟩,reading.property⟩ }
  | .rejected pair original broken => by
    have absent : read code pair.1 pair.2 = none := by
      cases known : read code pair.1 pair.2 with
      | none => rfl
      | some reading => exact False.elim (broken (by simp only [known,Option.isSome_some]))
    have requestSource : pair.1 ∈ code.actions := by
      obtain ⟨request,member,technology⟩ := List.mem_flatMap.mp original
      obtain ⟨state,_,same⟩ := List.mem_map.mp technology
      cases same
      exact member
    have technologySource : pair.2 ∈ menu := by
      obtain ⟨request,_,technology⟩ := List.mem_flatMap.mp original
      obtain ⟨state,reachable,same⟩ := List.mem_map.mp technology
      cases same
      exact reachable
    exact .unresolved pair.1 pair.2 requestSource technologySource absent

def debit (readings : List (Reading code))
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : ℚ :=
  (readings.map fun reading => code.law.totalDebit items reading.axis.1 reading.axis.2 / reading.amount).sum

def cap (readings : List (Reading code)) (budget : Party × Good → ℚ) : Nat :=
  Nat.ceil ((readings.map fun reading => budget reading.axis / reading.amount).sum)

private theorem debit_cons (readings : List (Reading code))
    (item : ExecutionItem Party Good Port Technology Instrument)
    (rest : List (ExecutionItem Party Good Port Technology Instrument)) :
    debit code readings (item::rest) =
      (readings.map fun reading => flowAt (code.law.actualDebit item.before item.request)
        reading.axis.1 reading.axis.2 / reading.amount).sum + debit code readings rest := by
  induction readings with
  | nil => simp [debit]
  | cons reading readings ih =>
    simp only [debit,List.map_cons,List.sum_cons,RawLaw.totalDebit,List.map_cons,List.sum_cons] at *
    rw [add_div]
    linarith

private theorem each_original_item_pays_a_source_generated_count
    (readings : List (Reading code)) (item : ExecutionItem Party Good Port Technology Instrument)
    (covered : ∃ reading ∈ readings,reading.request = item.request ∧ reading.technology = item.before.technology)
    (legal : code.law.Valid item.before item.request) :
    1 ≤ (readings.map fun reading => flowAt (code.law.actualDebit item.before item.request)
      reading.axis.1 reading.axis.2 / reading.amount).sum := by
  obtain ⟨reading,inside,request,technology⟩ := covered
  have exactCost := reading.original
  rw [request,technology,the_technology_reading_is_the_original_material_debit] at exactCost
  have paid : flowAt (code.law.actualDebit item.before item.request) reading.axis.1 reading.axis.2 /
      reading.amount = 1 := by
    rw [RawLaw.actualDebit,if_pos legal,exactCost,div_self (ne_of_gt reading.positive)]
  rw [← paid]
  apply List.single_le_sum
  · intro value present
    obtain ⟨other,_,rfl⟩ := List.mem_map.mp present
    exact div_nonneg (Institutions.Capitalism.Universal.Source.Material.paid_nonnegative code.law item _ _)
      other.positive.le
  · exact List.mem_map.mpr ⟨reading,inside,rfl⟩

theorem every_legal_dynamically_covered_word_pays_its_count
    (menu : List Technology) (coverage : Coverage code menu)
    (current : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (supported : ∀ request ∈ word,request ∈ code.actions)
    (reachable : ∀ item ∈ code.law.rawItems current word,item.before.technology ∈ menu)
    (legal : ∀ item ∈ code.law.rawItems current word,code.law.Valid item.before item.request) :
    (word.length : ℚ) ≤ debit code coverage.readings (code.law.rawItems current word) := by
  have count (items : List (ExecutionItem Party Good Port Technology Instrument))
      (covered : ∀ item ∈ items,∃ reading ∈ coverage.readings,
        reading.request = item.request ∧ reading.technology = item.before.technology)
      (accepted : ∀ item ∈ items,code.law.Valid item.before item.request) :
      (items.length : ℚ) ≤ debit code coverage.readings items := by
    induction items with
    | nil => simp [debit,RawLaw.totalDebit]
    | cons item rest ih =>
      have head := each_original_item_pays_a_source_generated_count code coverage.readings item
        (covered item List.mem_cons_self) (accepted item List.mem_cons_self)
      have tail := ih (fun other inside => covered other (List.mem_cons_of_mem _ inside))
        (fun other inside => accepted other (List.mem_cons_of_mem _ inside))
      rw [debit_cons]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith
  have original (item : ExecutionItem Party Good Port Technology Instrument)
      (inside : item ∈ code.law.rawItems current word) : item.request ∈ code.actions := by
    apply supported
    rw [← code.law.inventory_requests_exact current 0 word]
    exact List.mem_map.mpr ⟨item,inside,rfl⟩
  simpa only [RawLaw.rawItems,code.law.inventory_length] using count (code.law.rawItems current word)
    (fun item inside => coverage.covered item.request (original item inside) item.before.technology (reachable item inside)) legal

theorem every_original_dynamically_bounded_word_is_enumerated
    (menu : List Technology) (coverage : Coverage code menu) (budget : Party × Good → ℚ)
    (current : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (supported : ∀ request ∈ word,request ∈ code.actions)
    (reachable : ∀ item ∈ code.law.rawItems current word,item.before.technology ∈ menu)
    (legal : ∀ item ∈ code.law.rawItems current word,code.law.Valid item.before item.request)
    (affordable : ∀ reading ∈ coverage.readings,
      code.law.totalDebit (code.law.rawItems current word) reading.axis.1 reading.axis.2 ≤ budget reading.axis) :
    word ∈ words code.actions (cap code coverage.readings budget) := by
  apply (mem_words_iff _ _ _).mpr
  refine ⟨?_,supported⟩
  have paid := every_legal_dynamically_covered_word_pays_its_count code menu coverage current word supported reachable legal
  have total : debit code coverage.readings (code.law.rawItems current word) ≤
      (coverage.readings.map fun reading => budget reading.axis / reading.amount).sum := by
    unfold debit
    apply List.sum_le_sum
    intro reading inside
    exact div_le_div_of_nonneg_right (affordable reading inside) reading.positive.le
  exact_mod_cast (paid.trans total).trans (Nat.le_ceil _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic.Cost
