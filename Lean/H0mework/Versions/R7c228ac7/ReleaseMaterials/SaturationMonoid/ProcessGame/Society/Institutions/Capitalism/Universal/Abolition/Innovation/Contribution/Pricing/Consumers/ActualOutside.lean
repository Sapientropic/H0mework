import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualMechanism

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program

private theorem two_distinct_items_fill_the_budget {α : Type} (items : List α) (first second : α)
    (different : first ≠ second) (bounded : items.length ≤ 2) (one : first ∈ items) (two : second ∈ items) :
    items = [first,second] ∨ items = [second,first] := by
  cases items with
  | nil => cases one
  | cons a rest =>
      cases rest with
      | nil =>
          have oneEq := List.mem_singleton.mp one
          have twoEq := List.mem_singleton.mp two
          exact (different (oneEq.trans twoEq.symm)).elim
      | cons b tail =>
          have tailEmpty : tail = [] := List.length_eq_zero_iff.mp (by simpa using bounded)
          subst tail
          simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
          rcases one with one | one <;> rcases two with two | two <;> simp_all

private theorem a_paid_life_occurs_in_the_original_operations
    (law : RawLaw Bool Bool Bool Unit Unit) (current : Raw) (word : List R) (person : Bool)
    (paid : Exit.Necessity.BundlePaid law current word person [(true,1)] .necessity) :
    Operation.use person [(true,(1:ℚ))] Use.necessity ∈ word.map Request.operation := by
  rcases paid with empty | ⟨item,original,_accepted,matched⟩
  · cases empty
  · have requestOriginal : item.request ∈ word := by
      rw [← law.inventory_requests_exact current 0 word]
      exact List.mem_map.mpr ⟨item,original,rfl⟩
    exact List.mem_map.mpr ⟨item.request,requestOriginal,(Exit.Necessity.useMatches_iff item.request.operation person [(true,1)] .necessity).mp matched⟩

theorem two_paid_lives_use_the_entire_original_two_request_budget
    (law : RawLaw Bool Bool Bool Unit Unit) (current : Raw) (word : List R)
    (bounded : word.length ≤ 2)
    (first : Exit.Necessity.BundlePaid law current word false [(true,1)] .necessity)
    (second : Exit.Necessity.BundlePaid law current word true [(true,1)] .necessity) :
    word.map Request.operation = [.use false [(true,1)] .necessity,.use true [(true,1)] .necessity] ∨
      word.map Request.operation = [.use true [(true,1)] .necessity,.use false [(true,1)] .necessity] := by
  apply two_distinct_items_fill_the_budget
  · decide
  · simpa only [List.length_map] using bounded
  · exact a_paid_life_occurs_in_the_original_operations law current word false first
  · exact a_paid_life_occurs_in_the_original_operations law current word true second

private theorem an_actual_life_has_only_its_own_original_food_cost
    (law : RawLaw Bool Bool Bool Unit Unit) (before : Raw) (request : R) (index : Nat)
    (bearer person good : Bool) (valid : law.Valid before request)
    (operation : request.operation = .use bearer [(true,1)] .necessity) :
    Arithmetic.completeItemIncome law ⟨index,before,request⟩ person good =
      if bearer = person ∧ good = true then -1 else 0 := by
  have debit : law.actualDebit before request = locate bearer [(true,1)] := by
    rw [RawLaw.actualDebit,if_pos valid]
    simp only [RawLaw.debit,operation]
  have credit : law.actualCredit before request = [] := by
    rw [RawLaw.actualCredit,if_pos valid]
    simp only [RawLaw.credit,operation]
  simp only [Arithmetic.completeItemIncome,debit,credit,if_pos valid,Arithmetic.rawClaimIncome,operation]
  cases bearer <;> cases person <;> cases good <;> norm_num [flowAt,locate,amount]

theorem every_two_request_paid_outside_word_has_no_spare_productive_income
    (law : RawLaw Bool Bool Bool Unit Unit) (current : Raw) (word : List R)
    (bounded : word.length ≤ 2)
    (accepted : ∀ item ∈ law.rawItems current word,law.Valid item.before item.request)
    (first : Exit.Necessity.BundlePaid law current word false [(true,1)] .necessity)
    (second : Exit.Necessity.BundlePaid law current word true [(true,1)] .necessity)
    (person good : Bool) :
    Arithmetic.completeIncome law (law.rawItems current word) person good = if good then -1 else 0 := by
  have choices := two_paid_lives_use_the_entire_original_two_request_budget law current word bounded first second
  have size : word.length = 2 := by
    rcases choices with left | right
    · simpa only [List.length_map,List.length_cons,List.length_nil] using congrArg List.length left
    · simpa only [List.length_map,List.length_cons,List.length_nil] using congrArg List.length right
  cases word with
  | nil => cases size
  | cons a rest =>
      cases rest with
      | nil => cases size
      | cons b tail =>
          have tailEmpty : tail = [] := List.length_eq_zero_iff.mp (by simpa using size)
          subst tail
          have firstValid := accepted ⟨0,current,a⟩ List.mem_cons_self
          have secondValid := accepted ⟨1,law.step current a,b⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
          change Arithmetic.completeItemIncome law ⟨0,current,a⟩ person good +
            (Arithmetic.completeItemIncome law ⟨1,law.step current a,b⟩ person good + 0) = _
          rcases choices with left | right
          · simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at left
            rw [an_actual_life_has_only_its_own_original_food_cost law current a 0 false person good firstValid left.1,
              an_actual_life_has_only_its_own_original_food_cost law _ b 1 true person good secondValid left.2]
            cases person <;> cases good <;> norm_num
          · simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at right
            rw [an_actual_life_has_only_its_own_original_food_cost law current a 0 true person good firstValid right.1,
              an_actual_life_has_only_its_own_original_food_cost law _ b 1 false person good secondValid right.2]
            cases person <;> cases good <;> norm_num

noncomputable section

theorem every_two_request_outside_word_has_its_exact_original_living_account
    (input : SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource.Input Bool Bool Bool Unit Unit)
    (current : Raw) (members : List Bool) (word : List R)
    (needs : ∀ person, input.law.necessities current person = [(true,1)])
    (memberFalse : false ∈ members) (memberTrue : true ∈ members)
    (generated : word ∈ Material.Migration.sourceWords input current 2)
    (checked : Outside.Checks input current members word) (person good : Bool) :
    Outside.value input current person good word = if good then -1 else 0 := by
  rw [Outside.a_checked_value_is_its_complete_original_account input current members word checked,
    ← Arithmetic.complete_income_is_the_original_full_account]
  have paidFalse := (checked.1.2.1 false memberFalse).1
  have paidTrue := (checked.1.2.1 true memberTrue).1
  rw [needs] at paidFalse paidTrue
  exact every_two_request_paid_outside_word_has_no_spare_productive_income input.law current word
    ((Material.Migration.sourceWords_complete input current 2 word).mp generated).1
    (fun item member => (checked.1.1 item member).1) paidFalse paidTrue person good

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
