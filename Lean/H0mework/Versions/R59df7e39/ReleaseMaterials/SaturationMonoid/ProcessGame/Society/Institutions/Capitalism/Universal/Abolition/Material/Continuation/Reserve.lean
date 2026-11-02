import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Shared
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (policy : input.law.ReserveInsensitive)

def reserved (reserve : Party → Good → ℚ)
    (item : ExecutionItem Party Good Port Technology Instrument) :=
  { item with before := item.before.addReserve reserve }

include policy

omit [DecidableEq Port] in
theorem executed_items_addReserve
    (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ (input.law.execute current index word).items,
      input.law.Valid item.before item.request) :
    (input.law.execute (current.addReserve reserve) index word).items =
      ((input.law.execute current index word).items).map (reserved reserve) := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simp only [RawLaw.execute, List.forall_mem_cons] at accepted
      simp only [RawLaw.execute,
        input.law.step_addReserve policy current reserve nonnegative request accepted.1,
        ih _ (index + 1) accepted.2, List.map_cons, reserved]

omit [DecidableEq Port] in
theorem actualAndIndependent_addReserve
    (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (word : RawEvent Party Good Port Technology Instrument)
    (paid : ActualAndIndependent input current word) :
    ActualAndIndependent input (current.addReserve reserve) word := by
  have trace := executed_items_addReserve input policy current reserve nonnegative 0 word
    (fun item present => (paid item present).1)
  change input.law.rawItems (current.addReserve reserve) word =
    (input.law.rawItems current word).map (reserved reserve) at trace
  intro item present
  rw [trace] at present
  obtain ⟨original, source, rfl⟩ := List.mem_map.mp present
  have originalPaid := paid original source
  exact ⟨input.law.valid_addReserve policy _ reserve nonnegative _ originalPaid.1,
    input.law.valid_addReserve policy _ reserve nonnegative _ originalPaid.2.1, originalPaid.2.2⟩

omit [DecidableEq Port] in
theorem bundlePaid_addReserve
    (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (word : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ input.law.rawItems current word, input.law.Valid item.before item.request)
    (person : Party) (goods : Bundle Good) (purpose : Use)
    (paid : Exit.Necessity.BundlePaid input.law current word person goods purpose) :
    Exit.Necessity.BundlePaid input.law (current.addReserve reserve) word person goods purpose := by
  rcases paid with empty | ⟨item, present, valid, matched⟩
  · exact Or.inl empty
  · have trace := executed_items_addReserve input policy current reserve nonnegative 0 word accepted
    change input.law.rawItems (current.addReserve reserve) word =
      (input.law.rawItems current word).map (reserved reserve) at trace
    refine Or.inr ⟨reserved reserve item, ?_,
      input.law.valid_addReserve policy _ reserve nonnegative _ valid, matched⟩
    rw [trace]
    exact List.mem_map.mpr ⟨item, present, rfl⟩

omit [DecidableEq Port] in
theorem sharedPeriod_addReserve
    (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument)
    (paid : SharedPeriod input current members word) :
    SharedPeriod input (current.addReserve reserve) members word := by
  have accepted := fun item present => (paid.1 item present).1
  refine ⟨actualAndIndependent_addReserve input policy current reserve nonnegative word paid.1,
    ?_, ?_, paid.2.2.2⟩
  · intro person member
    rw [policy.necessities, policy.maintenance]
    exact ⟨bundlePaid_addReserve input policy current reserve nonnegative word accepted
        person _ _ (paid.2.1 person member).1,
      bundlePaid_addReserve input policy current reserve nonnegative word accepted
        person _ _ (paid.2.1 person member).2⟩
  · have trace := executed_items_addReserve input policy current reserve nonnegative 0 word accepted
    change input.law.rawItems (current.addReserve reserve) word =
      (input.law.rawItems current word).map (reserved reserve) at trace
    intro item present port required person
    rw [trace] at present
    obtain ⟨original, source, rfl⟩ := List.mem_map.mp present
    exact paid.2.2.1 original source port required person

omit [DecidableEq Port] in
theorem actualUse_addReserve
    (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (word : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ input.law.rawItems current word, input.law.Valid item.before item.request)
    (person : Party) (purpose : Use) (good : Good) :
    actualUse input (current.addReserve reserve) word person purpose good =
      actualUse input current word person purpose good := by
  have trace := executed_items_addReserve input policy current reserve nonnegative 0 word accepted
  change input.law.rawItems (current.addReserve reserve) word =
    (input.law.rawItems current word).map (reserved reserve) at trace
  simp only [actualUse, trace, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro item present
  have valid := accepted item present
  have enlarged := input.law.valid_addReserve policy item.before reserve nonnegative item.request valid
  have flow : input.law.actualDebit (item.before.addReserve reserve) item.request =
      input.law.actualDebit item.before item.request := by
    rw [RawLaw.actualDebit, if_pos enlarged, RawLaw.actualDebit, if_pos valid]
    rfl
  simp only [Function.comp_apply, reserved]
  rw [flow]

omit [DecidableEq Port] in
theorem originalNeedFloor_addReserve
    (origin current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ input.law.rawItems current word, input.law.Valid item.before item.request)
    (paid : OriginalNeedFloor input origin current members word) :
    OriginalNeedFloor input origin (current.addReserve reserve) members word := by
  simpa only [OriginalNeedFloor, actualUse_addReserve input policy current reserve nonnegative word accepted]
    using paid

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation
