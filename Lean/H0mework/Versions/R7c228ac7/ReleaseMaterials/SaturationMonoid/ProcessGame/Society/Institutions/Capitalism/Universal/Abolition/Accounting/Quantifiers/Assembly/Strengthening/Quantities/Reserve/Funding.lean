import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve

open Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

local notation "Current" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

def Accepted (current : Current) (word : Word) : Prop :=
  ∀ item ∈ law.rawItems current word, law.Valid item.before item.request

theorem the_original_word_is_executable_iff_its_gates_and_joint_stock_fit
    (current : Current) (word : Word) (reserve : Party → Good → ℚ) :
    Accepted law (current.addReserve reserve) word ↔
      Guards law reserve current word ∧ FitsThrough law reserve current word := by
  have exactFrom (index : Nat) :
      (∀ item ∈ (law.execute (current.addReserve reserve) index word).items,
        law.Valid item.before item.request) ↔
      Guards law reserve current word ∧ FitsThrough law reserve current word := by
    induction word generalizing current index with
    | nil => simp [RawLaw.execute, Guards, FitsThrough]
    | cons request tail ih =>
        simp only [RawLaw.execute, List.forall_mem_cons, Guards, FitsThrough]
        constructor
        · rintro ⟨first, rest⟩
          obtain ⟨gates, stock⟩ := (valid_iff_guards_and_stock law current request reserve).mp first
          rw [RawLaw.step, if_pos first, paid_step_carries_the_exact_reserve] at rest
          obtain ⟨later, enough⟩ := (ih (law.paidStep current request) (index + 1)).mp rest
          exact ⟨⟨gates, later⟩, stock, enough⟩
        · rintro ⟨⟨gates, later⟩, stock, enough⟩
          have first := (valid_iff_guards_and_stock law current request reserve).mpr ⟨gates, stock⟩
          refine ⟨first, ?_⟩
          rw [RawLaw.step, if_pos first, paid_step_carries_the_exact_reserve]
          exact (ih (law.paidStep current request) (index + 1)).mpr ⟨later, enough⟩
  exact exactFrom 0

theorem the_exact_domain_of_nonnegative_reserves
    (current : Current) (word : Word)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ bearer good, 0 ≤ reserve bearer good) :
    Accepted law (current.addReserve reserve) word ↔ Guards law reserve current word ∧
      ∀ bearer good, minimumReserve law current word bearer good ≤ reserve bearer good := by
  rw [the_original_word_is_executable_iff_its_gates_and_joint_stock_fit,
    joint_reserve_bound_is_exact law current word reserve nonnegative]

theorem the_generated_reserve_is_jointly_attained_and_globally_least
    (current : Current) (word : Word)
    (gates : Guards law (minimumReserve law current word) current word) :
    Accepted law (current.addReserve (minimumReserve law current word)) word ∧
    ∀ reserve, (∀ bearer good, 0 ≤ reserve bearer good) →
      Accepted law (current.addReserve reserve) word →
      ∀ bearer good, minimumReserve law current word bearer good ≤ reserve bearer good := by
  refine ⟨?_, ?_⟩
  · exact (the_exact_domain_of_nonnegative_reserves law current word _
      (minimumReserve_nonnegative law current word)).mpr ⟨gates, fun _ _ => le_rfl⟩
  · intro reserve nonnegative actual
    exact ((the_exact_domain_of_nonnegative_reserves law current word reserve nonnegative).mp actual).2

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve
