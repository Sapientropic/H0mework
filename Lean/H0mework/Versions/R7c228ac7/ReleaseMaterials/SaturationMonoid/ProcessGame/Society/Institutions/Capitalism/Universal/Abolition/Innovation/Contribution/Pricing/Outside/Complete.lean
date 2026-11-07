import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (budget : Nat) (person : Party) (good : Good)

theorem generated_words_cover_exactly_the_original_adequate_budgeted_grammar
    (word : RawEvent Party Good Port Technology Instrument) :
    word ∈ words input current members budget ↔
      (word.length ≤ budget ∧ ∀ request ∈ word, request ∈ Material.Migration.sourceAlphabet input current) ∧
        Checks input current members word := by
  rw [word_mem_iff,Material.Migration.sourceWords_complete]

theorem an_outside_amount_is_returned_iff_a_real_adequate_alternative_exists :
    (sourceOutside input current members budget person good).isSome = true ↔
      ∃ word ∈ Material.Migration.sourceWords input current budget, Checks input current members word := by
  unfold sourceOutside
  cases generate input current members budget person good with
  | found result =>
      simp only [Option.isSome_some,true_iff]
      exact ⟨result.word,result.generated,result.checked⟩
  | obstructed failures =>
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
      rintro ⟨word,original,safe⟩
      exact (failures word original).refutes input current members safe

def nativeOutside := generate input current (Root.GeneratedLaw.members input current) budget person good

omit [DecidableEq Port] in
theorem native_members_are_the_original_root_census (index : Nat) :
    Root.GeneratedLaw.members input
      (Root.ProgrammeSource.rawCurrent input (Root.ProgrammeHistory.visitAt input index).current) =
        Source.ProgrammeFace.ActualBirth.participants input (Root.ProgrammeHistory.visitAt input index) :=
  Root.GeneratedLaw.members_at_original_visit input index

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside
