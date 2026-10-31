import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Access

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financial

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

private theorem original_index_lower (current : RawCurrent Party Good Technology Instrument)
    (start : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (member : item ∈ (law.execute current start word).items) : start ≤ item.index := by
  induction word generalizing current start with
  | nil => simp [RawLaw.execute] at member
  | cons request tail prior =>
      simp only [RawLaw.execute, List.mem_cons] at member
      rcases member with rfl | later
      · exact le_refl _
      · exact (Nat.le_succ start).trans (prior _ _ later)

private theorem same_index_same_original (current : RawCurrent Party Good Technology Instrument)
    (start : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (left right : ExecutionItem Party Good Port Technology Instrument)
    (first : left ∈ (law.execute current start word).items)
    (second : right ∈ (law.execute current start word).items)
    (same : left.index = right.index) : left = right := by
  induction word generalizing current start with
  | nil => simp [RawLaw.execute] at first
  | cons request tail prior =>
      simp only [RawLaw.execute, List.mem_cons] at first second
      rcases first with rfl | first
      · rcases second with rfl | second
        · rfl
        · have lower := original_index_lower law _ _ tail right second
          simp only at same
          omega
      · rcases second with rfl | second
        · have lower := original_index_lower law _ _ tail left first
          simp only at same
          omega
        · exact prior _ _ first second

theorem original_index_injective (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    Function.Injective (fun item : OriginalItem law current word => item.val.index) := by
  intro left right same
  exact Subtype.ext (same_index_same_original law current 0 word left.val right.val
    left.property right.property same)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financial
