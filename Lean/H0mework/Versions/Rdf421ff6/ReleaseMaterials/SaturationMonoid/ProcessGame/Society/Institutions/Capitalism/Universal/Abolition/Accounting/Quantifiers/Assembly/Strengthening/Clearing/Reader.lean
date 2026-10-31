import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  (boundary : Nat) (plan : RawEvent Party Good Port Technology Instrument)
  (fallback : Macro.Raw.Reader input depth count)

/-- The finite source plan owns its actual raw positions. Once exhausted,
the same reader returns to the original open source. Native accounting heads
do not append a raw position. -/
def reader : Macro.Raw.Reader input depth count := fun cursor account =>
  if boundary ≤ cursor.past.length then
    match plan[cursor.past.length - boundary]? with
    | some request => .primitive request
    | none => fallback cursor account
  else fallback cursor account

variable (cursor : Physical.Cursor Party Good Port Technology Instrument)
  (account : (Abolition.Root.Epoch.Finance.process input depth count).GeneratedState)

theorem each_actual_position_reads_its_original_primitive
    (index : Nat) (request : Request Party Good Port Technology Instrument)
    (position : cursor.past.length = boundary + index) (listed : plan[index]? = some request) :
    reader boundary plan fallback cursor account = .primitive request := by
  have available : boundary ≤ cursor.past.length := by omega
  have offset : cursor.past.length - boundary = index := by omega
  simp only [reader,if_pos available,offset,listed]

theorem exhaustion_returns_the_same_actual_open_reader
    (finished : boundary + plan.length ≤ cursor.past.length) :
    reader boundary plan fallback cursor account = fallback cursor account := by
  have available : boundary ≤ cursor.past.length := by omega
  have outside : plan.length ≤ cursor.past.length - boundary := by omega
  simp only [reader,if_pos available,List.getElem?_eq_none outside]

theorem an_earlier_cut_uses_its_original_reader
    (earlier : cursor.past.length < boundary) :
    reader boundary plan fallback cursor account = fallback cursor account := by
  simp only [reader,if_neg (by omega : ¬ boundary ≤ cursor.past.length)]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
