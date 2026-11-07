import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Replay
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.CursorRead

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def original := Financial.Installation.Runtime.frames input depth count
def originalCursor := (original input depth count).cursor input
def originalRaw := Financial.Installation.Runtime.physical input (original input depth count)
def originalWord := ProgrammeSource.rawEvent input
  (Financial.Installation.Cursor.physicalVisit input (originalCursor input depth count)).current

/-- Only the original tick's material body enters the representation.
Bookkeeping contributes no empty period and hence no extra clock tick. -/
def cutPast : List (Compile.RawInput Party Good Port Technology Instrument) :=
  if Financial.Installation.Cursor.FreshBody input (originalCursor input depth count) then
    [.execute (reencoded input (originalRaw input depth count) (originalWord input depth count))]
  else []

def cutState := Physical.Public.stateAt input depth count 0 0 [] (cutPast input depth count)

def sourceRaw := ProgrammeSource.rawCurrent input
  (Financial.Installation.Cursor.physicalVisit input
    (Financial.Installation.Cursor.next input (originalCursor input depth count))).current

theorem the_cut_starts_at_the_literal_original_raw :
    (Actual.initial input depth count).raw = originalRaw input depth count := rfl

theorem the_source_generated_prefix_reads_the_original_financial_next :
    (cutState input depth count).raw = sourceRaw input depth count := by
  by_cases fresh : Financial.Installation.Cursor.FreshBody input (originalCursor input depth count)
  · have replay := (reencoded_reads_the_same_original_next input (Actual.initial input depth count)
      (originalWord input depth count)).2
    rw [the_cut_starts_at_the_literal_original_raw] at replay
    unfold cutState cutPast
    rw [if_pos fresh]
    change (Physical.Public.compile input (Actual.initial input depth count)
      (.execute (reencoded input (originalRaw input depth count) (originalWord input depth count)))).next.raw = _
    rw [replay]
    unfold sourceRaw
    rw [Financial.Installation.Cursor.physical_next_of_fresh input _ fresh,ProgrammeSource.actual_raw_next]
    rfl
  · have same := Financial.Installation.Cursor.physical_next_of_bookkeeping input
      (originalCursor input depth count) fresh
    unfold cutState cutPast
    rw [if_neg fresh]
    change originalRaw input depth count = sourceRaw input depth count
    unfold sourceRaw
    rw [same]
    rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix
