import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Totals
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.Root.Bound
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Base
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Family

/-! Actual material flows are read once, at the source execution tick.
Bookkeeping transports the same physical state and has zero material flow. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Material

open Source Source.Program Source.ProgrammeControl
open Source.ProgrammeControl.Kernel.AssetAuthority
open Financial.Installation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def rawAt (state : Cursor.State input) :=
  ProgrammeSource.rawCurrent input (Cursor.physicalVisit input state).current

def wordAt (state : Cursor.State input) :=
  ProgrammeSource.rawEvent input (Cursor.physicalVisit input state).current

def familyAt (state : Cursor.State input) :=
  Structural.familyAtVisit input (Cursor.physicalVisit input state)

def membersAt (state : Cursor.State input) :=
  ProgrammeFace.ActualBirth.participants input (Cursor.physicalVisit input state)

def freshAmount (state : Cursor.State input) (amount : ℚ) : ℚ :=
  if Cursor.FreshBody input state then amount else 0

def use (purpose : Use) (state : Cursor.State input) (location : Party × Good) : ℚ :=
  freshAmount input state (Source.Material.total (input.law.rawItems (rawAt input state) (wordAt input state))
    (fun item => Decoder.consumedFor input.law purpose item location.1 location.2))

def other (state : Cursor.State input) (location : Party × Good) : ℚ :=
  freshAmount input state (Source.Material.total (input.law.rawItems (rawAt input state) (wordAt input state))
    (fun item => Source.Material.otherPaid input.law item location.1 location.2))

def dependent (state : Cursor.State input) (location : Party × Good) : ℚ :=
  freshAmount input state (Source.Material.dependentTotal input.law (rawAt input state) (wordAt input state)
    (familyAt input state) (membersAt input state) location)

def independent (state : Cursor.State input) (location : Party × Good) : ℚ :=
  freshAmount input state (Source.Material.independentTotal input.law (rawAt input state) (wordAt input state)
    (familyAt input state) (membersAt input state) location)

def unresolved (state : Cursor.State input) (location : Party × Good) : ℚ :=
  freshAmount input state (Source.Material.unresolvedTotal input.law (rawAt input state) (wordAt input state)
    (familyAt input state) (membersAt input state) location)

private theorem fresh_nonnegative (state : Cursor.State input) (amount : ℚ) (nonnegative : 0 ≤ amount) :
    0 ≤ freshAmount input state amount := by
  unfold freshAmount
  split
  · exact nonnegative
  · exact le_refl 0

theorem quantities_nonnegative (state : Cursor.State input) (location : Party × Good) :
    0 ≤ use input .necessity state location ∧ 0 ≤ use input .maintenance state location ∧
      0 ≤ dependent input state location ∧ 0 ≤ independent input state location ∧
      0 ≤ unresolved input state location ∧ 0 ≤ other input state location := by
  have acquired := Source.Material.totals_nonnegative input.law (rawAt input state) (wordAt input state)
    (familyAt input state) (membersAt input state) location
  have useNonnegative (purpose : Use) : 0 ≤ use input purpose state location :=
    fresh_nonnegative input state _ (Source.Material.total_nonnegative _ _
      (fun item _ => Source.Material.consumed_nonnegative input.law purpose item location.1 location.2))
  exact ⟨useNonnegative _, useNonnegative _, fresh_nonnegative input state _ acquired.1,
    fresh_nonnegative input state _ acquired.2.1, fresh_nonnegative input state _ acquired.2.2,
    fresh_nonnegative input state _ (Source.Material.total_nonnegative _ _
      (fun item _ => Source.Material.other_nonnegative input.law item location.1 location.2))⟩

theorem actual_balance (state : Cursor.State input) (location : Party × Good) :
    (rawAt input (Cursor.next input state)).stock location.1 location.2 +
        use input .necessity state location + use input .maintenance state location + other input state location =
      (rawAt input state).stock location.1 location.2 + dependent input state location +
        independent input state location + unresolved input state location := by
  by_cases fresh : Cursor.FreshBody input state
  · have nextRaw : rawAt input (Cursor.next input state) =
        input.law.next (rawAt input state) (wordAt input state) :=
      (congrArg (ProgrammeSource.rawCurrent input)
        (Cursor.physical_next_of_fresh input state fresh)).trans (ProgrammeSource.actual_raw_next input _)
    simp only [nextRaw, use, other, dependent, independent, unresolved, freshAmount, if_pos fresh]
    exact Source.Material.actual_material_balance input.law _ _ _ _ location
  · have same := congrArg (fun visit => ProgrammeSource.rawCurrent input visit.current)
      (Cursor.physical_next_of_bookkeeping input state fresh)
    simp only [rawAt] at same ⊢
    simp [same, use, other, dependent, independent, unresolved, freshAmount, fresh]

theorem positive_dependence_returns_actual_control (state : Cursor.State input) (location : Party × Good)
    (positive : 0 < dependent input state location) :
    Cursor.FreshBody input state ∧
      Nonempty (ControlUse input.law (rawAt input state) (wordAt input state) (familyAt input state)) := by
  by_cases fresh : Cursor.FreshBody input state
  · exact ⟨fresh, Source.Material.positive_total_has_original_control input.law _ _ _ _ location
      (by simpa only [dependent, freshAmount, if_pos fresh] using positive)⟩
  · simp [dependent, freshAmount, fresh] at positive

def unresolvedItem (state : Cursor.State input) (location : Party × Good)
    (positive : 0 < unresolved input state location) : RootFace.Item input (Cursor.physicalVisit input state) :=
  (Source.Material.unresolvedOriginal input.law (rawAt input state) (wordAt input state)
    (familyAt input state) (membersAt input state) location (by
      by_cases fresh : Cursor.FreshBody input state
      · simpa only [unresolved, freshAmount, if_pos fresh] using positive
      · simp [unresolved, freshAmount, fresh] at positive)).val

def unresolvedOrigin (state : Cursor.State input) (location : Party × Good)
    (positive : 0 < unresolved input state location) : Financial.InstructionOrigin input :=
  RootFace.original input (Cursor.physicalVisit input state) (unresolvedItem input state location positive)

theorem unresolved_keeps_original_instruction (state : Cursor.State input)
    (location : Party × Good) (positive : 0 < unresolved input state location) :
    (unresolvedOrigin input state location positive).instruction? input =
      some (unresolvedItem input state location positive).val :=
  RootFace.original_decodes_exact_item input _ _

#print axioms actual_balance
#print axioms positive_dependence_returns_actual_control

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Material
