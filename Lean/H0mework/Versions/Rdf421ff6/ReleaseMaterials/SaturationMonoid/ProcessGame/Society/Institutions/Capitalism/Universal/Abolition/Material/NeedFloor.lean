import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Checks

/-! Necessity floors are read from the original current, before review fees.
Payments are sums of actual source debits, so split delivery is admitted and
relabeling an external fee as subsistence is not. This is a material readout,
not an additional responsibility ledger. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

def actualUse (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (person : Party) (purpose : Use) (good : Good) : ℚ :=
  ((input.law.rawItems current word).map fun item =>
    match item.request.operation with
    | .use bearer _ kind =>
        if bearer = person ∧ kind = purpose then
          flowAt (input.law.actualDebit item.before item.request) person good else 0
    | _ => 0).sum

/-- Each cell is a finite projection of an original member's source bundle.
Repeated goods use the bundle's total demand rather than its first entry. -/
def originalRequirements (origin : RawCurrent Party Good Technology Instrument)
    (members : List Party) : List (Party × Use × Good × ℚ) :=
  members.flatMap fun person =>
    (input.law.necessities origin person).map (fun lot =>
      (person, .necessity, lot.1, amount Good (input.law.necessities origin person) lot.1)) ++
    (input.law.mandatoryMaintenance origin person).map (fun lot =>
      (person, .maintenance, lot.1, amount Good (input.law.mandatoryMaintenance origin person) lot.1))

def OriginalNeedFloor (origin current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ cell ∈ originalRequirements input origin members,
    cell.2.2.2 ≤ actualUse input current word cell.1 cell.2.1 cell.2.2.1

instance (origin current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (OriginalNeedFloor input origin current members word) := by
  unfold OriginalNeedFloor
  infer_instance

structure NeedFloorIssue (origin current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) where
  cell : Party × Use × Good × ℚ
  original : cell ∈ originalRequirements input origin members
  deficit : actualUse input current word cell.1 cell.2.1 cell.2.2.1 < cell.2.2.2

theorem NeedFloorIssue.refutes {origin current : RawCurrent Party Good Technology Instrument}
    {members : List Party} {word : RawEvent Party Good Port Technology Instrument}
    (issue : NeedFloorIssue input origin current members word) :
    ¬ OriginalNeedFloor input origin current members word :=
  fun checked => (not_le_of_gt issue.deficit) (checked issue.cell issue.original)

inductive NeedFloorDecision (origin current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) : Type
  | accepted (checked : OriginalNeedFloor input origin current members word)
  | rejected (issue : NeedFloorIssue input origin current members word)

def checkOriginalNeedFloor (origin current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    NeedFloorDecision input origin current members word :=
  match inspectList (fun cell : Party × Use × Good × ℚ =>
      cell.2.2.2 ≤ actualUse input current word cell.1 cell.2.1 cell.2.2.1)
      (originalRequirements input origin members) with
  | .clear checked => .accepted checked
  | .failure cell original failed => .rejected ⟨cell, original, lt_of_not_ge failed⟩

theorem original_necessity_is_paid
    {origin current : RawCurrent Party Good Technology Instrument}
    {members : List Party} {word : RawEvent Party Good Port Technology Instrument}
    (checked : OriginalNeedFloor input origin current members word)
    (person : Party) (present : person ∈ members)
    (lot : Good × ℚ) (required : lot ∈ input.law.necessities origin person) :
    amount Good (input.law.necessities origin person) lot.1 ≤ actualUse input current word person .necessity lot.1 := by
  exact checked (person, .necessity, lot.1, amount Good (input.law.necessities origin person) lot.1)
    (List.mem_flatMap.mpr ⟨person, present,
      List.mem_append_left _ (List.mem_map.mpr ⟨lot, required, rfl⟩)⟩)

theorem original_maintenance_is_paid
    {origin current : RawCurrent Party Good Technology Instrument}
    {members : List Party} {word : RawEvent Party Good Port Technology Instrument}
    (checked : OriginalNeedFloor input origin current members word)
    (person : Party) (present : person ∈ members)
    (lot : Good × ℚ) (required : lot ∈ input.law.mandatoryMaintenance origin person) :
    amount Good (input.law.mandatoryMaintenance origin person) lot.1 ≤ actualUse input current word person .maintenance lot.1 := by
  exact checked (person, .maintenance, lot.1, amount Good (input.law.mandatoryMaintenance origin person) lot.1)
    (List.mem_flatMap.mpr ⟨person, present,
      List.mem_append_right _ (List.mem_map.mpr ⟨lot, required, rfl⟩)⟩)

#print axioms checkOriginalNeedFloor
#print axioms original_necessity_is_paid
#print axioms original_maintenance_is_paid

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material
