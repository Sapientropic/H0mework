import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Compilers

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Source

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

abbrev Row (Party Good Port Technology Instrument : Type u) :=
  ExecutionItem Party Good Port Technology Instrument × (Party × Good)

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Origin" => ProgrammeFace.Origin Party Good Port Technology Instrument
local notation "Point" => ProgrammeFace.Point Party Good Port Technology Instrument
local notation "Debit" => Row Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

/-- Net debit in the original unit, at one exact instruction and address. -/
def loss (law : Law) (row : Debit) : ℚ :=
  let item := row.1
  flowAt (law.actualDebit item.before item.request) row.2.1 row.2.2 -
    flowAt (law.actualCredit item.before item.request) row.2.1 row.2.2

/-- Only execution action points can read a debit. A refused request can
occur in the source trace but it has no paid debit position here. -/
def itemsAt (law : Law) (origin : Origin) : Point → List Item
  | .action seed =>
    if seed.kind = .execution then
      (law.rawItems origin.1 origin.2).filter (fun item => decide
        (item.index = seed.index ∧ item.request.signer = seed.party ∧ law.Valid item.before item.request))
    else []
  | _ => []

def rowsAt (law : Law) (origin : Origin) (point : Point) : List Debit :=
  (itemsAt law origin point).flatMap (fun item =>
    (((law.actualDebit item.before item.request).map Prod.fst).dedup
      |>.filter (fun address => decide (0 < loss law (item, address))))
      |>.map (fun address => (item, address)))

theorem item_at_exact (law : Law) (origin : Origin) (point : Point) (item : Item)
    (present : item ∈ itemsAt law origin point) :
    item ∈ law.rawItems origin.1 origin.2 ∧ law.Valid item.before item.request ∧
      point = .action ⟨item.index, .execution, item.request.signer⟩ := by
  cases point with
  | action seed =>
    cases seed with
    | mk index kind party =>
      by_cases paid : kind = .execution
      · subst kind
        change item ∈ (law.rawItems origin.1 origin.2).filter (fun row => decide
          (row.index = index ∧ row.request.signer = party ∧ law.Valid row.before row.request)) at present
        obtain ⟨original, matched⟩ := List.mem_filter.mp present
        obtain ⟨position, signer, actual⟩ := of_decide_eq_true matched
        exact ⟨original, actual, by rw [position, signer]⟩
      · simp [itemsAt, paid] at present
  | source _ | party _ | relation _ | target _ => simp [itemsAt] at present

theorem row_at_exact (law : Law) (origin : Origin) (point : Point) (row : Debit)
    (present : row ∈ rowsAt law origin point) :
    row.1 ∈ law.rawItems origin.1 origin.2 ∧ law.Valid row.1.before row.1.request ∧
      point = .action ⟨row.1.index, .execution, row.1.request.signer⟩ ∧
      row.2 ∈ (law.actualDebit row.1.before row.1.request).map Prod.fst ∧ 0 < loss law row := by
  obtain ⟨item, atPoint, belongs⟩ := List.mem_flatMap.mp present
  obtain ⟨address, listed, same⟩ := List.mem_map.mp belongs
  cases same
  obtain ⟨original, actual, exactPoint⟩ := item_at_exact law origin point item atPoint
  obtain ⟨debit, positive⟩ := List.mem_filter.mp listed
  exact ⟨original, actual, exactPoint, List.mem_dedup.mp debit, of_decide_eq_true positive⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
