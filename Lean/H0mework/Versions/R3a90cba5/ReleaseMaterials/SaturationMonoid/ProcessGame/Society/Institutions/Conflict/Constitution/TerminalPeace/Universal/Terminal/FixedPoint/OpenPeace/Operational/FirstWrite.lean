import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt inventory primitiveScript)
open Reparation.Actual (Occurrence)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (loss : Occurrence seed community)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)
  (body : RawEvent Party Good Port Technology Instrument)

/-- Production credit requires a positive output at a registered position. -/
def firstProductionCheck : Decidable (Clearance.Joint.ProducesAtFirstWrite loss body) := by
  let before := endAt seed (Occurrence.history loss ++ Clearance.Joint.openingDrain loss)
  let items := inventory before (primitiveScript body)
  let credit (item : ExecutionItem Party Good Port Technology Instrument) :=
    (Boundary.Actual.materialLaw before).actualCredit item.before item.request
  let hit (item : ExecutionItem Party Good Port Technology Instrument) : Prop :=
    match item.request.operation with
    | .produce person => ∃ address ∈ addresses, address.1 = person ∧
        0 < flowAt (credit item) person address.2
    | _ => False
  haveI : DecidablePred hit := fun item => by
    unfold hit
    cases item.request.operation <;> infer_instance
  refine decidable_of_iff (∃ item ∈ items, hit item) ?_
  change (∃ item ∈ items, hit item) ↔ ∃ item ∈ items, ∃ person good,
    item.request.operation = .produce person ∧ 0 < flowAt (credit item) person good
  have exactAt (item : ExecutionItem Party Good Port Technology Instrument) :
      hit item ↔ ∃ person good, item.request.operation = .produce person ∧
        0 < flowAt (credit item) person good := by
    cases operation : item.request.operation <;> simp only [hit, operation, reduceCtorEq, false_and, exists_false]
    rename_i producer
    constructor
    · rintro ⟨address, _, _, credited⟩
      exact ⟨producer, address.2, rfl, credited⟩
    · rintro ⟨person, good, written, credited⟩
      cases Operation.produce.inj written
      exact ⟨(producer, good), covered _, rfl, credited⟩
  constructor
  · rintro ⟨item, listed, posted⟩
    exact ⟨item, listed, (exactAt item).mp posted⟩
  · rintro ⟨item, listed, posted⟩
    exact ⟨item, listed, (exactAt item).mpr posted⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational
