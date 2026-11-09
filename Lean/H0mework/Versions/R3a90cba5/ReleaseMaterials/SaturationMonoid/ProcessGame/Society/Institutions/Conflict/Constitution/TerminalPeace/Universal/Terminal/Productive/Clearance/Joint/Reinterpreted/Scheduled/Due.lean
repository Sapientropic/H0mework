import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.History
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.RecipeMenu

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.Scheduled

open Capitalism.Universal.Source.Program
open Reparation.Actual (Script)
open FixedPoint (Recipe InReserve)
open FixedPoint.OpenPeace.Operational (RecipeMenu RejectedRecipes chooseRecipe)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

/-- One live original resident, with its already checked protection
through the next due period. Old balances may remain open. -/
structure State (loss : Reparation.Actual.Occurrence seed community)
    (front : Script Party Good Port Technology Instrument) (quantum : ℚ) where
  current : Current loss front
  base : RawCurrent Party Good Technology Instrument
  recipe : Recipe current.programme (originalRaw loss) (people loss front) base quantum
  reserve : InReserve base current.physical.raw

variable {quantum : ℚ} (before : State loss front quantum)

structure DueWrite where
  period : PeriodWrite before.current before.current.programme
  next : State loss front quantum
  actual : next.current = period.next
  elapsed : before.current.physical.raw.clock + quantum ≤ next.current.physical.raw.clock

def writeDue : DueWrite before := by
  let move := before.recipe.moveAt before.current.physical.raw before.reserve
  let period := writePeriod before.current before.current.programme (.refl _) move
  have stock : period.next.physical.raw = move.next := period.exactStock
  refine ⟨period, ⟨period.next, before.base, period.programmeNext.symm ▸ before.recipe, ?_⟩, rfl, ?_⟩
  · exact stock.symm ▸ before.recipe.next_reserved _ _
  · exact stock.symm ▸ before.recipe.next_clock _ _

def afterRefusal {Issue : Type} (refused : Refused before.current Issue) : State loss front quantum :=
  ⟨refused.next, before.base, refused.keepsProgramme.symm ▸ before.recipe,
    (congrArg (fun physical => physical.raw) refused.keepsPhysical).symm ▸ before.reserve⟩

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (initial : Current loss front)
  (menu : RecipeMenu initial.programme initial.physical.raw)

def openDue :
    Refused initial (RejectedRecipes initial.programme (originalRaw loss) initial.physical.raw (people loss front) menu) ⊕
      State loss front (initial.programme.law.duration initial.physical.raw) :=
  match chooseRecipe initial.programme (originalRaw loss) initial.physical.raw (people loss front) menu with
  | .inl denied => .inl (refuse initial denied)
  | .inr checked => .inr ⟨initial, initial.physical.raw, checked.recipe, ⟨fun _ _ => le_rfl, rfl, rfl⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.Scheduled
