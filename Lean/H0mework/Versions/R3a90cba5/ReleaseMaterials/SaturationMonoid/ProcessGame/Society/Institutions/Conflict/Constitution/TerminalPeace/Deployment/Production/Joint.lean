import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Production.Source
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint.Search

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open Conflict.Consumers.Evolving (W)
open Supply.Consumers (refillWord)
open FixedPoint.OpenPeace.Operational (RepeatCode RecipeMenu)
open FixedPoint.OpenPeace.Operational.Joint (Search search)
open FixedPoint.OpenPeace.Operational.Repair (Decision select)
open private actual_roster from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalShortage
open private original_need_cut from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalSource

private abbrev Prog := ProgrammeSource.Input Bool Bool Bool Unit Unit

def emptyCode (input : Prog) (same : input = revised) (raw : Original.Raw) : RepeatCode input raw :=
  { codeFor input same raw with production := [] }

def emptyMenu (input : Prog) (same : input = revised) (raw : Original.Raw) : RecipeMenu input raw :=
  [emptyCode input same raw]

private def jointAt (input : Prog) (same : input = revised)
    (origin raw : Original.Raw) (roster : List Bool) (incumbent : W) (limit : Nat) :=
  search input origin raw roster (emptyMenu input same raw) incumbent (emptyCode input same raw) limit

private def noSingleEdit {input : Prog} {origin raw : Original.Raw} {roster : List Bool}
    {offers : RecipeMenu input raw} {incumbent : W} :
    Decision input origin raw roster offers incumbent → Bool
  | .exhausted .. => true
  | _ => false

theorem the_empty_offer_exhausts_single_edits (input : Prog) (same : input = revised)
    (raw : Original.Raw) (stock : raw = chargedStock) (incumbent : W) (word : incumbent = refillWord) :
    noSingleEdit (select input (originalRaw loss) raw (people loss front) (emptyMenu input same raw) incumbent) = true := by
  subst input raw incumbent
  rw [original_need_cut]
  rcases actual_roster with roster | roster <;> rw [roster] <;> decide +kernel

private abbrev originalLimit := chargedStock.round + refillWord.length
private abbrev selection := jointAt revised rfl (Original.snapshot 111 113) chargedStock [false, true] refillWord originalLimit

private def attainedWidth {input : Prog} {origin raw : Original.Raw} {roster : List Bool}
    {offers : RecipeMenu input raw} {incumbent : W} {basis : RepeatCode input raw} {limit : Nat} :
    Search input origin raw roster offers incumbent basis limit → Option Nat
  | .pending _ => none
  | .found width _ _ _ => some width

set_option maxHeartbeats 1200000 in
private theorem sourcePays : selection.word.isSome = true := by decide +kernel

def jointWord : W := selection.word.get sourcePays

set_option maxHeartbeats 1800000 in
theorem named_joint_source_writes_at_width_four (input : Prog) (same : input = revised)
    (raw : Original.Raw) (stock : raw = chargedStock) (incumbent : W) (word : incumbent = refillWord) :
    let actual := jointAt input same (originalRaw loss) raw (people loss front) incumbent (raw.round + incumbent.length)
    actual.word = some jointWord ∧ attainedWidth actual = some 4 := by
  subst input raw incumbent
  rw [original_need_cut]
  rcases actual_roster with roster | roster <;> rw [roster] <;> dsimp only <;> constructor <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
