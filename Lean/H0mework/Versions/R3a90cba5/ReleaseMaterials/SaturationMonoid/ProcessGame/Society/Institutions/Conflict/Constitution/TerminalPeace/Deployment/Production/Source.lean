import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Review
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalShortage
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Repair

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open Conflict.Consumers.Evolving (W life)
open TerminalPeace.Supply (grow)
open Supply.Consumers (refillWord)
open FixedPoint.OpenPeace.Operational (RepeatCode RecipeMenu RecipeIssue)
open FixedPoint.OpenPeace.Operational.Repair (select)
open private actual_roster shortageAt from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalShortage
open private original_need_cut from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalSource
open private posted from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Review

private abbrev Prog := ProgrammeSource.Input Bool Bool Bool Unit Unit

def registeredOffers (input : Prog) (same : input = revised) (raw : Original.Raw) : RecipeMenu input raw :=
  let code := codeFor input same raw
  [{ code with production := List.replicate 4 (life true) },
   { code with production := [grow false, grow true, life true] }]

private def pick (input : Prog) (same : input = revised)
    (origin raw : Original.Raw) (roster : List Bool) (incumbent : W) :=
  select input origin raw roster (registeredOffers input same raw) incumbent

private abbrev namedChoice := pick revised rfl (Original.snapshot 111 113) chargedStock [false, true] refillWord

private theorem namedChoiceGenerates : namedChoice.generatedWord.isSome = true := by
  decide +kernel

def generatedWord : W :=
  namedChoice.generatedWord.get namedChoiceGenerates

theorem generated_actions : generatedWord = [life false, grow false, grow true, life true] := by
  decide +kernel

private def unmetNeed {input : Prog} {origin raw : Original.Raw} {roster : List Bool}
    {code : RepeatCode input raw} (issue : RecipeIssue input origin raw roster code) :
    Option (Bool × Use × Bool × ℚ) :=
  match issue with
  | .production (.unpaid (.originalNeed need)) => some need.cell
  | _ => none

private def refuses {input : Prog} {origin raw : Original.Raw} {roster : List Bool}
    {incumbent : W} {same : input = revised}
    (decision : FixedPoint.OpenPeace.Operational.Repair.Decision input origin raw roster
      (registeredOffers input same raw) incumbent) :
    Option (Option (Nat × Bool × Bool × ℚ × ℚ) × Option (Bool × Use × Bool × ℚ)) :=
  match decision with
  | .generated each _ | .exhausted each _ =>
    some (shortageAt (each ⟨0, by change 0 < 2; decide⟩),
      unmetNeed (each ⟨1, by change 1 < 2; decide⟩))
  | .registered _ => none

theorem pendingWord : pending.live.current.recipe.move.word = refillWord := by
  change visit.next.native.recipe.move.word = _
  have same : visit.next.native.recipe.move.word = visit.source.next.recipe.move.word := by
    generalize visit = selected
    cases selected <;> rfl
  rw [same, posted]
  exact startWord

set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 512 in
theorem named_source_compiles_the_new_production (input : Prog) (same : input = revised)
    (raw : Original.Raw) (stock : raw = chargedStock)
    (incumbent : W) (word : incumbent = refillWord) :
    let decision := pick input same (originalRaw loss) raw (people loss front) incumbent
    decision.generatedWord = some generatedWord ∧
      refuses decision = some (some (3, true, true, 1/2, 1), some (false, .necessity, true, 1)) := by
  subst input raw incumbent
  rw [original_need_cut]
  rcases actual_roster with roster | roster <;> rw [roster] <;> dsimp only <;> constructor <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
