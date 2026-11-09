import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalReview

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OriginalReview

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Conflict.Consumers.Evolving (W life)
open Runtime.Viability (Move)
open OriginalRecipe (programme originalRecipe periodPasses paidAt)
open TerminalPeace.Supply (grow personalWord)

noncomputable section

local notation "OriginalOpening" => OriginalRecipe.opening

private def reorder : ProductionOffer Bool Bool Bool Unit Unit :=
  { OriginalRecipe.offer with pilot := [grow true, grow true, life true, grow false, grow false, life false] }

private def revised := reviseProgramme programme reorder

private theorem opening_eq : OriginalOpening = Original.snapshot 117 107 := Settlement.settled_raw

private theorem personal_registration (person : Bool) :
    Supply.Registered revised OriginalOpening (personalWord person) := by
  intro request listed
  apply revision_registers_its_pilot programme reorder OriginalOpening request
  cases person <;> simp [personalWord, reorder] at listed ⊢ <;> grind

private theorem paid_reordered (roster : List Bool) (word : W)
    (checked : periodPasses roster word OriginalOpening = true) :
    Supply.Period revised origin OriginalOpening roster word :=
  let paid := paidAt origin OriginalOpening roster word checked
  ⟨paid.own, paid.originalFloor, paid.currentFloor, paid.positiveClock⟩

private def revisedMove : Move revised origin [false, true] OriginalOpening where
  word := reorder.pilot
  registered := revision_registers_its_pilot programme reorder OriginalOpening
  paid := paid_reordered [false, true] reorder.pilot (by rw [opening_eq]; decide +kernel)
  personal := fun person _ => ⟨personalWord person, personal_registration person, paid_reordered [person] (personalWord person)
    (by rw [opening_eq]; cases person <;> decide +kernel)⟩

private def reorderedKit : RevisionKit programme origin [false, true] OriginalOpening 1 reorder where
  recipe := {
    move := revisedMove
    law := {
      timing := (originalRecipe origin).law.timing
      reserve := (originalRecipe origin).law.reserve
      accumulating := by
        change Balance.FiniteChecks .accumulating revised.law OriginalOpening reorder.pilot
        rw [opening_eq]
        decide +kernel
      positive := by norm_num
      duration := fun _ _ _ _ => le_rfl
      registered := fun _ _ _ _ word => word }
    registration := fun _ _ _ _ _ word => word
    positiveGain := ⟨true, true, by
      change 0 < Balance.gain revised.law OriginalOpening reorder.pilot true true
      rw [opening_eq]
      decide +kernel⟩ }
  starts := rfl
  produces := ⟨grow true, List.mem_cons_self, true, rfl⟩

private def signedRevision : Replies Bool Bool Bool Unit Unit :=
  { personalReplies true with revision := fun _ _ _ _ => true }

/-- The original actors approve the opposite production order. That
different submitted experiment is the installed first write. -/
theorem the_reordered_original_recipe_is_actually_installed :
    let round := dispatch signedRevision initial (.revise reorder)
    round.visit.read.disposition = .revised ∧
      round.visit.read.commands = reorder.pilot ∧ round.visit.read.commands ≠ initial.move.word ∧
      round.next.programme = revised ∧ round.next.ledger.stack.balances = Settlement.settled.stack.balances := by
  have approved : RevisionApproval signedRevision.revision initial.ledger.resident.erase
      initial.physical.raw [false, true] reorder := fun _ _ => rfl
  obtain ⟨kit, actual, selected⟩ := (inspectRevision_passes_iff
    programme origin [false, true] OriginalOpening 1 signedRevision.revision initial.ledger.resident.erase
    initial.physical.raw reorder).mpr ⟨approved, ⟨reorderedKit⟩⟩
  have written := an_accepted_revision_is_its_actual_trial signedRevision initial reorder kit actual selected
  have distinct : reorder.pilot ≠ initial.move.word := by
    rw [initial.recipe.moveAt_word initial.physical.raw initial.reserved]
    change reorder.pilot ≠ OriginalRecipe.offer.pilot
    intro impossible
    have first := congrArg (fun word => word.head?.map Request.signer) impossible
    change (some true : Option Bool) = some false at first
    cases first
  exact ⟨written.1, written.2.1, fun same => distinct (written.2.1.symm.trans same),
    written.2.2.1, written.2.2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OriginalReview
