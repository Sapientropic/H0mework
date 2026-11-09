import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalNetwork

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Material (inspectList)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Conflict.Consumers.Evolving (life)
open FixedPoint.OpenPeace.Operational (RepeatCode RecipeIssue checkRecipe)
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open RevisedOrders (openPayment)

noncomputable section

private abbrev Programme := Capitalism.Universal.Root.ProgrammeSource.Input Bool Bool Bool Unit Unit

private def tripleMeal (input : Programme) (same : input = revised) (raw : Original.Raw) :
    RepeatCode input raw :=
  { codeFor input same raw with production := [life true, life true, life true] }

private theorem actual_roster : people loss front = [false, true] ∨ people loss front = [true, false] := by
  have unique : (people loss front).Nodup := List.nodup_dedup _
  have first := both_original_parties_have_standing false
  have second := both_original_parties_have_standing true
  generalize people loss front = roster at unique first second ⊢
  rcases roster with _ | ⟨p, next⟩
  · cases first
  rcases next with _ | ⟨q, rest⟩
  · cases p <;> simp_all
  cases p <;> cases q <;> simp [List.nodup_cons] at unique
  all_goals
    have exhausted : rest = [] := by
      cases rest with
      | nil => rfl
      | cons person tail =>
        cases person <;> simp_all
    simp [exhausted]

/-- Read the literal first blocked position and its stock and debit from
the existing recipe diagnostic. -/
private def shortageAt {input : Programme} {origin raw : Original.Raw} {roster : List Bool}
    {code : RepeatCode input raw} (issue : RecipeIssue input origin raw roster code) :
    Option (Nat × Bool × Bool × ℚ × ℚ) :=
  match issue with
  | .production (.unpaid (.instruction stop)) =>
    match stop.issue with
    | .materialShortage lot _ _ =>
      let item := (input.law.rawItems raw code.production)[stop.position]
      some (stop.position.val, lot.1.1, lot.1.2, item.before.stock lot.1.1 lot.1.2,
        flowAt (input.law.debit item.before item.request) lot.1.1 lot.1.2)
    | _ => none
  | _ => none

private def readShortage (input : Programme) (same : input = revised) (raw : Original.Raw) (roster : List Bool) :=
  match checkRecipe input (originalRaw loss) raw roster (tripleMeal input same raw) with
  | .inl issue => shortageAt issue
  | .inr _ => none

private theorem literal_shortage (input : Programme) (same : input = revised)
    (raw : Original.Raw) (stock : raw = afterClear) :
    readShortage input same raw (people loss front) = some (2, true, true, 0, 1) := by
  subst input raw
  obtain roster | roster := actual_roster
  · rw [roster]
    decide +kernel
  · rw [roster]
    decide +kernel

private abbrev settled := actualNetwork.paid.next
private abbrev law := actualNetwork.paid.sameProgramme.trans actualTrial.revisedProgramme
private abbrev requested := tripleMeal settled.programme law settled.physical.raw

theorem the_original_dispatch_names_the_first_real_shortage :
    ∃ denied, openNetwork settled quote FixedPoint.OpenPeace.Network.Runtime.OriginalOrders.payment openPayment
        requested = .inl denied ∧
      (∃ issue, denied.visit.read = .recipe issue ∧ shortageAt issue = some (2, true, true, 0, 1)) ∧
      denied.next.ledger.stack.balances = settled.ledger.stack.balances ∧
      denied.next.physical = settled.physical ∧
      (⟨settled.ledger.world,
        (Installation.Core.action settled.ledger denied.visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = denied.next.ledger.resident.erase := by
  have short := literal_shortage settled.programme law settled.physical.raw
    (payment_lands_at_the_actual_stock actualNetwork.paid)
  unfold readShortage at short
  cases tested : checkRecipe settled.programme (originalRaw loss) settled.physical.raw (people loss front) requested with
  | inr accepted =>
    rw [tested] at short
    cases short
  | inl issue =>
    rw [tested] at short
    let refusal := refuse settled (RenewalIssue.recipe issue)
    have chosen : openNetwork settled quote FixedPoint.OpenPeace.Network.Runtime.OriginalOrders.payment openPayment
        requested = .inl refusal := by
      unfold openNetwork inspectRenewal
      cases inspectList (fun row => row.2.remaining = 0) settled.ledger.stack.balances with
      | failure row original due =>
        exact (due (actualNetwork.network.paid row (actualNetwork.network.rows.symm ▸ original))).elim
      | clear _ => simp only [tested, refusal]
    exact ⟨refusal, chosen, ⟨issue, rfl, short⟩, refusal.keepsRows, refusal.keepsPhysical, refusal.canonical⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
