import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Period
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Rule

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Conflict.Consumers.Evolving (W life)

noncomputable section

private abbrev registered := TerminalPeace.Supply.revisedInput
private abbrev opening := Settlement.settledCut.raw
private abbrev spending := Material.livingWord
private abbrev grow := TerminalPeace.Supply.grow

private theorem opening_eq : opening = Original.snapshot 117 107 :=
  Settlement.settled_raw

def refillWord : W :=
  [grow false, grow false, life false, grow true, grow true, life true]

private def passes (origin raw : Original.Raw) (word : W) : Bool :=
  match inspect registered origin raw [false, true] word with
  | .inl _ => false
  | .inr _ => true

private theorem passes_period (origin raw : Original.Raw) (word : W) (passed : passes origin raw word = true) :
    Period registered origin raw [false, true] word := by
  unfold passes at passed
  cases found : inspect registered origin raw [false, true] word with
  | inl issue =>
    rw [found] at passed
    cases passed
  | inr paid => exact paid.down

theorem the_original_reserve_can_be_spent_and_replenished_in_two_paid_periods :
    let depleted := registered.law.next opening spending
    let renewed := registered.law.next depleted refillWord
    Period registered opening opening [false, true] spending ∧
      Period registered opening depleted [false, true] refillWord ∧
      (∀ person, depleted.stock person true < opening.stock person true) ∧
      renewed = opening.retime (opening.clock + 2) (opening.round + 2) := by
  dsimp only
  refine ⟨passes_period _ _ _ (by rw [opening_eq]; decide +kernel),
    passes_period _ _ _ (by rw [opening_eq]; decide +kernel), ?_, ?_⟩
  · intro person
    rw [opening_eq]
    cases person <;> decide +kernel
  · rw [opening_eq]
    apply RawCurrent.ext
    · funext person good
      cases person <;> cases good <;> decide +kernel
    · funext instrument debtor creditor
      cases instrument
      cases debtor <;> cases creditor <;> decide +kernel
    · exact Subsingleton.elim _ _
    · decide +kernel
    · decide +kernel

theorem the_refill_is_accepted_after_the_same_native_spending_write :
    let first := Physical.Public.compile registered Settlement.settledCut.state (.execute spending)
    let second := Physical.Public.compile registered first.next (.execute refillWord)
    first.isAccepted = true ∧ second.isAccepted = true ∧
      second.next.raw = opening.retime (opening.clock + 2) (opening.round + 2) := by
  let first := Physical.Public.compile registered Settlement.settledCut.state (.execute spending)
  have paid := the_original_reserve_can_be_spent_and_replenished_in_two_paid_periods
  have firstWrite := paid.1.native_write Settlement.settledCut.state
  have same : first.next.raw = registered.law.next opening spending :=
    congrArg (fun current => current.raw) firstWrite.2.2
  have refill : Period registered opening first.next.raw [false, true] refillWord := by
    rw [same]
    exact paid.2.1
  have secondWrite := refill.native_write first.next
  refine ⟨firstWrite.1, secondWrite.1, ?_⟩
  have next := congrArg (fun current => current.raw) secondWrite.2.2
  change (Physical.Public.compile registered first.next (.execute refillWord)).next.raw =
    registered.law.next first.next.raw refillWord at next
  rw [same] at next
  exact next.trans paid.2.2.2

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Consumers
