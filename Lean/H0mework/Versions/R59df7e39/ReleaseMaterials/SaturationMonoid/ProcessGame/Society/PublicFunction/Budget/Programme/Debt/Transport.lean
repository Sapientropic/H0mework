import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Local

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Transport

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (first second : Cursor code) (origin : Origin first) (other : Origin second)
  (template : Template (code := code))

theorem each_original_share_uses_its_own_matched_terminal_slot
    (left : OldSlot first origin) (right : OldSlot second other)
    (index : left.val = right.val)
    (matched : Native.Coupling.Match code first.source.input second.source.input
      (Financial.accountAt first.source.input (arrival first))
      (Financial.accountAt second.source.input (arrival second))) :
    share first origin template left = share second other template right := by
  have leftAt := (followed first origin left).present
  have rightAt := (followed second other right).present
  have leftTime : origin.val+(arrival first-origin.val) = arrival first := by
    have bounded := origin.isLt
    omega
  have rightTime : other.val+(arrival second-other.val) = arrival second := by
    have bounded := other.isLt
    omega
  change (Financial.accountAt first.source.input (origin.val+(arrival first-origin.val))).current.slots[left.val]? = _ at leftAt
  change (Financial.accountAt second.source.input (other.val+(arrival second-other.val))).current.slots[right.val]? = _ at rightAt
  conv at leftAt => lhs;rw [leftTime,index]
  conv at rightAt => lhs;rw [rightTime]
  have row := congrArg (fun images => images[right.val]?) matched.slots
  simp only [Identity.financeImage,List.getElem?_map] at row
  rw [leftAt,rightAt] at row
  simp only [Option.map_some] at row
  have fields := Identity.correspondence_keeps_contract_shares_and_archive code first.source.input second.source.input
    (followed first origin left).slot (followed second other right).slot ⟨Option.some.inj row⟩
  have instrument := congrArg Identity.ClaimImage.instrument fields.1
  have debtor := congrArg Identity.ClaimImage.debtor fields.1
  have balance := congrArg (fun balances : Party →₀ ℚ => balances template.creditor) fields.2.1
  change (Financial.slotClaim second.source.input (followed second other right).slot).instrument =
    (Financial.slotClaim first.source.input (followed first origin left).slot).instrument at instrument
  change (Financial.slotClaim second.source.input (followed second other right).slot).debtor =
    (Financial.slotClaim first.source.input (followed first origin left).slot).debtor at debtor
  dsimp only [share]
  rw [instrument,debtor,balance]

theorem matched_original_and_terminal_accounts_preserve_the_original_remaining
    (atOrigin : Native.Coupling.Match code first.source.input second.source.input
      (account first origin) (account second other))
    (atArrival : Native.Coupling.Match code first.source.input second.source.input
      (Financial.accountAt first.source.input (arrival first))
      (Financial.accountAt second.source.input (arrival second))) :
    remaining first origin template = remaining second other template := by
  have lengths := congrArg List.length atOrigin.slots
  simp only [Identity.financeImage,List.length_map] at lengths
  unfold remaining
  apply congrArg List.sum
  apply List.ext_getElem
  · simp only [List.length_map,List.length_finRange]
    exact lengths.symm
  · intro index leftBound rightBound
    simp only [List.length_map,List.length_finRange] at leftBound rightBound
    simp only [List.getElem_map,List.getElem_finRange]
    exact each_original_share_uses_its_own_matched_terminal_slot first second origin other template
      ⟨index,leftBound⟩ ⟨index,rightBound⟩ rfl atArrival

theorem matched_original_and_terminal_accounts_generate_the_same_original_word
    (atOrigin : Native.Coupling.Match code first.source.input second.source.input
      (account first origin) (account second other))
    (atArrival : Native.Coupling.Match code first.source.input second.source.input
      (Financial.accountAt first.source.input (arrival first))
      (Financial.accountAt second.source.input (arrival second))) :
    word first origin template = word second other template :=
  equal_retained_original_share_summaries_generate_the_same_word first origin template second other
    (matched_original_and_terminal_accounts_preserve_the_original_remaining first second origin other template atOrigin atArrival)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Transport
