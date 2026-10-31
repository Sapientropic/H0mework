import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Settlement.Word
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open Source.Program Innovation

private theorem sum_flatMap {α : Type} (members : List α) (values : α → List ℚ) :
    (members.flatMap values).sum = (members.map (fun member => (values member).sum)).sum := by
  induction members <;> simp_all

def requestValue (request : Request Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor holder : Party) : ℚ :=
  match request.operation with
  | .settle source borrower creditor quantity =>
      if source = instrument ∧ borrower = debtor ∧ creditor = holder then quantity else 0
  | _ => 0

def wordValue (word : RawEvent Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor holder : Party) : ℚ :=
  (word.map (fun request => requestValue request instrument debtor holder)).sum

private theorem sum_indicator (members : List Party) (unique : members.Nodup)
    (balance : Party → ℚ) (holder : Party) :
    (members.map (fun actor => if actor = holder then balance actor else 0)).sum =
      if holder ∈ members then balance holder else 0 := by
  induction members with
  | nil => simp
  | cons actor rest ih =>
      obtain ⟨absent,distinct⟩ := List.nodup_cons.mp unique
      simp only [List.map_cons,List.sum_cons,List.mem_cons]
      rw [ih distinct]
      by_cases same : actor = holder
      · subst actor
        simp [absent]
      · simp [same,Ne.symm same]

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
private theorem shares_sum_indicator (balance : Financial.Balance input) (holder : Party) :
    (balance.support.toList.map (fun actor => if actor = holder then balance actor else 0)).sum = balance holder := by
  rw [sum_indicator _ balance.support.nodup_toList]
  by_cases present : holder ∈ balance.support
  · rw [if_pos (Finset.mem_toList.mpr present)]
  · rw [if_neg (fun listed => present (Finset.mem_toList.mp listed))]
    exact (by simpa only [Finsupp.mem_support_iff,not_not] using present : balance holder = 0).symm

def nativeRequest (law : RawLaw Party Good Port Technology Instrument)
    (slot : ObligationSlot (vocabulary input depth count)) (holder : Party) : Request Party Good Port Technology Instrument :=
  let claim := slotClaim input depth count slot
  ⟨claim.debtor input depth count,[],law.issuerPort (claim.instrument input depth count),[],
    .settle (claim.instrument input depth count) (claim.debtor input depth count) holder
      (slotBalance input depth count slot holder)⟩

def nativeWord (law : RawLaw Party Good Port Technology Instrument)
    (account : (process input depth count).GeneratedState) : RawEvent Party Good Port Technology Instrument :=
  account.current.slots.flatMap fun slot => (slotBalance input depth count slot).support.toList.filterMap fun holder =>
    if 0 < slotBalance input depth count slot holder then some (nativeRequest input depth count law slot holder) else none

variable (law : RawLaw Party Good Port Technology Instrument)

theorem every_generated_settlement_request_has_its_original_nonnegative_share
    (account : (process input depth count).GeneratedState)
    (request : Request Party Good Port Technology Instrument) (listed : request ∈ nativeWord input depth count law account) :
    ∃ instrument debtor holder quantity, request.operation = .settle instrument debtor holder quantity ∧ 0 ≤ quantity := by
  obtain ⟨slot,_,member⟩ := List.mem_flatMap.mp listed
  obtain ⟨holder,_,selected⟩ := List.mem_filterMap.mp member
  split at selected
  · rename_i positive
    cases Option.some.inj selected
    exact ⟨_,_,_,_,rfl,le_of_lt positive⟩
  · cases selected

theorem the_native_settlement_word_contains_exactly_the_whole_current_ledger
    (account : (process input depth count).GeneratedState)
    (instrument : Instrument) (debtor creditor : Party) :
    wordValue (nativeWord input depth count law account) instrument debtor creditor =
      ledgerClaims input depth count account.current instrument debtor creditor := by
  unfold wordValue nativeWord ledgerClaims
  rw [List.map_flatMap,sum_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro slot member
  let balance := slotBalance input depth count slot
  have allPositive : ∀ holder ∈ balance.support.toList, 0 < balance holder := by
    intro holder listed
    have nonzero := Finsupp.mem_support_iff.mp (Finset.mem_toList.mp listed)
    exact lt_of_le_of_ne ((generated_sound input depth count account slot member).2 holder) nonzero.symm
  have full : balance.support.toList.filterMap (fun holder =>
      if 0 < balance holder then some (nativeRequest input depth count law slot holder) else none) =
        balance.support.toList.map (nativeRequest input depth count law slot) := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro holder listed
    exact if_pos (allPositive holder listed)
  change ((balance.support.toList.filterMap _).map _).sum = _
  rw [full,List.map_map]
  simp only [Function.comp_def]
  unfold slotClaims
  by_cases matching : (slotClaim input depth count slot).instrument input depth count = instrument ∧
      (slotClaim input depth count slot).debtor input depth count = debtor
  · rw [if_pos matching]
    have terms : (fun holder => requestValue (nativeRequest input depth count law slot holder) instrument debtor creditor) =
        (fun holder => if holder = creditor then balance holder else 0) := by
      funext holder
      simp only [requestValue,nativeRequest,matching.1,matching.2,true_and]
      rfl
    rw [terms]
    exact shares_sum_indicator input balance creditor
  · rw [if_neg matching]
    have terms : (fun holder => requestValue (nativeRequest input depth count law slot holder) instrument debtor creditor) = fun _ => (0 : ℚ) := by
      funext holder
      simp only [requestValue,nativeRequest]
      exact if_neg (fun same => matching ⟨same.1,same.2.1⟩)
    rw [terms]
    simp

variable {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

theorem the_generic_source_word_is_the_literal_original_wordFrom
    (account : (process seed.input seed.depth seed.count).GeneratedState) :
    nativeWord seed.input seed.depth seed.count seed.current.actualLaw account = Settlement.wordFrom seed account := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
