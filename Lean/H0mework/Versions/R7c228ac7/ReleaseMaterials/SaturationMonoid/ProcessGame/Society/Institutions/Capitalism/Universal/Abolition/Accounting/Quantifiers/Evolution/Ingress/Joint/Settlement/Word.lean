import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Settlement

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def request (slot : ObligationSlot (Abolition.Root.Epoch.Finance.vocabulary seed.input seed.depth seed.count))
    (holder : Party) : Request Party Good Port Technology Instrument :=
  let claim := Abolition.Root.Epoch.Finance.slotClaim seed.input seed.depth seed.count slot
  ⟨claim.debtor seed.input seed.depth seed.count,[],
    seed.current.actualLaw.issuerPort (claim.instrument seed.input seed.depth seed.count),[],
    .settle (claim.instrument seed.input seed.depth seed.count) (claim.debtor seed.input seed.depth seed.count) holder
      (Abolition.Root.Epoch.Finance.slotBalance seed.input seed.depth seed.count slot holder)⟩

/-- Enumerate actual current creditor shares, including holders outside an
earlier member list. This generates requests, never payment receipts. -/
def wordFrom (account : (Abolition.Root.Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState) :
    RawEvent Party Good Port Technology Instrument :=
  account.current.slots.flatMap fun slot =>
    (Abolition.Root.Epoch.Finance.slotBalance seed.input seed.depth seed.count slot).support.toList.filterMap fun holder =>
      if 0 < Abolition.Root.Epoch.Finance.slotBalance seed.input seed.depth seed.count slot holder then
        some (request seed slot holder)
      else none

def word := wordFrom seed (Background.nativeAccount seed)

theorem every_positive_current_share_is_requested
    (account : (Abolition.Root.Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState)
    (slot : ObligationSlot (Abolition.Root.Epoch.Finance.vocabulary seed.input seed.depth seed.count))
    (listed : slot ∈ account.current.slots) (holder : Party)
    (positive : 0 < Abolition.Root.Epoch.Finance.slotBalance seed.input seed.depth seed.count slot holder) :
    request seed slot holder ∈ wordFrom seed account := by
  apply List.mem_flatMap.mpr
  refine ⟨slot,listed,List.mem_filterMap.mpr ⟨holder,?_,?_⟩⟩
  · exact Finset.mem_toList.mpr (Finsupp.mem_support_iff.mpr (ne_of_gt positive))
  · exact if_pos positive

theorem every_positive_original_current_share_is_requested
    (slot : ObligationSlot (Abolition.Root.Epoch.Finance.vocabulary seed.input seed.depth seed.count))
    (listed : slot ∈ (Background.nativeAccount seed).current.slots) (holder : Party)
    (positive : 0 < Abolition.Root.Epoch.Finance.slotBalance seed.input seed.depth seed.count slot holder) :
    request seed slot holder ∈ word seed :=
  every_positive_current_share_is_requested seed (Background.nativeAccount seed) slot listed holder positive

theorem a_terminal_archive_cannot_generate_another_payment
    (archive : TerminalArchive (Abolition.Root.Epoch.Finance.vocabulary seed.input seed.depth seed.count)) :
    (Abolition.Root.Epoch.Finance.slotBalance seed.input seed.depth seed.count (.terminal archive)).support = ∅ := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Settlement
