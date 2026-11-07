import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution.Prefix
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Native.Seed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution

open Source.Program Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {window : Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} (claim : Source.Claim window)

def law := PublicFunction.physicalLaw window.input.law

def before := Financial.Installation.Runtime.physical window.input window.frame

def members := (Financial.Installation.observe window.input window.cursor).members.dedup

def refunds : RawEvent Party Good Port Technology Instrument :=
  (Source.demands window).map fun demand =>
    ⟨demand.leg.sender,[],demand.leg.item.val.request.purpose,[],
      .transfer demand.leg.recipient demand.leg.sender [(demand.leg.good,demand.quantity)]⟩

/-- Every original slot is visited once, and its current creditor shares are
read once. Ordinary transfers are never substituted for these settlements. -/
def repayments : RawEvent Party Good Port Technology Instrument :=
  window.nativeSlots.flatMap fun slot => (members (window := window)).filterMap fun creditor =>
    let nativeClaim := Financial.slotClaim window.input slot
    let amount := Financial.slotBalance window.input slot creditor
    if 0 < amount then
      some ⟨nativeClaim.debtor,[],window.input.law.issuerPort nativeClaim.instrument,[],
        .settle nativeClaim.instrument nativeClaim.debtor creditor amount⟩
    else none

def needs : RawEvent Party Good Port Technology Instrument :=
  let purpose := ((Source.demands window).head claim.nonempty).leg.item.val.request.purpose
  (members (window := window)).flatMap fun actor =>
    [⟨actor,[],purpose,[],.use actor (window.input.law.necessities (before (window := window)) actor) .necessity⟩,
     ⟨actor,[],purpose,[],.use actor (window.input.law.mandatoryMaintenance (before (window := window)) actor) .maintenance⟩]

def proposed := refunds (window := window) ++ repayments (window := window) ++ needs claim

def candidate := (proposed claim).map (fun request => request.resign request.signer)

def selected := payable (law (window := window)) (before (window := window)) (candidate claim)

def unexecuted := (candidate claim).drop (selected claim).length

theorem selected_is_valid_in_the_original_live_stock :
    ∀ item ∈ (law (window := window)).rawItems (before (window := window)) (selected claim),
      (law (window := window)).Valid item.before item.request :=
  validity_reaches_every_original_inventory_item _ _ _ (the_source_prefix_is_valid _ _ _) 0

def raw : Abolition.Root.Registered.Compile.RawInput Party Good Port Technology Instrument := .execute (selected claim)

def cursor := Abolition.Root.Registered.Physical.receive Abolition.Root.Registered.Physical.initial (raw claim)

def actualItems := Abolition.Root.Registered.Macro.Public.Accounting.items window.input window.depth window.count
  0 0 [] (cursor claim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution
