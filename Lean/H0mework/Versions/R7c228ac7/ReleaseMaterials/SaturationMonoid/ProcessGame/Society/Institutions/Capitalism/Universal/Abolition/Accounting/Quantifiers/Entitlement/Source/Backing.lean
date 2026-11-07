import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Window
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements.Funding

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Universal.Source.Program Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def NativeBacks (leg : window.Leg)
    (slot : ObligationSlot (Financial.vocabulary window.input)) : Prop :=
  (Financial.slotClaim window.input slot).debtor = leg.sender ∧
  window.input.law.settlementUnit (Financial.slotClaim window.input slot).instrument = leg.good ∧
  0 < Financial.slotBalance window.input slot leg.recipient

instance (leg : window.Leg) (slot : ObligationSlot (Financial.vocabulary window.input)) :
    Decidable (NativeBacks window leg slot) := by unfold NativeBacks; infer_instance

structure NativeBacking (leg : window.Leg) where
  private mk ::
  index : Fin window.nativeSlots.length
  backed : NativeBacks window leg (window.nativeSlots.get index)

namespace NativeBacking
variable {window} {leg : window.Leg} (basis : NativeBacking window leg)

def slot := window.nativeSlots.get basis.index
def claim := Financial.slotClaim window.input basis.slot
def principal := Financial.slotBalance window.input basis.slot leg.recipient
def materialQuote := basis.principal * window.input.law.settlementRate basis.claim.instrument

theorem principal_positive : 0 < basis.principal := basis.backed.2.2

end NativeBacking

def readNative (leg : window.Leg) : Option (NativeBacking window leg) :=
  (List.finRange window.nativeSlots.length).findSome? fun index =>
    if backed : NativeBacks window leg (window.nativeSlots.get index) then some ⟨index,backed⟩
    else none

/-- The source scans all actual slots. This absence says nothing about an
uninterpreted external authority or a different root action. -/
def NoNativeBacking (leg : window.Leg) : Prop :=
  ∀ index : Fin window.nativeSlots.length, ¬ NativeBacks window leg (window.nativeSlots.get index)

instance (leg : window.Leg) : Decidable (NoNativeBacking window leg) := by unfold NoNativeBacking; infer_instance

inductive Classification (leg : window.Leg) where
  | sourceSignature (signed : leg.item.val.request.signer = leg.sender)
  | sourceConsent (consent : leg.sender ∈ leg.item.val.request.consents)
  | nativeBasisDemand (backing : NativeBacking window leg)
  | outsideControl (uncontrolled : ¬ ControlledReturn leg)
  | sourceBasisDemand (controlled : ControlledReturn leg) (absent : NoNativeBacking window leg)

def classify (leg : window.Leg) : Classification window leg := by
  letI : Decidable (ControlledReturn (law := window.input.law) (before := window.before) (word := window.word) leg) :=
    instDecidableControlledReturn (law := window.input.law) (before := window.before) (word := window.word) leg
  exact if signed : leg.item.val.request.signer = leg.sender then .sourceSignature signed
  else if consent : leg.sender ∈ leg.item.val.request.consents then .sourceConsent consent
  else if controlled : ControlledReturn (law := window.input.law) (before := window.before) (word := window.word) leg then
    match Abolition.Material.inspectList
        (fun index => ¬ NativeBacks window leg (window.nativeSlots.get index)) (List.finRange window.nativeSlots.length) with
    | .failure index _ positive => .nativeBasisDemand ⟨index,of_not_not positive⟩
    | .clear absent => .sourceBasisDemand controlled (fun index => absent index (List.mem_finRange index))
  else .outsideControl controlled

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source
