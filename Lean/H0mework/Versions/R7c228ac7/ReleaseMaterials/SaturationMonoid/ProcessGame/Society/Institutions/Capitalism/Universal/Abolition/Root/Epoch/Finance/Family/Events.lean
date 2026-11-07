import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle ComplementObservation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

/-- Old events remain literal objects in their source fibre. A later law
cannot reinterpret the admitted obligation or its historical archive. -/
inductive Event : Type
  | original (index : Index) (event : Finance.Event (sources index) (depths index) (counts index))
  | review (claim : Claim sources depths counts) (receipt : Review sources depths counts claim)
      (before : Balance (Party := Party)) (cap : ℚ)

def Event.claim : Event sources depths counts → Claim sources depths counts
  | .original index event => ⟨index, event.claim (sources index) (depths index) (counts index)⟩
  | .review claim _ _ _ => claim

def Event.before : Event sources depths counts → Balance (Party := Party)
  | .original index event => event.before (sources index) (depths index) (counts index)
  | .review _ _ before _ => before

def Event.after : Event sources depths counts → Balance (Party := Party)
  | .original index event => event.after (sources index) (depths index) (counts index)
  | .review _ receipt before cap => receipt.after sources depths counts before cap

def Event.Lawful : Event sources depths counts → Prop
  | .original index event => event.Lawful (sources index) (depths index) (counts index)
  | .review _ receipt before cap => (∀ holder, 0 ≤ before holder) ∧ 0 ≤ cap ∧ cap ≤ receipt.movement.quantity

def Event.CommitmentAt : Event sources depths counts → Claim sources depths counts → Type
  | .original index event, claim =>
      (original : Finance.Claim (sources index) (depths index) (counts index)) ×
        (Finance.Event.CommitmentAt (sources index) (depths index) (counts index) event original ×
          PLift ((⟨index, original⟩ : Claim sources depths counts) = claim))
  | .review .., _ => PEmpty

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
