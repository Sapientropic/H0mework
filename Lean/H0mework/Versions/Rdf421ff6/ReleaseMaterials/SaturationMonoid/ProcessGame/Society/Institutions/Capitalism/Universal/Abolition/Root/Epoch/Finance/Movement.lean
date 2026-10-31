import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Instruction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

structure Movement (origin : ActualItem input depth count) where
  private mk ::
  kind : Financial.MovementKind
  instrument : Instrument
  debtor : Party
  sender : Party
  receiver : Party
  quantity : ℚ
  operation : (origin.instruction input depth count).request.operation =
    match kind with
    | .payment => .settle instrument debtor sender quantity
    | .assignment => .assign instrument debtor sender receiver quantity
  accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
    (origin.instruction input depth count).request

def readMovement (origin : ActualItem input depth count) : Option (Movement input depth count origin) :=
  if accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
      (origin.instruction input depth count).request then
    match operation : (origin.instruction input depth count).request.operation with
    | .settle instrument debtor holder quantity =>
        some ⟨.payment, instrument, debtor, holder, holder, quantity, operation, accepted⟩
    | .assign instrument debtor sender receiver quantity =>
        some ⟨.assignment, instrument, debtor, sender, receiver, quantity, operation, accepted⟩
    | _ => none
  else none

theorem Movement.quantity_nonnegative {origin : ActualItem input depth count}
    (movement : Movement input depth count origin) : 0 ≤ movement.quantity := by
  have guard := movement.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guard
  rw [movement.operation] at guard
  cases kind : movement.kind <;> simp only [kind] at guard <;> exact guard.1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance
