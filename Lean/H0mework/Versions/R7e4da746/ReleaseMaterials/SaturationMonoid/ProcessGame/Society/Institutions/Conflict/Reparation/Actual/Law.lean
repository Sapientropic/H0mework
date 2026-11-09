import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.CoSigned
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Entries

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtAdmissionFirstWrite

noncomputable section

structure Balance where
  remaining : ℚ
  nonnegative : 0 ≤ remaining

def Balance.subtract (before : Balance) (amount : ℚ) (within : amount ≤ before.remaining) : Balance :=
  ⟨before.remaining - amount, sub_nonneg.mpr within⟩

inductive Phase
  | unfiled
  | live (balance : Balance)

def budget : Phase → Nat
  | .unfiled => 2
  | .live balance => if balance.remaining = 0 then 0 else 1

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (origin : Occurrence seed community)

def opening : Balance := ⟨origin.quantity, origin.positive.le⟩

inductive Step : Phase → Phase → Type
  | file : Step .unfiled (.live (opening origin))
  | final (before : Balance) (share : Share origin) (within : share.amount ≤ before.remaining)
      (full : share.amount = before.remaining) :
      Step (.live before) (.live (before.subtract share.amount within))
  | jointFinal (before : Balance) (share : JointShare origin) (within : share.amount ≤ before.remaining)
      (full : share.amount = before.remaining) :
      Step (.live before) (.live (before.subtract share.amount within))

inductive Carry : Phase → Phase → Type
  | wait (phase : Phase) : Carry phase phase
  | partPaid (before : Balance) (share : Share origin) (within : share.amount ≤ before.remaining)
      (stillDue : share.amount < before.remaining) :
      Carry (.live before) (.live (before.subtract share.amount within))
  | jointPartPaid (before : Balance) (share : JointShare origin) (within : share.amount ≤ before.remaining)
      (stillDue : share.amount < before.remaining) :
      Carry (.live before) (.live (before.subtract share.amount within))

def Paid : Phase → Type
  | .unfiled => PEmpty
  | .live balance => PLift (balance.remaining = 0)

def Obstruction : Phase → Type
  | .unfiled => Unit
  | .live balance => PLift (0 < balance.remaining)

def law : DebtActivationLaw where
  DebtState := Phase
  DebtId := Nat × Nat × Key Party Good
  DebtClaim := Occurrence seed community
  debtId := origin.address
  debtClaim := origin
  budget := budget
  StepAt := Step origin
  step_budget_lt := by
    intro _ _ step
    cases step with
    | file => simp [budget, opening, ne_of_gt origin.positive]
    | final before share _ full | jointFinal before share _ full =>
      have nonzero : before.remaining ≠ 0 := ne_of_gt (full ▸ share.positive)
      simp [budget, Balance.subtract, full, nonzero]
  transportLaw? := some {
    EventAt := Carry origin
    budget_le := by
      intro _ _ step
      cases step with
      | wait => exact le_rfl
      | partPaid before share _ remains | jointPartPaid before share _ remains =>
        have nonzero : before.remaining ≠ 0 := ne_of_gt (share.positive.trans remains)
        simp [budget, Balance.subtract, nonzero, ne_of_gt (sub_pos.mpr remains)] }
  SettlementAt := Paid
  settlement_budget_zero := by
    intro phase paid
    cases phase with
    | unfiled => exact nomatch paid
    | live balance => simp [budget, paid.down]
  ObstructionAt := Obstruction

def file : SourceFixedDebtAdmissionEventAt (law origin) .unfiled :=
  .ofStep (Step.file (origin := origin))

def credit (balance : Balance) (share : Share origin) (within : share.amount ≤ balance.remaining) :
    Transport.Motion (law origin) (.live balance) (.live (balance.subtract share.amount within)) :=
  if full : share.amount = balance.remaining then .inl (.final balance share within full)
  else .inr (.partPaid balance share within (lt_of_le_of_ne within full))

/-- The original obligation makes the same bounded transition when the
debtor's delivered transfer and victim's acknowledgement are paired. -/
def jointCredit (balance : Balance) (share : JointShare origin) (within : share.amount ≤ balance.remaining) :
    Transport.Motion (law origin) (.live balance) (.live (balance.subtract share.amount within)) :=
  if full : share.amount = balance.remaining then .inl (.jointFinal balance share within full)
  else .inr (.jointPartPaid balance share within (lt_of_le_of_ne within full))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
