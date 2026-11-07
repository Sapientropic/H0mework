import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def familyState (shared : Current seed claim) : Responsibility.Family.State seed.claim :=
  by
    constructor
    case remaining => exact shared.productive
    case raw => exact shared.raw
    case nonnegative => exact shared.productive_nonnegative
    case outside => exact shared.productive_outside
    case declared => exact shared.productiveDeclared

def projectState : Productive.State seed claim → Responsibility.Family.State seed.claim
  | .legacy old => old
  | .current shared => familyState seed claim shared

theorem every_current_coordinate_is_the_actual_shared_coordinate (shared : Current seed claim) :
    (familyState seed claim shared).raw = shared.raw ∧
      (familyState seed claim shared).remaining = shared.productive ∧
      (familyState seed claim shared).declared = shared.productiveDeclared := ⟨rfl,rfl,rfl⟩

theorem the_actual_remaining_budget_is_literal (state : Productive.State seed claim) :
    Responsibility.Family.State.budget seed.claim (projectState seed claim state) =
      (Productive.law seed claim).budget state := by
  cases state <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
