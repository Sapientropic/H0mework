import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Stack

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Stack

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Transport

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {N J : WorldRelationNetwork} (finance : DebtActivationLaw)

def under : {J : WorldRelationNetwork} → Stack seed community N J →
    Stack seed community (ExtendedNetwork N finance) (ExtendedNetwork J finance)
  | _, .base _ => .base (ExtendedNetwork N finance)
  | _, .add prior origin balance view => .add (under prior) origin balance (view.under finance)

theorem under_support (stack : Stack seed community N J) (support : N.Support)
    (native : Option finance.DebtState) :
    (under finance stack).support (support, native) = (stack.support support, native) := by
  induction stack with
  | base => rfl
  | add prior origin balance view ih =>
    change ((view.under finance).support ((under finance prior).support (support, native)) (.live balance)) = _
    rw [ih]
    rfl

theorem under_balances (stack : Stack seed community N J) :
    (under finance stack).balances = stack.balances := by
  induction stack with
  | base => rfl
  | add prior origin balance view ih =>
    change (under finance prior).balances ++ [(origin, balance)] = prior.balances ++ [(origin, balance)]
    rw [ih]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Stack
