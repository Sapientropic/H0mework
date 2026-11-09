import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Stack
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Write

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Stack

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Transport

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {N : WorldRelationNetwork}

def original (atBase : N.Support) (entry : OpenResponsibilityAt N atBase) :
    {J : WorldRelationNetwork} → (stack : Stack seed community N J) →
      OpenResponsibilityAt J (stack.support atBase)
  | _, .base _ => entry
  | _, .add prior _ balance view => view.original (r := .live balance) (original atBase entry prior)

/-- Only source-backed balance changes are allowed in an existing layer. -/
inductive Move : {J : WorldRelationNetwork} → Stack seed community N J → Stack seed community N J → Type _
  | base : Move (.base N) (.base N)
  | add {M J : WorldRelationNetwork} {before after : Stack seed community N M}
      (move : Move before after) (origin : Occurrence seed community) {left right : Balance}
      (view : Shape (law origin) M J)
      (motion : Motion (law origin) (.live left) (.live right)) :
      Move (.add before origin left view) (.add after origin right view)

namespace Move

def wait : {J : WorldRelationNetwork} → (stack : Stack seed community N J) → Move stack stack
  | _, .base _ => .base
  | _, .add prior origin balance view =>
    .add (wait prior) origin view (.inr (Carry.wait (.live balance)))

def lift {s t : N.Support} (whole : Whole N s t) (owner : OpenResponsibilityAt N s) :
    {J : WorldRelationNetwork} → {before after : Stack seed community N J} →
      Move before after → Whole J (before.support s) (after.support t)
  | _, _, _, .base => whole
  | _, _, _, .add (before := before) move _ view motion =>
    let old := lift whole owner move
    let focus := before.original s owner
    ⟨view.lift motion old.val focus, view.lift_keeps_keys motion old.val focus old.property⟩

theorem keeps_origins {J : WorldRelationNetwork} {before after : Stack seed community N J}
    (move : Move before after) :
    after.balances.map Prod.fst = before.balances.map Prod.fst := by
  induction move with
  | base => rfl
  | add _ origin view motion ih =>
    simp only [balances, List.map_append, List.map_cons, List.map_nil, ih]

end Move

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Stack
