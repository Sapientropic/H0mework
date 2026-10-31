set_option autoImplicit false

universe u v

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

theorem option_with_equation_none {α β : Type} (value : Option α)
    (noneCase : value = none → β) (someCase : ∀ item, value = some item → β)
    (observed : value = none) :
    (Option.rec (motive := fun branch => value = branch → β) noneCase someCase value rfl) = noneCase observed := by
  subst value
  rfl

theorem option_with_equation_some {α β : Type} (value : Option α)
    (noneCase : value = none → β) (someCase : ∀ item, value = some item → β)
    (item : α) (observed : value = some item) :
    (Option.rec (motive := fun branch => value = branch → β) noneCase someCase value rfl) = someCase item observed := by
  subst value
  rfl

theorem rec_with_equation {α : Sort u} {β : Sort v} (value branch : α)
    (body : value = branch → β) (back : branch = value) (observed : value = branch) :
    (Eq.rec (motive := fun next _ => value = next → β) body back rfl) = body observed := by
  cases back
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
