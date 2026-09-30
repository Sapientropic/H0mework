import H0mework.Fock.HistoryConditional.NativePosteriorWeight

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

abbrev inventoryCount (keys : Finset Fine) (forget : Fine → Coarse) (bound : Nat)
    (previous : SourceConditionalNativeObservers.State Fine bound) (value : Coarse) : Nat :=
  ∑ key ∈ keys, if forget key = value then (previous key).1 else 0

abbrev inventoryMerge (keys : Finset Fine) (forget : Fine → Coarse) (bound : Nat)
    (previous : SourceConditionalNativeObservers.State Fine bound) : SourceConditionalNativeObservers.State Coarse bound := fun value =>
  let total := inventoryCount keys forget bound previous value
  (total, fun index => ∑ key ∈ keys,
    if forget key = value then ((previous key).1 : ℚ) / total * (previous key).2 index else 0)

end SourceConditionalNativeMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
