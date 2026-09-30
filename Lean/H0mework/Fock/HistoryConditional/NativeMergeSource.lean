import H0mework.Fock.HistoryConditional.NativeMergeInventory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

def count (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat)
    (previous : SourceConditionalNativeObservers.State Fine bound) (value : Coarse) : Nat :=
  inventoryCount (SourceUniformFibreVariance.outputs bound (fun index => read index.val)) forget bound previous value

def merge (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat)
    (previous : SourceConditionalNativeObservers.State Fine bound) : SourceConditionalNativeObservers.State Coarse bound :=
  inventoryMerge (SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) forget bound previous

end SourceConditionalNativeMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
