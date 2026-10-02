import H0mework.Realization.Operations.SuccessorBoundary

/-! The existing whole successor certificate is advanced by the original source action before any field read. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceSuccessorBoundary

noncomputable section
universe u
variable (R : Type u) [CommRing R]

theorem certificate_push_map : (certificate R).comp (push R) = certificate R + LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro index
  apply LinearMap.ext_ring
  simp [push, certificate_single, Finset.sum_range_succ]

theorem certificate_push (source : Nat →₀ R) :
    certificate R (push R source) = certificate R source + source :=
  LinearMap.congr_fun (certificate_push_map R) source

theorem certificate_boundary (source : Nat →₀ R) : certificate R (boundary R source) = source := by
  change certificate R (push R source - source) = source
  rw [map_sub, certificate_push, add_sub_cancel_left]

end
end SourceSuccessorBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
