import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical

/-! The full original Pa source correction is read by its original orthogonal complement. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolPaResolvent_source_pairing (probe : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange)
    (left : BurnolPaOrthogonalCarrier) :
    inner ℂ (left : BurnolL2) (burnolDirectRightResolvent (probe.value / 2) (p : BurnolL2)) =
      burnolPaResolventSourceCoefficient probe p *
        inner ℂ (left : BurnolL2) (burnolUnitTailResponse probe 4) := by
  obtain ⟨c, hc, hread⟩ := Submodule.mem_map.mp (burnolPaResolvent_source_correction probe p inPa)
  have kill : inner ℂ (left : BurnolPaAmbientCarrier) c = 0 :=
    (Submodule.mem_orthogonal' _ _).mp left.property c hc
  rw [sub_eq_iff_eq_add.mp hread.symm, inner_add_right, inner_smul_right]
  change inner ℂ (left : BurnolPaAmbientCarrier) c + _ = _
  rw [kill, zero_add]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
