import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.GeneratorStrong

/-! The original strong resolvent and Fourier anti-action generate the mixed resolvent identity without division. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolDirectRightResolvent_fourier_mixed (z w : ℂ)
    (zr : 1 / 4 < z.re) (wr : 1 / 4 < w.re) (value : BurnolL2) :
    (z + w - 1 / 2) • burnolDirectRightResolvent z
      (fourierL2 (burnolDirectRightResolvent w value)) =
    -(burnolDirectRightResolvent z (fourierL2 value) +
      fourierL2 (burnolDirectRightResolvent w value)) := by
  let q := fourierL2 (burnolDirectRightResolvent w value)
  let r := burnolDirectRightResolvent z (fourierL2 value)
  have forward := burnolDirectRightResolventOrbit_hasDerivAt z zr (fourierL2 value)
  have reverse := burnolFourierOrbit_hasDerivAt _ _
    (burnolDirectRightResolventOrbit_hasDerivAt w wr value)
  have combined := forward.add reverse
  have same : r + q = burnolDirectRightResolvent z (-(z + w - 1 / 2) • q) := by
    apply burnolDirectRightResolvent_of_strongEquation z zr
    convert! combined using 1
    · funext h
      rw [map_add]
      rfl
    · simp only [map_add, map_smul]
      dsimp only [q, r]
      module
  rw [burnolDirectRightResolvent_smul] at same
  change (z + w - 1 / 2) • burnolDirectRightResolvent z q = -(r + q)
  rw [same]
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
