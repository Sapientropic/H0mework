import H0mework.Versions.Y.Arithmetic.SonineProjection.MeanZero

/-! The original continuous endpoint Fourier profile restricts to the existing two columns. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Edge

open Complex MeasureTheory
open scoped ENNReal InnerProductSpace Topology
open Constructor

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

def raw (radius : ℝ) : ℝ → ℂ :=
  (radius : ℂ) • (phase radius + phase (-radius)) -
    burnolRadiusTruncatedFourierRaw radius (intervalConstant radius)

theorem raw_apply (radius frequency : ℝ) :
    raw radius frequency =
      (radius : ℂ) * (phase frequency radius + phase frequency (-radius)) -
        burnolRadiusTruncatedFourierRaw radius (intervalConstant radius) frequency := by
  simp only [raw, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [phase_symm radius frequency, phase_symm (-radius) frequency]

theorem raw_continuous (radius : ℝ) : Continuous (raw radius) :=
  (((phaseContinuous radius).add (phaseContinuous (-radius))).const_smul (radius : ℂ)).sub
    (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant radius))

theorem compact_truncatedFourier (state : BurnolQuarterIntervalL2) :
    compact (burnolRadiusTruncatedFourierRaw q state)
      (burnolRadiusTruncatedFourierRaw_continuous state) = burnolTruncatedFourier state := by
  apply Lp.ext
  exact (compact_read _ _).trans (truncatedFourier_read state).symm

theorem compact_raw :
    compact (raw q) (raw_continuous q) =
      (q : ℂ) • (compact (phase q) (phaseContinuous q) +
        compact (phase (-q)) (phaseContinuous (-q))) -
          burnolTruncatedFourier (intervalConstant q) := by
  unfold raw
  rw [compact_sub _ _
    (((phaseContinuous q).add (phaseContinuous (-q))).const_smul (q : ℂ))
    (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant q)),
    compact_smul _ _ ((phaseContinuous q).add (phaseContinuous (-q))),
    compact_add _ _ (phaseContinuous q) (phaseContinuous (-q)), compact_truncatedFourier]

theorem quarter_restriction_read :
    (compact (raw q) (raw_continuous q) : ℝ → ℂ) =ᵐ[μq] raw q :=
  compact_read _ _

/-- The full `T1` correction is the sum of the two original half-column corrections. -/
theorem zeroMean_raw_eq_endpointColumns :
    zeroMean (compact (raw q) (raw_continuous q)) = endpointColumn q + endpointColumn (-q) := by
  rw [compact_raw]
  unfold endpointColumn
  simp only [map_sub, map_smul, map_add]
  module

end
end OriginalRieszSource.Edge
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
