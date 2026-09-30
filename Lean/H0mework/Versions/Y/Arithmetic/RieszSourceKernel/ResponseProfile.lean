import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Core
import H0mework.Versions.Y.Arithmetic.RieszEuler.EdgeFourier

/-! The response profile retains the original delta edge as a full tempered distribution. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Response

open Complex FourierTransform MeasureTheory
open scoped FourierTransform

noncomputable section

local notation "q" => (1 / 4 : ℝ)

def wholeU : BurnolL2 := burnolQuarterZeroExtension (u : BurnolQuarterIntervalL2)

def wholeV : BurnolL2 := burnolQuarterZeroExtension (v : BurnolQuarterIntervalL2)

theorem wholeU_reflection : reflectL2 wholeU = wholeU := by
  change reflectL2 (burnolRadiusZeroExtension q (u : BurnolQuarterIntervalL2)) =
    burnolRadiusZeroExtension q (u : BurnolQuarterIntervalL2)
  rw [burnolRadiusZeroExtension_reflect, u_reflection]

theorem wholeV_reflection : reflectL2 wholeV = wholeV := by
  change reflectL2 (burnolRadiusZeroExtension q (v : BurnolQuarterIntervalL2)) =
    burnolRadiusZeroExtension q (v : BurnolQuarterIntervalL2)
  rw [burnolRadiusZeroExtension_reflect, v_reflection]

def Psi : TemperedDistribution ℝ ℂ :=
  𝓕 (wholeU : TemperedDistribution ℝ ℂ) - (wholeV : TemperedDistribution ℝ ℂ) - GapEuler.edge q

theorem Psi_fourier :
    𝓕 Psi = (wholeU : TemperedDistribution ℝ ℂ) -
      𝓕 (wholeV : TemperedDistribution ℝ ℂ) - 𝓕 (GapEuler.edge q) := by
  have twice : 𝓕 (𝓕 (wholeU : TemperedDistribution ℝ ℂ)) = (wholeU : TemperedDistribution ℝ ℂ) := by
    rw [Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq]
    change (fourierL2 (fourierL2 wholeU) : TemperedDistribution ℝ ℂ) = _
    rw [fourierL2_fourierL2, wholeU_reflection]
  change (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
    (𝓕 (wholeU : TemperedDistribution ℝ ℂ) - (wholeV : TemperedDistribution ℝ ℂ) - GapEuler.edge q) = _
  rw [map_sub, map_sub]
  change 𝓕 (𝓕 (wholeU : TemperedDistribution ℝ ℂ)) -
    𝓕 (wholeV : TemperedDistribution ℝ ℂ) - 𝓕 (GapEuler.edge q) = _
  rw [twice]

theorem Psi_fourier_pairing (test : SchwartzMap ℝ ℂ) :
    (𝓕 Psi) test = (wholeU : TemperedDistribution ℝ ℂ) test -
      (𝓕 (wholeV : TemperedDistribution ℝ ℂ)) test -
        ∫ x : ℝ, test x * Edge.raw q x := by
  rw [Psi_fourier]
  simp only [sub_apply]
  rw [Edge.fourier_edge_pairing q (by norm_num) test]

end
end OriginalRieszSource.Response
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
