import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedPositionDomain
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ResponseCountingReadback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.JointWardReadback

open Complex Filter MeasureTheory
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section

/-- The complete complex Ward identity reads the actual finite Eu response on both source sides. -/
theorem original_forward_limit (left right : BurnolCompletedMellinCoordinate)
    (leftZero : riemannZeta left.value = 0) (rightZero : riemannZeta right.value = 0) :
    let jl := JointCounting.value left leftZero
    let jr := JointCounting.value right rightZero
    let tl := Kernel.A left • CountingDual.value left - Kernel.beta left • PositionCounting.value left leftZero
    let tr := Kernel.A right • CountingDual.value right - Kernel.beta right • PositionCounting.value right rightZero
    let eu := burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2)
    Tendsto (fun N : ℕ =>
      star (star left.value - 1 / 2) * inner ℂ tl jr +
      (star right.value - 1 / 2) * inner ℂ jl tr +
      star (Kernel.A left ^ 2 - Kernel.beta left ^ 2) * star (inner ℂ (FiniteForcing.source N jr) eu) +
      (Kernel.A right ^ 2 - Kernel.beta right ^ 2) * inner ℂ (FiniteForcing.source N jl) eu)
      atTop (𝓝 0) := by
  dsimp only
  have l := ResponseCounting.joint_forward_pairing_tendsto left leftZero false
  have r := ResponseCounting.joint_forward_pairing_tendsto right rightZero false
  have constant : Tendsto (fun _ : ℕ =>
      star (star left.value - 1 / 2) * inner ℂ
        (Kernel.A left • CountingDual.value left - Kernel.beta left • PositionCounting.value left leftZero)
        (JointCounting.value right rightZero) +
      (star right.value - 1 / 2) * inner ℂ (JointCounting.value left leftZero)
        (Kernel.A right • CountingDual.value right - Kernel.beta right • PositionCounting.value right rightZero))
      atTop (𝓝 _) := tendsto_const_nhds
  have actual := (constant.add (r.star.const_mul (star (Kernel.A left ^ 2 - Kernel.beta left ^ 2)))).add
    (l.const_mul (Kernel.A right ^ 2 - Kernel.beta right ^ 2))
  have ward := CountedEulerDomain.joint_cross_balance left right leftZero rightZero
  simp only [CountedEulerDomain.jointVelocity, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply] at ward
  have symmetric : star (inner ℂ (JointCounting.value right rightZero) (ResponseCounting.value false)) =
      inner ℂ (ResponseCounting.value false) (JointCounting.value right rightZero) := inner_conj_symm _ _
  have value :
      star (star left.value - 1 / 2) * inner ℂ
        (Kernel.A left • CountingDual.value left - Kernel.beta left • PositionCounting.value left leftZero)
        (JointCounting.value right rightZero) +
      (star right.value - 1 / 2) * inner ℂ (JointCounting.value left leftZero)
        (Kernel.A right • CountingDual.value right - Kernel.beta right • PositionCounting.value right rightZero) +
      star (Kernel.A left ^ 2 - Kernel.beta left ^ 2) * star (inner ℂ (JointCounting.value right rightZero)
        (ResponseCounting.value false)) +
      (Kernel.A right ^ 2 - Kernel.beta right ^ 2) * inner ℂ (JointCounting.value left leftZero)
        (ResponseCounting.value false) = 0 := by
    rw [symmetric]
    linear_combination ward
  rw [value] at actual
  exact actual

end
end OriginalRieszFinitePairing.CoPoisson.Ward.JointWardReadback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
