import H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.GeneratorResolvent
import H0mework.Versions.R7e4da746.Arithmetic.RieszResponse.ResponseRead

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource
open scoped Topology InnerProductSpace
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

theorem full_R_euler (z : ℂ) (right : 1/4 < z.re) (v : BurnolL2) :
    GapEuler.euler (burnolDirectRightResolvent z v : TemperedDistribution ℝ ℂ) +
      (2*z-1/2) • (burnolDirectRightResolvent z v : TemperedDistribution ℝ ℂ) =
        -(2 : ℂ) • (v : TemperedDistribution ℝ ℂ) := by
  ext test
  let r := burnolDirectRightResolvent z v
  let read : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  have orbit := burnolDirectRightResolventOrbit_hasDerivAt z right v
  have strongRead := (read.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 orbit
  have weakRead := OriginalRieszSource.Dilation.original_weak_at_zero r test
  have chart : HasDerivAt (fun t : ℝ => -t/2) (-1/2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg.div_const 2
  have weakScaled := weakRead.scomp_of_eq (0 : ℝ) chart (by norm_num)
  have same := strongRead.unique weakScaled
  change read ((z-1/4) • r+v) = (-1/2 : ℝ) • GapEuler.euler (r : TemperedDistribution ℝ ℂ) test at same
  simp only [map_add,map_smul,smul_eq_mul,Complex.real_smul,
    Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat] at same
  change GapEuler.euler (r : TemperedDistribution ℝ ℂ) test +
    (2*z-1/2)*(r : TemperedDistribution ℝ ℂ) test = -(2 : ℂ)*(v : TemperedDistribution ℝ ℂ) test
  change (z-1/4)*(r : TemperedDistribution ℝ ℂ) test+(v : TemperedDistribution ℝ ℂ) test =
    (-1/2 : ℂ)*GapEuler.euler (r : TemperedDistribution ℝ ℂ) test at same
  linear_combination 2 * same

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
