import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Source
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

-- The source interval action has a resonance-safe finite difference; no inverse scalar is supplied.
theorem source_power_difference (lambda : ℂ) (lower upper : ℝ) (positive : 0<lower) (ordered : lower≤upper) :
    lambda*(∫ x : ℝ in lower..upper,(x:ℂ)^(lambda-1))=(upper:ℂ)^lambda-(lower:ℂ)^lambda := by
  by_cases zero : lambda=0
  · simp only [zero,zero_mul,Complex.cpow_zero,sub_self]
  have away : (0:ℝ)∉Set.uIcc lower upper := by
    rw [uIcc_of_le ordered]
    intro inside
    exact not_le_of_gt positive inside.1
  have integrable := intervalIntegral.intervalIntegrable_cpow (a:=lower) (b:=upper) (r:=lambda-1) (μ:=volume) (Or.inr away)
  have differential : ∀ x∈Set.uIcc lower upper,HasDerivAt (fun t:ℝ=>(t:ℂ)^lambda) (lambda*(x:ℂ)^(lambda-1)) x := by
    intro x inside
    exact hasDerivAt_ofReal_cpow_const (fun same=>away (same ▸ inside)) zero
  have source := intervalIntegral.integral_eq_sub_of_hasDerivAt differential (integrable.const_mul lambda)
  rw [intervalIntegral.integral_const_mul] at source
  exact source

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
