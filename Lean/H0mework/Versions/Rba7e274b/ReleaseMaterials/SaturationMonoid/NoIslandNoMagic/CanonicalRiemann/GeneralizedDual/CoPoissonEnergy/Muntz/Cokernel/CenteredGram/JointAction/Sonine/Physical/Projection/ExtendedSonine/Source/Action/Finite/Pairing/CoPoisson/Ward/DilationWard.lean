import H0mework.Versions.V2.Arithmetic.RieszResponse.ResponseRead
import H0mework.Arithmetic.RieszResponse.Integration
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.GeneratorResolvent
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard

open Complex Filter MeasureTheory
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

private def read (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)

private theorem finite_action (value rhs : BurnolL2)
    (equation : GapEuler.euler (value : TemperedDistribution ℝ ℂ) = (rhs : TemperedDistribution ℝ ℂ))
    (shift : ℝ) :
    burnolMultiplicativeDilation shift value = value +
      ∫ time : ℝ in (0 : ℝ)..shift, burnolMultiplicativeDilation time rhs := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  have action (time : ℝ) : HasDerivAt (fun h : ℝ => read test (burnolMultiplicativeDilation h value))
      (read test (burnolMultiplicativeDilation time rhs)) time := by
    have actual := Dilation.original_weak_derivative value test time
    rw [OriginalRieszFiniteResponse.original_euler_action, equation,
      ← OriginalRieszFiniteResponse.original_read] at actual
    exact actual
  have regular : Continuous (fun time : ℝ => read test (burnolMultiplicativeDilation time rhs)) :=
    (read test).continuous.comp (burnolMultiplicativeDilation_stronglyContinuous rhs)
  have actual := _root_.OriginalRieszFiniteResponse.Integration.finite_response
    (fun h : ℝ => read test (burnolMultiplicativeDilation h value))
    (fun h : ℝ => read test (burnolMultiplicativeDilation h rhs)) 0
    (by simpa only [zero_mul, sub_zero] using action) regular shift
  simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul, burnolMultiplicativeDilation_zero] at actual
  change read test (burnolMultiplicativeDilation shift value) =
    read test (value + ∫ time : ℝ in (0 : ℝ)..shift, burnolMultiplicativeDilation time rhs)
  rw [map_add, ← (read test).intervalIntegral_comp_comm
    ((burnolMultiplicativeDilation_stronglyContinuous rhs).intervalIntegrable 0 shift)]
  exact actual

/-- An actual L² Euler right-hand side generates the strong derivative of the original unitary action. -/
theorem strong_derivative (value rhs : BurnolL2)
    (equation : GapEuler.euler (value : TemperedDistribution ℝ ℂ) = (rhs : TemperedDistribution ℝ ℂ)) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift value) rhs 0 := by
  have regular := burnolMultiplicativeDilation_stronglyContinuous rhs
  have primitive := intervalIntegral.integral_hasDerivAt_right
    (regular.intervalIntegrable (0 : ℝ) 0) regular.stronglyMeasurable.stronglyMeasurableAtFilter regular.continuousAt
  have source := primitive.const_add value
  simp only [burnolMultiplicativeDilation_zero] at source
  convert! source using 1
  funext shift
  exact finite_action value rhs equation shift

/-- Both actual Euler-domain members are consumed; no stationary insertion is supplied. -/
theorem cross_balance (left leftRhs right rightRhs : BurnolL2)
    (leftEquation : GapEuler.euler (left : TemperedDistribution ℝ ℂ) = (leftRhs : TemperedDistribution ℝ ℂ))
    (rightEquation : GapEuler.euler (right : TemperedDistribution ℝ ℂ) = (rightRhs : TemperedDistribution ℝ ℂ)) :
    inner ℂ leftRhs right + inner ℂ left rightRhs = 0 := by
  have actual := (strong_derivative left leftRhs leftEquation).inner ℂ
    (strong_derivative right rightRhs rightEquation)
  simp only [burnolMultiplicativeDilation_zero] at actual
  have fixed : (fun shift : ℝ => inner ℂ (burnolMultiplicativeDilation shift left)
      (burnolMultiplicativeDilation shift right)) = fun _ : ℝ => inner ℂ left right := by
    funext shift
    exact (burnolMultiplicativeDilation shift).inner_map_map left right
  rw [fixed] at actual
  simpa only [add_comm] using actual.unique (hasDerivAt_const (0 : ℝ) (inner ℂ left right))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
