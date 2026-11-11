import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CompactConductorTailReadback
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.TruncatedFourier.ActualBridge

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.ExteriorFourier
open Complex Filter MeasureTheory Set FourierTransform
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.CompactConductorTailReadback
noncomputable section
private theorem fourier_l2_raw (value : BurnolL2) (source : Integrable (value : ℝ → ℂ)) :
    (fourierL2 value : ℝ → ℂ) =ᵐ[volume] 𝓕 (value : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (fourierL2 value)).locallyIntegrable (by norm_num)
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ source).locallyIntegrable
  · intro testReal smooth compact
    let test : SchwartzMap ℝ ℂ :=
      (compact.comp_left (show Complex.ofRealCLM 0 = 0 by rfl)).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp smooth)
    have distributional := Lp.fourier_toTemperedDistribution_eq value
    have paired := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := 𝐞) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) source test.integrable
    calc
      (∫ x : ℝ, testReal x • fourierL2 value x) = ((fourierL2 value : BurnolL2) : TemperedDistribution ℝ ℂ) test := by
        simp [test, Function.comp_apply, Complex.real_smul]
      _ = (𝓕 ((value : BurnolL2) : TemperedDistribution ℝ ℂ)) test := by
        change ((FourierTransform.fourier value : BurnolL2) : TemperedDistribution ℝ ℂ) test = _
        exact congrArg (fun d : TemperedDistribution ℝ ℂ => d test) distributional.symm
      _ = ((value : BurnolL2) : TemperedDistribution ℝ ℂ) (𝓕 test) := rfl
      _ = ∫ x : ℝ, (𝓕 test) x • value x := by simp
      _ = ∫ x : ℝ, test x • 𝓕 (value : ℝ → ℂ) x := by
        have flip : (∫ x : ℝ, 𝓕 (value : ℝ → ℂ) x * test x) =
            ∫ x : ℝ, value x * 𝓕 test x := by
          simpa only [smul_eq_mul, Real.fourier_eq, burnolRealInner_flip_fourier] using! paired
        simpa only [smul_eq_mul, mul_comm] using flip.symm
      _ = ∫ x : ℝ, testReal x • 𝓕 (value : ℝ → ℂ) x := by
        apply integral_congr_ae
        filter_upwards with x
        simp [test, Function.comp_apply, Complex.real_smul]

end
end OriginalGamma.Source.ExteriorFourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
