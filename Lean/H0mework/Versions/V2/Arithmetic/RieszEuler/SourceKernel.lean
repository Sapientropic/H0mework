import H0mework.Versions.V2.Arithmetic.RieszEuler.WindowTest
import H0mework.Versions.V2.Arithmetic.RieszForcing.ForcingCutoff
import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.Trace

/-!
The actual source's local weak Euler law generates its complete finite Fourier
kernel identity. The source is used as its original interval L² value; no
pointwise differentiability or continuity at zero is required.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Euler

open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal FourierTransform Topology
open Constructor Translator.ForcingCutoff WindowTest

noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem window_pairing_eq_truncated
    (state : BurnolQuarterIntervalL2) (frequency : ℝ) :
    (∫ x : ℝ in Ioc (-q) q, state x * wave frequency x) =
      burnolRadiusTruncatedFourierRaw q state frequency := by
  have native := fourierRaw_integral (state : ℝ → ℂ) frequency
  change burnolRadiusTruncatedFourierRaw q state frequency =
    ∫ x : ℝ in (-q)..q, phase frequency x * state x at native
  rw [native, intervalIntegral.integral_of_le (by norm_num : -q ≤ q)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  rw [wave_eq frequency (Ioc_subset_Icc_self inside), mul_comm]

private theorem window_moment_eq_sourceDerivative
    (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    (∫ x : ℝ in Ioc (-q) q,
      ((x : ℂ) * (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x) *
        deriv (wave frequency) x) =
      (frequency : ℂ) * burnolRieszReturnRawDerivative coordinate frequency := by
  rw [burnolRieszReturnRawDerivative_integral]
  change (∫ x : ℝ in Ioc (-q) q,
    ((x : ℂ) * (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x) *
      deriv (wave frequency) x) =
    (frequency : ℂ) * ∫ x : ℝ in Icc (-q) q,
      𝐞 (-(frequency * x)) * (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) *
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x)
  rw [integral_Icc_eq_integral_Ioc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  rw [wave_deriv frequency (Ioc_subset_Icc_self inside)]
  unfold phase
  ring

private theorem edge_wave_eq_raw (frequency : ℝ) :
    GapEuler.edge q (wave frequency) = Edge.raw q frequency := by
  have constantRead :
      (intervalConstant q : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (-q) q)] fun _ => (1 : ℂ) :=
    ae_restrict_of_ae_restrict_of_subset
      (show Ioc (-q) q ⊆ symmetricInterval q from Ioc_subset_Icc_self)
      (intervalConstant_coeFn q)
  have windowIntegral : (∫ x : ℝ in Ioc (-q) q, wave frequency x) =
      burnolRadiusTruncatedFourierRaw q (intervalConstant q) frequency := by
    rw [← window_pairing_eq_truncated]
    apply integral_congr_ae
    filter_upwards [constantRead] with x constant
    rw [constant, one_mul]
  rw [edge_pairing, wave_eq frequency (by norm_num), wave_eq frequency (by norm_num),
    windowIntegral, Edge.raw_apply]

/-- Transport the single actual source weak law to its original full Fourier kernel. -/
theorem source_kernel_ward
    (coordinate : BurnolCompletedMellinCoordinate) (db : BurnolQuarterMeanZeroCarrier)
    (weakSource :
      GapEuler.euler
        (burnolQuarterZeroExtension
          (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
            TemperedDistribution ℝ ℂ) =
        (burnolQuarterZeroExtension (db : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) - Kernel.beta coordinate • GapEuler.edge q)
    (frequency : ℝ) :
    (frequency : ℂ) * burnolRieszReturnRawDerivative coordinate frequency +
      (1 / 2 : ℂ) * burnolRadiusTruncatedFourierRaw q
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) frequency +
      burnolRadiusTruncatedFourierRaw q (db : BurnolQuarterIntervalL2) frequency =
        Kernel.beta coordinate * Edge.raw q frequency := by
  have source := congrArg (fun value : TemperedDistribution ℝ ℂ => value (wave frequency)) weakSource
  simp only [sub_apply, smul_apply, smul_eq_mul] at source
  have sourceRead := euler_zeroExtension_pairing
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    ((burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : ℝ → ℂ)
    Filter.EventuallyEq.rfl (wave frequency)
  have derivativeRead := zeroExtension_pairing (db : BurnolQuarterIntervalL2)
    ((db : BurnolQuarterIntervalL2) : ℝ → ℂ) Filter.EventuallyEq.rfl (wave frequency)
  rw [sourceRead, derivativeRead, window_moment_eq_sourceDerivative,
    window_pairing_eq_truncated, window_pairing_eq_truncated, edge_wave_eq_raw] at source
  linear_combination -source

end
end OriginalRieszSource.Euler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
