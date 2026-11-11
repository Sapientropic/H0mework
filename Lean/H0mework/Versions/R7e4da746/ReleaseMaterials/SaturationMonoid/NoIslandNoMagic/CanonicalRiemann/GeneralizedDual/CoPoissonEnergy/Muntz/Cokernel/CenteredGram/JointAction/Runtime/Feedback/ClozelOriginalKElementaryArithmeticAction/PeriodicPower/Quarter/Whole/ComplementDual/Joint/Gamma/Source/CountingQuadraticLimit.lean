import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.ResolventBoundary
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Continuity
import H0mework.Arithmetic.SonineProjection.MeanZeroBlock
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Trace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Channels
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousChannels
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCountingSource
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.SourceDerivative
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.RawDerivative
import H0mework.Versions.R7e4da746.Arithmetic.RieszCanonicalRaw.RieszSingleFourierSource
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.CountingQuadraticLimit
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszSource OriginalRieszSourceGreen
open OriginalGamma.Source.CountingQuadratic
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def dualQuadratic (i : ℕ × ℕ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (CountingDual.sourceCLM i.1).adjoint * (CountingDual.sourceCLM i.2).adjoint

theorem dual_dilation (N : ℕ) (time : ℝ) (value : BurnolL2) :
    DualSource.source N (burnolMultiplicativeDilation time value) =
      burnolMultiplicativeDilation time (DualSource.source N value) := by
  have channel (radius : ℝ) :
      ContinuousChannels.channel 1 radius (burnolMultiplicativeDilation time value) =
        burnolMultiplicativeDilation time (ContinuousChannels.channel 1 radius value) := by
    simp only [ContinuousChannels.channel, map_smul, burnolMultiplicativeDilation_add]
    rw [add_comm]
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub, map_sum]
  congr 1
  exact (burnolMultiplicativeDilation time).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N value)

def radialOrbit (t : ℝ) (value : BurnolL2) : BurnolL2 :=
  (Real.exp (Real.log (4 * t) / 2) : ℂ) •
    burnolMultiplicativeDilation (-Real.log (4 * t)) value

theorem radialOrbit_norm (t : ℝ) (positive : 0 < t) (value : BurnolL2) :
    ‖radialOrbit t value‖ = 2 * Real.sqrt t * ‖value‖ := by
  rw [radialOrbit, norm_smul, LinearIsometryEquiv.norm_map, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have square : Real.exp (Real.log (4 * t) / 2) ^ 2 = 4 * t := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have exponent : (2 : ℝ) * (Real.log (4 * t) / 2) = Real.log (4 * t) := by ring
    rw [exponent, Real.exp_log (by positivity)]
  have amplitude : Real.exp (Real.log (4 * t) / 2) = 2 * Real.sqrt t := by
    nlinarith [Real.sq_sqrt positive.le, Real.sqrt_nonneg t, Real.exp_pos (Real.log (4 * t) / 2)]
  rw [amplitude]

theorem radialOrbit_continuous (value : BurnolL2) : ContinuousOn (fun t : ℝ => radialOrbit t value) (Ioi 0) := by
  intro t positive
  have logarithm : ContinuousAt (fun u : ℝ => Real.log (4 * u)) t :=
    (continuous_const.mul continuous_id).continuousAt.log (ne_of_gt (mul_pos (by norm_num) positive))
  exact ((Complex.continuous_ofReal.continuousAt.comp
      (Real.continuous_exp.continuousAt.comp (logarithm.div_const 2))).smul
    ((burnolMultiplicativeDilation_stronglyContinuous value).continuousAt.comp logarithm.neg)).continuousWithinAt

private theorem radial_integrand_integrable (s : Set ℝ) (measurableS : MeasurableSet s)
    (positiveS : s ⊆ Ioi 0) (coefficient : ℝ → ℂ) (measurable : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s)
    (value : BurnolL2) : IntegrableOn (fun t : ℝ => coefficient t • radialOrbit t value) s := by
  have measured : AEStronglyMeasurable (fun t : ℝ => coefficient t • radialOrbit t value)
      (volume.restrict s) := measurable.aestronglyMeasurable.smul
    (((radialOrbit_continuous value).mono positiveS).aestronglyMeasurable measurableS)
  apply (integrable_norm_iff measured).mp
  apply (weighted.const_mul (2 * ‖value‖)).congr
  filter_upwards [ae_restrict_mem measurableS] with t inside
  rw [norm_smul, radialOrbit_norm t (positiveS inside) value]
  ring

def radialSynthesis (s : Set ℝ) (coefficient : ℝ → ℂ) (value : BurnolL2) : BurnolL2 :=
  ∫ t : ℝ in s, coefficient t • radialOrbit t value

private theorem radial_synthesis_add (s : Set ℝ) (measurableS : MeasurableSet s)
    (positiveS : s ⊆ Ioi 0) (coefficient : ℝ → ℂ) (measurable : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s)
    (left right : BurnolL2) : radialSynthesis s coefficient (left + right) =
      radialSynthesis s coefficient left + radialSynthesis s coefficient right := by
  have integrableLeft := radial_integrand_integrable s measurableS positiveS coefficient measurable weighted left
  have integrableRight := radial_integrand_integrable s measurableS positiveS coefficient measurable weighted right
  unfold radialSynthesis radialOrbit
  simp only [map_add, smul_add]
  exact integral_add integrableLeft integrableRight

private theorem radial_synthesis_smul (s : Set ℝ) (coefficient : ℝ → ℂ)
    (scalar : ℂ) (value : BurnolL2) : radialSynthesis s coefficient (scalar • value) =
      scalar • radialSynthesis s coefficient value := by
  unfold radialSynthesis radialOrbit
  simp only [map_smul]
  have same (t : ℝ) : coefficient t • ((Real.exp (Real.log (4 * t) / 2) : ℂ) •
      (scalar • burnolMultiplicativeDilation (-Real.log (4 * t)) value)) =
      scalar • (coefficient t • ((Real.exp (Real.log (4 * t) / 2) : ℂ) •
        burnolMultiplicativeDilation (-Real.log (4 * t)) value)) := by module
  simp_rw [same, integral_smul]

private theorem radial_synthesis_bound (s : Set ℝ) (measurableS : MeasurableSet s)
    (positiveS : s ⊆ Ioi 0) (coefficient : ℝ → ℂ) (value : BurnolL2) :
    ‖radialSynthesis s coefficient value‖ ≤
      (2 * ∫ t : ℝ in s, Real.sqrt t * ‖coefficient t‖) * ‖value‖ := by
  have raw : (fun t : ℝ => ‖coefficient t • radialOrbit t value‖) =ᵐ[volume.restrict s]
      fun t => (2 * ‖value‖) * (Real.sqrt t * ‖coefficient t‖) := by
    filter_upwards [ae_restrict_mem measurableS] with t inside
    rw [norm_smul, radialOrbit_norm t (positiveS inside) value]
    ring
  calc
    ‖radialSynthesis s coefficient value‖ ≤
        ∫ t : ℝ in s, ‖coefficient t • radialOrbit t value‖ := norm_integral_le_integral_norm _
    _ = _ := by rw [integral_congr_ae raw, integral_const_mul]; ring

def radialSynthesisCLM (s : Set ℝ) (measurableS : MeasurableSet s) (positiveS : s ⊆ Ioi 0)
    (coefficient : ℝ → ℂ) (measurable : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  ({ toFun := radialSynthesis s coefficient
     map_add' := radial_synthesis_add s measurableS positiveS coefficient measurable weighted
     map_smul' := radial_synthesis_smul s coefficient } : BurnolL2 →ₗ[ℂ] BurnolL2).mkContinuous
      (2 * ∫ t : ℝ in s, Real.sqrt t * ‖coefficient t‖)
      (radial_synthesis_bound s measurableS positiveS coefficient)

theorem radialSynthesisCLM_apply (s : Set ℝ) (measurableS : MeasurableSet s) (positiveS : s ⊆ Ioi 0)
    (coefficient : ℝ → ℂ) (measurable : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s) (value : BurnolL2) :
    radialSynthesisCLM s measurableS positiveS coefficient measurable weighted value =
      ∫ t : ℝ in s, coefficient t • radialOrbit t value := rfl

theorem return_weighted_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => Real.sqrt t * ‖burnolRieszReturnRawDerivative c t‖) (Ioc 0 q) :=
  ((Real.continuous_sqrt.mul (burnolRieszReturnRawDerivative_continuous c).norm).integrableOn_Icc).mono_set
    Ioc_subset_Icc_self

theorem tail_weighted_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => Real.sqrt t * ‖(t : ℂ) ^ (-star c.value - 1)‖) (Ioi q) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith [c.rightHalf] : -c.value.re - 1 / 2 < -1)
    (by norm_num : (0 : ℝ) < q)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t inside
  have positive : 0 < t := lt_trans (by norm_num) inside
  rw [Real.sqrt_eq_rpow t, Complex.norm_cpow_eq_rpow_re_of_pos positive, ← Real.rpow_add positive]
  congr 1
  simp
  ring

theorem whole_tail_measurable (c : BurnolCompletedMellinCoordinate) :
    Measurable (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1)) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro t outside
  have nonzero : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
  exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr nonzero)).continuousWithinAt

def returnSynthesis (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  radialSynthesisCLM (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (burnolRieszReturnRawDerivative c) (burnolRieszReturnRawDerivative_continuous c).measurable
    (return_weighted_integrable c)

def tailSynthesis (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  radialSynthesisCLM (Ioi q) measurableSet_Ioi (Ioi_subset_Ioi (by norm_num))
    (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1)) (whole_tail_measurable c) (tail_weighted_integrable c)

def bSynthesis (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  radialSynthesisCLM (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (sourceRawDerivative c) (source_slope_measurable c) (b_weighted_slope_integrable c)

def originalBaseSynthesis (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  Kernel.A c • ContinuousLinearMap.id ℂ BurnolL2 - returnSynthesis c + (star c.value / 2) • tailSynthesis c

def originalBSynthesis (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  Kernel.beta c • ContinuousLinearMap.id ℂ BurnolL2 - bSynthesis c

theorem original_base_synthesis (c : BurnolCompletedMellinCoordinate) :
    KCountingSource.base c = originalBaseSynthesis c ConstantDual.seed := by
  rw [original_base_step_reconstruction]
  rfl

theorem original_b_synthesis (c : BurnolCompletedMellinCoordinate) :
    burnolQuarterZeroExtension (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2) =
      originalBSynthesis c ConstantDual.seed := by
  rw [original_b_step_reconstruction]
  rfl

theorem source_fourier (N : ℕ) (value : BurnolL2) :
    CountingDual.sourceCLM N (fourierL2 value) = fourierL2 (DualSource.source N value) := by
  have channel (a : ℝ) : ContinuousChannels.channel (-1) a (fourierL2 value) =
      fourierL2 (ContinuousChannels.channel 1 a value) := by
    simp only [ContinuousChannels.channel, neg_one_mul, one_mul, map_smul,
      fourierL2_burnolMultiplicativeDilation]
  have integer (n : ℕ) : Channels.sourceChannel n (fourierL2 value) =
      fourierL2 (ContinuousChannels.channel 1 n value) := by
    simpa only [ContinuousChannels.channel, Channels.sourceChannel, neg_one_mul] using channel n
  rw [CountingDual.sourceCLM_apply]
  unfold FiniteForcing.source ContinuousChannels.normalization DualSource.source
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N value)

end
end OriginalGamma.Source.CountingQuadraticLimit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
