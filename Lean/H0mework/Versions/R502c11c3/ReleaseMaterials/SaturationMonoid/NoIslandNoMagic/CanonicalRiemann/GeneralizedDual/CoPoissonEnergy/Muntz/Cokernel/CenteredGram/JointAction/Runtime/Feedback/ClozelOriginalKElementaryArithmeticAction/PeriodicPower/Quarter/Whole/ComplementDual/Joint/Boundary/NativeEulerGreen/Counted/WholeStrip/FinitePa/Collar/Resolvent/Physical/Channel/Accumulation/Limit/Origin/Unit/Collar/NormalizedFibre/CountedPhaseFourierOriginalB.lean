import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseFourierWindow

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalPaPhysicalGreen
open OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open FourierTransform
open scoped Topology FourierTransform BoundedContinuousFunction InnerProductSpace

open private phase_source_compact phase_source_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseInput
open private cutoff_split_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
open private seed_quarter_balance smooth_dual_inverse from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open private hilbert_wave_of_tempered_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseFourierWindow
open private actual_phase_outer_constant from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseField
open private moment from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel


local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "T" => burnolTruncatedFourier
local notation "μ" => burnolQuarterMeanCoefficient
local notation "BI" => burnolMeanZeroBlockInverse
local notation "B" => burnolRieszSingleFourierSource
local notation "B₀" => fun c => logBFirst c 0
local notation "η" => burnolAmbientMeanZeroFourier
local notation "leading" => ForcingPrimitive.leadingCoefficient
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "clock" => fun n : Nat => Real.log ((n+2 : Nat) : ℝ)

private theorem counted_seed_wave_quarter (c : BurnolCompletedMellinCoordinate) :
    countedWaveWindow q (compactPhaseWave (countedSeedSplit c)) =
      Constructor.compact (Constructor.fourierRaw (seedRaw c.value))
        (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne)) := by
  apply Lp.ext
  filter_upwards [counted_wave_window_read q (compactPhaseWave (countedSeedSplit c)),
    Constructor.compact_read (Constructor.fourierRaw (seedRaw c.value))
      (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne))] with x first second
  rw [first, second, actual_counted_seed_wave_read]

/-- The original quarter column keeps the actual ambient and seed wave
components before either component's mean is removed. -/
theorem actual_counted_homogeneous_quarter_wave (c : BurnolCompletedMellinCoordinate) :
    countedHomogeneousFourierWindow c q = leading c • SingularCounting.powerL2 c := by
  unfold countedHomogeneousFourierWindow
  rw [counted_seed_wave_quarter, add_comm]
  exact seed_quarter_balance c

private theorem phase_input_wave_supported (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, q < |x| →
      (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)).2 x = 0 := by
  let v := countedPhaseSource c n
  have complete := originalPhysicalCutoff_coeFn q v
  change (originalPhysicalCutoff q (countedPhaseSource c n) : ℝ → ℂ) =ᵐ[volume] _ at complete
  rw [phase_source_compact] at complete
  filter_upwards [complete, cutoff_split_read r₀ v] with x all split outside
  have missing : x ∉ symmetricInterval q := fun h => outside.not_ge (abs_le.mpr h)
  have small : x ∉ symmetricInterval r₀ := fun h => outside.not_ge ((abs_le.mpr h).trans (by norm_num))
  change v x = _ at all
  rw [indicator_of_notMem missing] at all
  exact split.2.trans (by rw [indicator_of_notMem small, all, sub_zero])

private theorem phase_input_fourier_wave (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    (fourierL2 (countedPhaseSource c n) : ℝ → ℂ) =ᵐ[volume]
      compactPhaseWave (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)) := by
  apply hilbert_wave_of_tempered_read
  intro test
  have source := compact_phase_wave_tempered _ (phase_input_wave_supported c n) test
  rw [distributionOfSplit_from_cutoff, Lp.fourier_toTemperedDistribution_eq] at source
  exact source

private theorem phase_input_quarter (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    Rq (fourierL2 (countedPhaseSource c n)) =
      countedWaveWindow q (compactPhaseWave (splitAtPhysicalCutoff r₀ (countedPhaseSource c n))) := by
  apply Lp.ext
  let v := fourierL2 (countedPhaseSource c n)
  let wave := compactPhaseWave (splitAtPhysicalCutoff r₀ (countedPhaseSource c n))
  have actual := ae_restrict_of_ae (s := symmetricInterval q) (phase_input_fourier_wave c n)
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) v, actual, counted_wave_window_read q wave]
    with x domain read returned
  exact domain.trans (read.trans returned.symm)

/-- Apply the original Fourier forcing leg and its original block inverse to
the finite actual phase source. -/
def countedPhaseOriginalB (c : BurnolCompletedMellinCoordinate) (n : Nat) : M :=
  BI (η (countedPhaseSource c n))

/-- The original counted source pays the exact old B and zero-th log column
in the strong quarter topology. -/
theorem actual_counted_phase_original_B (c : BurnolCompletedMellinCoordinate) :
    Tendsto (countedPhaseOriginalB c) atTop (𝓝 ((-(1/2 : ℂ)) • (leading c • B₀ c-B c))) := by
  let consumer := burnolMeanZeroBlockInverse.comp (Constructor.zeroMean.comp ((countedWaveWindow q).comp compactPhaseWave))
  have source := (consumer.continuous.tendsto _).comp (actual_counted_phase_source_limit c)
  have limit : consumer (countedSeedSplit c) = leading c • B₀ c-B c := by
    change BI (Constructor.zeroMean (countedWaveWindow q (compactPhaseWave (countedSeedSplit c)))) = _
    rw [counted_seed_wave_quarter]
    change BI (firstSource c.value c.belowOne) = _
    rw [← smooth_dual_inverse]
    exact (actual_native_smooth c).symm
  rw [map_smul, limit] at source
  apply source.congr'
  filter_upwards with n
  let value := countedPhaseSource c n
  have even : burnolAmbientEvenPart value = value := by
    unfold burnolAmbientEvenPart
    change (1/2 : ℂ) • (countedPhaseSource c n+reflectL2 (countedPhaseSource c n)) = _
    rw [phase_source_even, ← two_smul ℂ value, smul_smul]
    norm_num
  change BI (Constructor.zeroMean (countedWaveWindow q
    (compactPhaseWave (splitAtPhysicalCutoff r₀ value)))) =
      BI (Constructor.zeroMean (Rq (fourierL2 (burnolAmbientEvenPart value))))
  rw [even, phase_input_quarter]

private theorem quarter_mean_continuous : Continuous μ := by
  unfold burnolQuarterMeanCoefficient
  exact (innerSL ℂ (intervalConstant q)).continuous.div_const _

/-- The two original return means consume the same strongly generated B leg. -/
theorem actual_counted_phase_B_two_means (c : BurnolCompletedMellinCoordinate) :
    let limit : M := (-(1/2 : ℂ)) • (leading c • B₀ c-B c)
    Tendsto (fun n => (μ (T (countedPhaseOriginalB c n : Hq)),
        μ (T (S (countedPhaseOriginalB c n) : Hq)))) atTop
      (𝓝 (μ (T (limit : Hq)), μ (T (S limit : Hq)))) := by
  have actual := actual_counted_phase_original_B c
  have first : Continuous (fun b : M => μ (T (b : Hq))) :=
    quarter_mean_continuous.comp (burnolTruncatedFourier.continuous.comp continuous_subtype_val)
  have second : Continuous (fun b : M => μ (T (S b : Hq))) :=
    first.comp burnolMeanZeroTruncatedFourier.continuous
  exact ((first.tendsto _).comp actual).prodMk_nhds ((second.tendsto _).comp actual)

/-- The actual B return and the outer R clock generate the same finite part. -/
theorem actual_counted_phase_B_outer_feedback (c : BurnolCompletedMellinCoordinate) :
    let m := moment c (E (S (nativeSmooth c) : Hq))
    Tendsto (fun n => (countedPhaseOuterCoefficient c n+(clock n : ℂ),
        (-2 : ℂ)*moment c (E (S (countedPhaseOriginalB c n) : Hq)))) atTop (𝓝 (m,m)) := by
  let observer := (moment c).comp (burnolQuarterZeroExtension.comp
    ((Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp S))
  have original : Tendsto (countedPhaseOriginalB c) atTop (𝓝 ((-(1/2 : ℂ)) • nativeSmooth c)) :=
    actual_counted_phase_original_B c
  have feedback := (((observer.continuous.tendsto _).comp original).const_mul (-2 : ℂ))
  rw [map_smul, smul_eq_mul, ← mul_assoc, show (-2 : ℂ)*(-(1/2 : ℂ)) = 1 by norm_num,
    one_mul] at feedback
  exact (actual_phase_outer_constant c).prodMk_nhds feedback

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
