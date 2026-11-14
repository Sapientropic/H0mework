import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseHomogeneousWave

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalRieszSource.Translator
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open FourierTransform
open scoped Topology FourierTransform BoundedContinuousFunction ContDiff

open private wave_test_integrable from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseHomogeneousWave
open private actual_phase_outer_constant from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseField
open private moment from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel


local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "R" => fun c => burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "clock" => fun n : Nat => Real.log ((n+2 : Nat) : ℝ)
local notation "A" => fun c (n : Nat) => Prod.fst (clockCoefficients c (actualClockPair c n))
local notation "m" => fun c => moment c
  (burnolQuarterZeroExtension (burnolMeanZeroTruncatedFourier (nativeSmooth c) : BurnolQuarterIntervalL2))

/-- The same outer coefficient that removes the complete original homogeneous field. -/
def countedPhaseOuterCoefficient (c : BurnolCompletedMellinCoordinate) (n : Nat) : ℂ :=
  2*((phase c n)⁻¹*A c n)

def countedPhaseFourier (c : BurnolCompletedMellinCoordinate) (n : Nat) : BurnolL2 :=
  fourierL2 (R c (countedPhaseSource c n))

def countedWaveWindow (radius : ℝ) : (ℝ →ᵇ ℂ) →L[ℂ] BurnolRadiusIntervalL2 radius :=
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (symmetricInterval radius)) :=
    ⟨lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top radius)⟩
  BoundedContinuousFunction.toLp 2 (volume.restrict (symmetricInterval radius)) ℂ

theorem counted_wave_window_read (radius : ℝ) (wave : ℝ →ᵇ ℂ) :
    (countedWaveWindow radius wave : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval radius)] wave := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (symmetricInterval radius)) :=
    ⟨lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top radius)⟩
  exact BoundedContinuousFunction.coeFn_toLp 2 _ ℂ wave

def countedHomogeneousFourierWindow (c : BurnolCompletedMellinCoordinate) (radius : ℝ) :
    BurnolRadiusIntervalL2 radius :=
  burnolRadiusRestriction radius (ForcingWhole.whole c)+
    countedWaveWindow radius (compactPhaseWave (countedSeedSplit c))

private theorem hilbert_wave_of_tempered_read (value : BurnolL2) (wave : ℝ →ᵇ ℂ)
    (read : ∀ test : SchwartzMap ℝ ℂ, (value : S') test = ∫ x, test x*wave x) :
    (value : ℝ → ℂ) =ᵐ[volume] wave := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp value).locallyIntegrable (by norm_num)) wave.continuous.locallyIntegrable
  intro test smooth finite
  have support : HasCompactSupport (Complex.ofRealCLM ∘ test) := finite.comp_left rfl
  have regular : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ test) := by fun_prop
  let g := support.toSchwartzMap regular
  have exactRead := read g
  rw [Lp.toTemperedDistribution_apply] at exactRead
  change (∫ x, (test x : ℂ) • value x) = ∫ x, (test x : ℂ)*wave x at exactRead
  simpa only [smul_eq_mul, Complex.real_smul] using exactRead

/-- The actual Hilbert wave plus its original ambient correction is exactly
the ordinary compact wave minus the same source seed contribution. -/
theorem actual_counted_phase_fourier_wave (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    let a := countedPhaseOuterCoefficient c n
    let original := countedPhaseFourier c n+a • ForcingWhole.whole c
    let compact := compactPhaseWave (countedCompactPhaseField c n)-a • compactPhaseWave (countedSeedSplit c)
    (original : ℝ → ℂ) =ᵐ[volume] compact := by
  let a := countedPhaseOuterCoefficient c n
  let Y := countedPhaseFourier c n
  let whole := ForcingWhole.whole c
  let wave := compactPhaseWave (countedCompactPhaseField c n)
  let seed := compactPhaseWave (countedSeedSplit c)
  let original := Y+a • whole
  let compact := wave-a • seed
  have support := (actual_counted_compact_phase_support c n).mono fun _ h outside => (h outside).2
  have position : distributionOfSplit (countedCompactPhaseField c n) =
      (R c (countedPhaseSource c n) : S')+a • distributionOfSplit (countedHomogeneousSplit c) := by
    unfold countedCompactPhaseField
    rw [map_add, map_smul, distributionOfSplit_from_cutoff]
    rfl
  have equality (test : SchwartzMap ℝ ℂ) : (original : S') test = ∫ x, test x*compact x := by
    have generated := compact_phase_wave_tempered _ support test
    rw [position, FourierAdd.fourier_add, FourierSMul.fourier_smul,
      Lp.fourier_toTemperedDistribution_eq, add_apply, smul_apply, smul_eq_mul,
      actual_counted_homogeneous_wave_split] at generated
    change (Y : S') test+a*((whole : S') test+∫ x, test x*seed x) = ∫ x, test x*wave x at generated
    have wholeDist : (original : S') test = (Y : S') test+a*(whole : S') test := by
      change Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2 (Y+a • whole) test = _
      rw [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rfl
    have seedInt : Integrable (fun x => a*(test x*seed x)) :=
      (wave_test_integrable seed test).const_mul a
    have compactInt : (∫ x, test x*compact x) = (∫ x, test x*wave x)-a*(∫ x, test x*seed x) := by
      rw [← integral_const_mul, ← integral_sub (wave_test_integrable wave test) seedInt]
      apply integral_congr_ae
      filter_upwards with x
      change test x*(wave x-a*seed x) = test x*wave x-a*(test x*seed x)
      ring
    rw [wholeDist, compactInt]
    linear_combination generated
  exact hilbert_wave_of_tempered_read original compact equality

/-- On every bounded frequency window the literal Hilbert wave has the
same full homogeneous column and the same ordinary compact correction. -/
theorem actual_counted_phase_fourier_window (c : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (n : Nat) :
    burnolRadiusRestriction radius (countedPhaseFourier c n) =
      countedWaveWindow radius (compactPhaseWave (countedCompactPhaseField c n))-
        countedPhaseOuterCoefficient c n • countedHomogeneousFourierWindow c radius := by
  let a := countedPhaseOuterCoefficient c n
  let original := countedPhaseFourier c n+a • ForcingWhole.whole c
  let compact := compactPhaseWave (countedCompactPhaseField c n)-a • compactPhaseWave (countedSeedSplit c)
  have exactRead : burnolRadiusRestriction radius original = countedWaveWindow radius compact := by
    apply Lp.ext
    have actual : (original : ℝ → ℂ) =ᵐ[volume] (compact : ℝ → ℂ) :=
      actual_counted_phase_fourier_wave c n
    have restricted := ae_restrict_of_ae (s := symmetricInterval radius) actual
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) original, restricted,
      counted_wave_window_read radius compact] with x domain observed returned
    exact domain.trans (observed.trans returned.symm)
  change burnolRadiusRestriction radius (countedPhaseFourier c n+a • ForcingWhole.whole c) =
    countedWaveWindow radius (compactPhaseWave (countedCompactPhaseField c n)-a •
      compactPhaseWave (countedSeedSplit c)) at exactRead
  simp only [map_add, map_sub, map_smul] at exactRead
  unfold countedHomogeneousFourierWindow
  linear_combination (norm := module) exactRead

/-- The complete subleading position and its original Hilbert wave converge
together on each bounded frequency window. -/
theorem actual_counted_phase_subleading_fourier (c : BurnolCompletedMellinCoordinate) (radius : ℝ) :
    Tendsto (fun n : Nat =>
      (splitAtPhysicalCutoff r₀ (R c (countedPhaseSource c n))-(clock n : ℂ) • countedHomogeneousSplit c,
       burnolRadiusRestriction radius (countedPhaseFourier c n)-(clock n : ℂ) •
         countedHomogeneousFourierWindow c radius)) atTop
      (𝓝 (countedPhaseSubleadingLimit c,
        countedWaveWindow radius (compactPhaseWave (countedCompactPhaseLimit c))-
          (m c) • countedHomogeneousFourierWindow c radius)) := by
  have position := actual_counted_phase_subleading_field c
  let h := countedHomogeneousFourierWindow c radius
  have outer : Tendsto (fun n : Nat => countedPhaseOuterCoefficient c n+(clock n : ℂ)) atTop (𝓝 (m c)) :=
    actual_phase_outer_constant c
  have wave := ((countedWaveWindow radius).continuous.tendsto _).comp
    (actual_counted_compact_phase_wave c).snd_nhds
  refine position.prodMk_nhds ((wave.sub (outer.smul_const h)).congr' ?_)
  filter_upwards with n
  rw [actual_counted_phase_fourier_window]
  change countedWaveWindow radius (compactPhaseWave (countedCompactPhaseField c n))-
    (countedPhaseOuterCoefficient c n+(clock n : ℂ)) • h = _
  rw [add_smul]
  abel

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
