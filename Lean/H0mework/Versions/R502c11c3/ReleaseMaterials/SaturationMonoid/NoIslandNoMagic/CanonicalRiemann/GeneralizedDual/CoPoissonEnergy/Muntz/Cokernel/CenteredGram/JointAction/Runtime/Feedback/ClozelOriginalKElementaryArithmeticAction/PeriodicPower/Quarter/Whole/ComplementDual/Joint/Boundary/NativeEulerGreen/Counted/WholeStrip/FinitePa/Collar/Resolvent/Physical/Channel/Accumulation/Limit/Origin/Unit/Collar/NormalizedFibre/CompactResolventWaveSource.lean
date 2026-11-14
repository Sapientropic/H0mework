import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactWaveVolterra
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszSource.Translator
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail
open FourierTransform
open scoped Topology InnerProductSpace FourierTransform BoundedContinuousFunction

open private cutoff_split_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
open private homogeneous_tail_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit
open private outside_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Exterior
open private radiusTail_positiveRead from H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.FirstCurrent


open private hilbert_wave_of_tempered_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseFourierWindow
open private wave_test_integrable from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseHomogeneousWave

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "tail" => fun c => burnolRadiusNormalizedUnitTail (barC c) q (by norm_num)

def compactResolventSourceMoment (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  inner ℂ (SingularCounting.powerL2 (barC c)) (burnolQuarterRestriction value)

def compactResolventBalanced (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : L¹ × BurnolL2 :=
  splitAtPhysicalCutoff r₀ (R c value)+(2*compactResolventSourceMoment c value) • countedHomogeneousSplit c

/-- Integrate the actual compact input's wave, independently of the R output. -/
def compactResolventWaveSource (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) (ξ : ℝ) : ℂ :=
  2*(∫ t : ℝ in 0..1, (t : ℂ)^(-s₀ c)*compactPhaseWave (splitAtPhysicalCutoff r₀ value) (t*ξ))

private theorem quarter_tail_outer_read (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, q < |x| → tail c x = -((|x| : ℝ) : ℂ)^(-s₀ c) := by
  let t := tail c
  have even : reflectL2 t = t := by
    unfold t burnolRadiusNormalizedUnitTail
    dsimp only
    rw [map_neg, map_add, reflectL2_reflectL2, add_comm]
  have reflect := Lp.coeFn_compMeasurePreserving t negMeasurePreserving
  change ∀ᵐ x : ℝ ∂volume, reflectL2 t x = t (-x) at reflect
  rw [even] at reflect
  have raw := radiusTail_positiveRead (barC c) q (by norm_num)
  filter_upwards [raw, negMeasurePreserving.quasiMeasurePreserving.ae raw, reflect]
    with x read opposite parity beyond
  rcases lt_or_gt_of_ne (abs_pos.mp ((by norm_num : 0 < q).trans beyond)) with negative | positive
  · rw [abs_of_neg negative] at beyond ⊢
    change t x = _
    rw [parity]
    exact (opposite (neg_pos.mpr negative)).trans (if_pos beyond)
  · rw [abs_of_pos positive] at beyond ⊢
    exact (read positive).trans (if_pos beyond)

private theorem original_compact_split_support (value : BurnolL2)
    (supported : originalPhysicalCutoff q value = value) :
    let z := splitAtPhysicalCutoff r₀ value
    ∀ᵐ x : ℝ ∂volume, q < |x| → z.1 x = 0 ∧ z.2 x = 0 := by
  have support := originalPhysicalCutoff_coeFn q value
  rw [supported] at support
  filter_upwards [cutoff_split_read r₀ value, support] with x cut read beyond
  have inner : x ∉ symmetricInterval r₀ := fun h =>
    beyond.not_ge ((abs_le.mpr h).trans (by norm_num))
  have outer : x ∉ symmetricInterval q := fun h => beyond.not_ge (abs_le.mpr h)
  have zero : value x = 0 := read.trans (indicator_of_notMem outer _)
  exact ⟨cut.1.trans (indicator_of_notMem inner _), cut.2.trans (by rw [indicator_of_notMem inner, zero, sub_zero])⟩

/-- The original compact source tail cancels with the full original homogeneous field. -/
theorem actual_compact_resolvent_balanced_support (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : originalPhysicalCutoff q value = value) (even : reflectL2 value = value) :
    let z := compactResolventBalanced c value
    ∀ᵐ x : ℝ ∂volume, q < |x| → z.1 x = 0 ∧ z.2 x = 0 := by
  let y := R c value
  let a := compactResolventSourceMoment c value
  let u := splitAtPhysicalCutoff r₀ y
  let h := countedHomogeneousSplit c
  have action : y = originalPhysicalCutoff q y+a • tail c :=
    actual_compact_R_mellin_source (barC c) value supported even
  have exterior : y-originalPhysicalCutoff q y = a • tail c := by
    linear_combination (norm := module) action
  have actual := outside_read q y
  change (y-originalPhysicalCutoff q y : BurnolL2) =ᵐ[volume]
    (fun x => if q < |x| then y x else 0) at actual
  rw [exterior] at actual
  have centreH := (counted_homogeneous_even_physical_split c).centre
  filter_upwards [cutoff_split_read r₀ y, centreH, homogeneous_tail_read c, actual,
    quarter_tail_outer_read c, Lp.coeFn_smul a (tail c), Lp.coeFn_smul (2*a) h.1,
    Lp.coeFn_smul (2*a) h.2, Lp.coeFn_add u.1 ((2*a) • h.1), Lp.coeFn_add u.2 ((2*a) • h.2)]
    with x split centre outside acted tailRead tailScale centreScale exteriorScale centreSum exteriorSum beyond
  have small : r₀ < |x| := (by norm_num : r₀ < q).trans beyond
  have missing : x ∉ symmetricInterval r₀ := fun h => small.not_ge (abs_le.mpr h)
  have yRaw : y x = a*(-((|x| : ℝ) : ℂ)^(-s₀ c)) := by
    rw [if_pos beyond, tailScale, Pi.smul_apply, smul_eq_mul, tailRead beyond] at acted
    exact acted.symm
  constructor
  · change (u.1+(2*a) • h.1 : L¹) x = 0
    have cut : u.1 x = _ := split.1
    have zero : h.1 x = 0 := centre missing
    rw [centreSum, Pi.add_apply, cut, indicator_of_notMem missing, centreScale, Pi.smul_apply,
      zero, smul_zero, add_zero]
  · change (u.2+(2*a) • h.2 : BurnolL2) x = 0
    have cut : u.2 x = _ := split.2
    have raw : h.2 x = ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ) := by
      change h.2 x = _ at outside
      rw [if_pos small] at outside
      exact outside
    rw [exteriorSum, Pi.add_apply, cut, indicator_of_notMem missing, sub_zero, exteriorScale,
      Pi.smul_apply, smul_eq_mul, raw, yRaw]
    ring

/-- The balanced field obeys the original Euler law with the literal compact input. -/
theorem actual_compact_resolvent_euler (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    eulerOfPhysicalSplit c (compactResolventBalanced c value) =
      -(2 : ℂ) • distributionOfSplit (splitAtPhysicalCutoff r₀ value) := by
  have action : eulerOfPhysicalSplit c (splitAtPhysicalCutoff r₀ (R c value)) =
      -(2 : ℂ) • (value : S') := actual_split_R_equation c value
  have homogeneous : eulerOfPhysicalSplit c (countedHomogeneousSplit c) = 0 := counted_homogeneous_euler c
  have zero (scalar : ℂ) : scalar • (0 : S') = 0 := by
    ext test
    simp [smul_apply]
  rw [compactResolventBalanced, map_add, map_smul, action, homogeneous, zero, add_zero,
    distributionOfSplit_from_cutoff]

theorem actual_compact_resolvent_source_wave (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : originalPhysicalCutoff q value = value) (even : reflectL2 value = value) (ξ : ℝ) :
    compactPhaseWave (compactResolventBalanced c value) ξ = compactResolventWaveSource c value ξ := by
  simpa only [compactResolventWaveSource, neg_neg] using compact_wave_volterra c _ _ (-(2 : ℂ))
    (actual_compact_resolvent_balanced_support c value supported even)
    (original_compact_split_support value supported) (actual_compact_resolvent_euler c value) ξ

/-- The generated ordinary source wave and its actual moment recover the whole original Hilbert Fourier field. -/
theorem actual_compact_resolvent_hilbert_wave (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : originalPhysicalCutoff q value = value) (even : reflectL2 value = value)
    (test : SchwartzMap ℝ ℂ) :
    (fourierL2 (R c value) : S') test =
      (∫ ξ, test ξ*compactResolventWaveSource c value ξ)-
        (2*compactResolventSourceMoment c value)*𝓕 (distributionOfSplit (countedHomogeneousSplit c)) test := by
  have support := (actual_compact_resolvent_balanced_support c value supported even).mono
    fun _ h beyond => (h beyond).2
  have source := compact_phase_wave_tempered (compactResolventBalanced c value) support test
  simp_rw [actual_compact_resolvent_source_wave c value supported even] at source
  rw [compactResolventBalanced, map_add, map_smul, distributionOfSplit_from_cutoff, FourierAdd.fourier_add,
    FourierSMul.fourier_smul, Lp.fourier_toTemperedDistribution_eq, add_apply, smul_apply, smul_eq_mul] at source
  exact eq_sub_of_add_eq source


private def compactResolventHilbertRaw (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) (ξ : ℝ) : ℂ :=
  compactResolventWaveSource c value ξ-
    (2*compactResolventSourceMoment c value)*(ForcingPrimitive.leadingCoefficient c*((|ξ| : ℝ) : ℂ)^(s₀ c-1))

private theorem compact_resolvent_hilbert_raw (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : originalPhysicalCutoff q value = value) (even : reflectL2 value = value) :
    (fourierL2 (R c value) : ℝ → ℂ) =ᵐ[volume] compactResolventHilbertRaw c value := by
  let a := 2*compactResolventSourceMoment c value
  let Y := fourierL2 (R c value)
  let forcing := ForcingWhole.whole c
  let W := compactPhaseWave (compactResolventBalanced c value)
  let V := compactPhaseWave (countedSeedSplit c)
  let hilbert := Y+a • forcing
  let ordinary := W-a • V
  have raw : (hilbert : ℝ → ℂ) =ᵐ[volume] ordinary := by
    apply hilbert_wave_of_tempered_read
    intro test
    have action := actual_compact_resolvent_hilbert_wave c value supported even test
    simp_rw [← actual_compact_resolvent_source_wave c value supported even] at action
    rw [actual_counted_homogeneous_wave_split] at action
    change (Y : S') test = (∫ ξ, test ξ*W ξ)-a*((forcing : S') test+∫ ξ, test ξ*V ξ) at action
    have projected : (hilbert : S') test = (Y : S') test+a*(forcing : S') test := by
      change Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2 (Y+a • forcing) test = _
      rw [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rfl
    have integral : (∫ ξ, test ξ*ordinary ξ) = (∫ ξ, test ξ*W ξ)-a*(∫ ξ, test ξ*V ξ) := by
      have integrable : Integrable (fun ξ => a*(test ξ*V ξ)) := (wave_test_integrable V test).const_mul a
      rw [← integral_const_mul, ← integral_sub (wave_test_integrable W test) integrable]
      apply integral_congr_ae
      filter_upwards with ξ
      change test ξ*(W ξ-a*V ξ) = test ξ*W ξ-a*(test ξ*V ξ)
      ring
    rw [projected, integral]
    linear_combination action
  filter_upwards [raw, Lp.coeFn_add Y (a • forcing), Lp.coeFn_smul a forcing,
    ForcingWhole.whole_read c, volume.ae_ne (0 : ℝ)] with ξ same added scaled atForcing nonzero
  change (Y+a • forcing : BurnolL2) ξ = (W-a • V : ℝ →ᵇ ℂ) ξ at same
  rw [added, Pi.add_apply, scaled, Pi.smul_apply, smul_eq_mul, atForcing] at same
  change Y ξ+a*ForcingWhole.raw c ξ = W ξ-a*V ξ at same
  have seed := actual_seed_fourier_balance_abs c ξ nonzero
  have actualSeed : V ξ = _ := actual_counted_seed_wave_read c ξ
  rw [← actualSeed] at seed
  change Y ξ = compactResolventWaveSource c value ξ-
    a*(ForcingPrimitive.leadingCoefficient c*((|ξ| : ℝ) : ℂ)^(s₀ c-1))
  rw [← actual_compact_resolvent_source_wave c value supported even]
  linear_combination same-a*seed

/-- The full Hilbert wave is computed from the actual input and its actual moment. -/
def compactResolventHilbertWave (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : originalPhysicalCutoff q value = value) (even : reflectL2 value = value) : BurnolL2 :=
  ((memLp_congr_ae (compact_resolvent_hilbert_raw c value supported even)).mp
    (Lp.memLp (fourierL2 (R c value)))).toLp (compactResolventHilbertRaw c value)

theorem actual_compact_resolvent_hilbert_wave_value (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : originalPhysicalCutoff q value = value) (even : reflectL2 value = value) :
    compactResolventHilbertWave c value supported even = fourierL2 (R c value) := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (compact_resolvent_hilbert_raw c value supported even).symm

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
