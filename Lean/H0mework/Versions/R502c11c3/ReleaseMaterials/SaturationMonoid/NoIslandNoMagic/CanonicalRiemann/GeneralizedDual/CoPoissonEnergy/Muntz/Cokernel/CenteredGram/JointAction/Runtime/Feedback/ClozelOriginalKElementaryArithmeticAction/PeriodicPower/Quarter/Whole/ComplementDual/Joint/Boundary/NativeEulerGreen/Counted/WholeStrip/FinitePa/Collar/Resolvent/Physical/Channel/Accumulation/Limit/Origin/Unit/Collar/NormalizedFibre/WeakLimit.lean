import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.OriginL1

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology ENNReal FourierTransform

open private half_power_integrable actual_positive_integrable from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.OriginL1
open private acted_even half_tail_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Exterior
open private radiusTail_positiveRead from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.FirstCurrent

local notation "q₀" => (1/4 : ℝ)
local notation "r₀" => (q₀/2)
local notation "box" => symmetricInterval r₀
local notation "pos" => Ioc (0 : ℝ) r₀
local notation "Y" => countedNormalizedField
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "H" => fun c (x : ℝ) => ((|x| : ℝ) : ℂ)^(-star (BurnolCompletedMellinCoordinate.value c))*(1/2 : ℂ)
local notation "tail" => fun c => (-(1/2 : ℂ)) • burnolRadiusNormalizedUnitTail (barC c) r₀ (by norm_num)
local notation "Cut" => originalPhysicalCutoff r₀

private theorem even_cut_reconstruction {V : Type*} [AddZeroClass V] (f : ℝ → V)
    (even : ∀ᵐ x ∂volume, f (-x) = f x) :
    (box).indicator f =ᵐ[volume] fun x => (pos).indicator f x+(pos).indicator f (-x) := by
  filter_upwards [even, volume.ae_ne (0 : ℝ)] with x atx nonzero
  by_cases inside : |x| ≤ r₀
  · rw [indicator_of_mem (show x ∈ box from abs_le.mp inside)]
    by_cases positive : 0 < x
    · have member : x ∈ pos := ⟨positive, by rwa [abs_of_pos positive] at inside⟩
      have opposite : -x ∉ pos := fun h => (not_lt_of_ge (neg_nonpos.mpr positive.le)) h.1
      rw [indicator_of_mem member, indicator_of_notMem opposite, add_zero]
    · have negative := lt_of_le_of_ne (le_of_not_gt positive) nonzero
      have member : -x ∈ pos := ⟨neg_pos.mpr negative, by rwa [abs_of_neg negative] at inside⟩
      rw [indicator_of_notMem (show x ∉ pos from fun h => positive h.1),
        indicator_of_mem member, zero_add, atx]
  · have missing : x ∉ box := fun h => inside (abs_le.mpr h)
    have first : x ∉ pos := fun h => inside (by rw [abs_of_pos h.1]; exact h.2)
    have second : -x ∉ pos := fun h => inside (by
      rw [← abs_neg x, abs_of_pos h.1]
      exact h.2)
    rw [indicator_of_notMem missing, indicator_of_notMem first, indicator_of_notMem second, add_zero]

private theorem homogeneous_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    H c (-x) = H c x := by simp only [abs_neg]

private theorem homogeneous_positive_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (H c) pos (volume : Measure ℝ) := by
  have paid := (show IntegrableOn (fun x : ℝ => (x : ℂ)^(-star c.value)*(1/2 : ℂ))
    (Ioc 0 q₀) (volume : Measure ℝ) from half_power_integrable c).mono_set (Ioc_subset_Ioc_right (by norm_num : r₀ ≤ q₀))
  apply paid.congr_fun _ measurableSet_Ioc
  intro x hx
  change (x : ℂ)^(-star c.value)*(1/2 : ℂ) = ((|x| : ℝ) : ℂ)^(-star c.value)*(1/2 : ℂ)
  rw [abs_of_pos hx.1]

private theorem centre_integrable (c : BurnolCompletedMellinCoordinate) :
    Integrable ((box).indicator (H c)) volume := by
  have positive : Integrable ((pos).indicator (H c)) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (homogeneous_positive_integrable c)
  have negative := negMeasurePreserving.integrable_comp_of_integrable positive
  exact (positive.add negative).congr
    (even_cut_reconstruction (H c) (Eventually.of_forall (homogeneous_even c))).symm

private def centreLimit (c : BurnolCompletedMellinCoordinate) : Lp ℂ 1 (volume : Measure ℝ) :=
  (centre_integrable c).toL1 ((box).indicator (H c))

private def countedCentre (c : BurnolCompletedMellinCoordinate) (n : Nat) : Lp ℂ 1 (volume : Measure ℝ) :=
  (originalPhysicalCutoff_integrable r₀ (Y c n)).toL1 (Cut (Y c n) : ℝ → ℂ)

private theorem normalized_even (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    reflectL2 (Y c n) = Y c n := by
  unfold countedNormalizedField
  rw [map_smul, acted_even c n]

private theorem positive_half_error (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ∫ x in pos, ‖Y c n x-H c x‖) atTop (𝓝 0) := by
  have upper := actual_normalized_counted_positive_L1 c
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ upper
  filter_upwards with n
  have read : (∫ x in pos, ‖Y c n x-H c x‖) =
      ∫ x in pos, ‖Y c n x-(x : ℂ)^(-star c.value)*(1/2 : ℂ)‖ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    change ‖Y c n x-((|x| : ℝ) : ℂ)^(-star c.value)*(1/2 : ℂ)‖ = _
    rw [abs_of_pos hx.1]
  rw [read]
  exact setIntegral_mono_set ((actual_positive_integrable c n).sub (half_power_integrable c)).norm
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ hx => (Ioc_subset_Ioc_right (by norm_num : r₀ ≤ q₀)) hx)

private theorem half_centre_strong (c : BurnolCompletedMellinCoordinate) :
    Tendsto (countedCentre c) atTop (𝓝 (centreLimit c)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have source := (positive_half_error c).const_mul (2 : ℝ)
  simp only [mul_zero] at source
  apply source.congr'
  filter_upwards with n
  let error := fun x : ℝ => ‖Y c n x-H c x‖
  have left := originalPhysicalCutoff_integrable r₀ (Y c n)
  have right := centre_integrable c
  have difference : ‖countedCentre c n-centreLimit c‖ =
      ∫ x, ‖Cut (Y c n) x-(box).indicator (H c) x‖ := by
    unfold countedCentre centreLimit
    rw [← Integrable.toL1_sub, Integrable.norm_toL1_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm (left.sub right).aestronglyMeasurable]
    rfl
  have shapes : (fun x => ‖Cut (Y c n) x-(box).indicator (H c) x‖) =ᵐ[volume] (box).indicator error := by
    filter_upwards [originalPhysicalCutoff_coeFn r₀ (Y c n)] with x cut
    rw [cut]
    by_cases member : x ∈ box
    · rw [indicator_of_mem member, indicator_of_mem member, indicator_of_mem member]
    · rw [indicator_of_notMem member, indicator_of_notMem member,
        indicator_of_notMem member, sub_self, norm_zero]
  have even : ∀ᵐ x : ℝ ∂volume, error (-x) = error x := by
    have reflection := Lp.coeFn_compMeasurePreserving (Y c n) negMeasurePreserving
    change ∀ᵐ x : ℝ ∂volume, reflectL2 (Y c n) x = Y c n (-x) at reflection
    rw [normalized_even] at reflection
    filter_upwards [reflection] with x h
    dsimp only [error]
    rw [← h, abs_neg]
  have positive : Integrable ((pos).indicator error) volume := by
    have yInt : IntegrableOn (Y c n : ℝ → ℂ) pos (volume : Measure ℝ) := (show IntegrableOn (Y c n : ℝ → ℂ)
      (Ioc 0 q₀) (volume : Measure ℝ) from actual_positive_integrable c n).mono_set (Ioc_subset_Ioc_right (by norm_num))
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact (yInt.sub (homogeneous_positive_integrable c)).norm
  have negative : Integrable (fun x : ℝ => (pos).indicator error (-x)) volume :=
    negMeasurePreserving.integrable_comp_of_integrable positive
  have sum : (∫ x, (pos).indicator error x+(pos).indicator error (-x)) =
      (∫ x, (pos).indicator error x)+(∫ x, (pos).indicator error (-x)) := by
    simpa only [Pi.add_apply] using integral_add positive negative
  rw [difference, integral_congr_ae shapes, integral_congr_ae (even_cut_reconstruction error even),
    sum, integral_neg_eq_self ((pos).indicator error), ← two_mul, integral_indicator measurableSet_Ioc]

/-- The original homogeneous field is represented by its integrable centre and
its square-integrable exterior, both selected by the same physical cutoff. -/
def countedHomogeneousDistribution (c : BurnolCompletedMellinCoordinate) : S' :=
  (centreLimit c : S')+((tail c : BurnolL2) : S')

private theorem counted_cutoff_distribution (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    (countedCentre c n : S') = (Cut (Y c n) : S') := by
  ext test
  simp only [Lp.toTemperedDistribution_apply]
  have read := (originalPhysicalCutoff_integrable r₀ (Y c n)).coeFn_toL1
  apply integral_congr_ae
  filter_upwards [read] with x hx
  change countedCentre c n x = _ at hx
  rw [hx]

private theorem counted_full_weak (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n => (Y c n : S')) atTop (𝓝 (countedHomogeneousDistribution c)) := by
  let centre := Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 1
  let exterior := Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2
  have inner := (centre.continuous.tendsto (centreLimit c)).comp (half_centre_strong c)
  have outer := (exterior.continuous.tendsto (tail c)).comp (actual_normalized_counted_half_exterior c)
  apply (inner.add outer).congr'
  filter_upwards with n
  change (countedCentre c n : S')+exterior (Y c n-Cut (Y c n)) = exterior (Y c n)
  rw [counted_cutoff_distribution, map_sub]
  change exterior (Cut (Y c n))+(exterior (Y c n)-exterior (Cut (Y c n))) = exterior (Y c n)
  abel

/-- The actual normalized remainder has one weak position field and the Fourier
image of that same field. Both faces use the original physical projection. -/
theorem actual_normalized_counted_remainder_joint_weak (c : BurnolCompletedMellinCoordinate) :
    let remainder := fun n : Nat => Y c n-(P (Y c n) : BurnolL2)
    let target := countedHomogeneousDistribution c-((K c : BurnolL2) : S')
    Tendsto (fun n => ((remainder n : S'), (fourierL2 (remainder n) : S'))) atTop (𝓝 (target, 𝓕 target)) := by
  let remainder := fun n : Nat => Y c n-(P (Y c n) : BurnolL2)
  let target : S' := countedHomogeneousDistribution c-((K c : BurnolL2) : S')
  let dist := Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2
  have physical : Tendsto (fun n => P (Y c n)) atTop (𝓝 (K c)) := by
    simpa only [countedNormalizedField, map_smul] using actual_scaled_counted_physical_limit c
  have inclusion : Continuous (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) :=
    continuous_subtype_val
  have physicalRead := ((dist.continuous.comp inclusion).tendsto (K c)).comp physical
  have complete : Tendsto (fun n => dist (Y c n)) atTop (𝓝 (countedHomogeneousDistribution c)) :=
    counted_full_weak c
  have positions : Tendsto (fun n => dist (remainder n)) atTop (𝓝 target) := by
    dsimp only [remainder]
    simp_rw [map_sub]
    exact complete.sub physicalRead
  have waves := ((FourierTransform.fourierCLM ℂ S').continuous.tendsto target).comp positions
  apply (positions.prodMk_nhds waves).congr'
  filter_upwards with n
  change ((remainder n : S'), 𝓕 (remainder n : S')) =
    ((remainder n : S'), (fourierL2 (remainder n) : S'))
  exact congrArg (fun field : S' => ((remainder n : S'), field))
    (Lp.fourier_toTemperedDistribution_eq (remainder n))

private theorem homogeneous_tail_read (c : BurnolCompletedMellinCoordinate) :
    ((tail c : BurnolL2) : ℝ → ℂ) =ᵐ[volume] fun x => if r₀ < |x| then H c x else 0 := by
  let t := burnolRadiusNormalizedUnitTail (barC c) r₀ (by norm_num)
  let u : BurnolL2 := (-(1/2 : ℂ)) • t
  have positive : ∀ᵐ x : ℝ ∂volume, 0 < x → u x = if r₀ < x then H c x else 0 := by
    filter_upwards [radiusTail_positiveRead (barC c) r₀ (by norm_num),
      Lp.coeFn_smul (-(1/2 : ℂ)) t] with x raw coeff xpos
    change (-(1/2 : ℂ) • t : BurnolL2) x = _ at coeff
    change (-(1/2 : ℂ) • t : BurnolL2) x = _
    rw [coeff, Pi.smul_apply, smul_eq_mul]
    have atx := raw xpos
    change t x = _ at atx
    rw [atx]
    simp only [show (barC c).value = star c.value from rfl, abs_of_pos xpos]
    split_ifs <;> ring
  have even : reflectL2 u = u := by
    dsimp only [u, t]
    rw [map_smul, half_tail_even]
  have reflect := Lp.coeFn_compMeasurePreserving u negMeasurePreserving
  change ∀ᵐ x : ℝ ∂volume, reflectL2 u x = u (-x) at reflect
  rw [even] at reflect
  filter_upwards [positive, negMeasurePreserving.quasiMeasurePreserving.ae positive, reflect,
    volume.ae_ne (0 : ℝ)] with x first second reflection nonzero
  change u x = _
  by_cases xpos : 0 < x
  · simpa only [abs_of_pos xpos] using first xpos
  · have negative := lt_of_le_of_ne (le_of_not_gt xpos) nonzero
    change 0 < -x → u (-x) = _ at second
    rw [reflection, abs_of_neg negative]
    simpa only [abs_neg, abs_of_neg negative] using second (neg_pos.mpr negative)

private theorem homogeneous_test_read (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x => test x*H c x) volume ∧
      countedHomogeneousDistribution c test = ∫ x, test x*H c x := by
  let centre := centreLimit c
  let outside : BurnolL2 := tail c
  have inside : Integrable (fun x => test x*centre x) volume :=
    (memLp_one_iff_integrable.mp (Lp.memLp centre)).mul_of_top_right test.memLp_top
  have outer : Integrable (fun x => test x*outside x) volume :=
    (test.memLp 2).integrable_mul (Lp.memLp outside)
  have both : (fun x => test x*centre x+test x*outside x) =ᵐ[volume] fun x => test x*H c x := by
    have core := (centre_integrable c).coeFn_toL1
    filter_upwards [core, homogeneous_tail_read c] with x small far
    change centre x = _ at small
    change outside x = _ at far
    rw [small, far]
    by_cases member : |x| ≤ r₀
    · rw [indicator_of_mem (show x ∈ box from abs_le.mp member), if_neg (not_lt_of_ge member),
        mul_zero, add_zero]
    · rw [indicator_of_notMem (show x ∉ box from fun h => member (abs_le.mpr h)),
        if_pos (lt_of_not_ge member), mul_zero, zero_add]
  refine ⟨(inside.add outer).congr both, ?_⟩
  change (centre : S') test+(outside : S') test = _
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]
  rw [← integral_add inside outer]
  exact integral_congr_ae both

/-- The limit uses the original two source feet of the Riesz kernel. -/
theorem actual_normalized_remainder_original_feet (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    (countedHomogeneousDistribution c-((K c : BurnolL2) : S')) test =
      ∫ x, test x*(PositionCounting.seedRaw c x+
        fourierL2 (burnolQuarterZeroExtension (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2)) x) := by
  have kInt : Integrable (fun x => test x*(K c : BurnolL2) x) volume :=
    (test.memLp 2).integrable_mul (Lp.memLp (K c : BurnolL2))
  obtain ⟨whole, read⟩ := homogeneous_test_read c test
  change countedHomogeneousDistribution c test-((K c : BurnolL2) : S') test = _
  rw [read, Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  rw [← integral_sub whole kInt]
  apply integral_congr_ae
  filter_upwards [KCounting.original_kernel_raw c] with x paid
  change (K c : BurnolL2) x = _ at paid
  rw [paid]
  ring

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
