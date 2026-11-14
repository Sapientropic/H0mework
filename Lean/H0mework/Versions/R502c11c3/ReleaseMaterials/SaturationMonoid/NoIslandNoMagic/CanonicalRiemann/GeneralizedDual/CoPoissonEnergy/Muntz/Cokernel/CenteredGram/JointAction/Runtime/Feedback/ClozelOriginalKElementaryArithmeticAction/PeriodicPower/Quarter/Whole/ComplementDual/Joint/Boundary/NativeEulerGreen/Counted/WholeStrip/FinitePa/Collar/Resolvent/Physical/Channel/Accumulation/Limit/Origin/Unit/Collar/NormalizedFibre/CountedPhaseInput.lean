import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedStrongOriginTrace

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen OriginalRieszSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKCoefficientBFiniteAction
open scoped Topology ENNReal

open private rho_le_half counted_input_even normalized_input_compact from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedStrongInput
open private positive_window_L1_bound from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Rate
open private cutoff_split_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
open private even_cut_reconstruction homogeneous_tail_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit
open private mean_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "box" => symmetricInterval r₀
local notation "pos" => Ioc (0 : ℝ) r₀
local notation "μ₊" => Measure.restrict (volume : Measure ℝ) pos
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "N" => fun n : Nat => ((n+2 : Nat) : ℝ)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "clock" => fun n : Nat => Real.log (N n)
local notation "rho" => fun n : Nat => q/N n
local notation "delta" => fun c (n : Nat) => floorFromResponses c+riemannZeta (s₀ c) • elementarySource c-compensated c (n+2)
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "bφ" => fun c n => (phase c n)⁻¹*B c n

/-- The same actual count difference at its original phase scale. -/
def countedPhaseSource (c : BurnolCompletedMellinCoordinate) (n : Nat) : BurnolL2 :=
  (phase c n)⁻¹ • delta c n

private theorem phase_rescale (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    countedPhaseSource c n = (clock n : ℂ) • (((clock n : ℂ)*phase c n)⁻¹ • delta c n) := by
  unfold countedPhaseSource
  have live : (clock n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by dsimp only; exact_mod_cast (by omega : 1 < n+2))).ne'
  rw [smul_smul, mul_inv_rev, mul_left_comm, mul_inv_cancel₀ live, mul_one]

private theorem phase_source_even (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    reflectL2 (countedPhaseSource c n) = countedPhaseSource c n := by
  rw [phase_rescale, map_smul, counted_input_even]

private theorem phase_source_compact (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    originalPhysicalCutoff q (countedPhaseSource c n) = countedPhaseSource c n := by
  rw [phase_rescale]
  change FiniteMobiusResolventFlux.cutoff q ((clock n : ℂ) • _) = _
  rw [map_smul]
  exact congrArg ((clock n : ℂ) • ·) (normalized_input_compact c n)

private theorem phase_parity (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, countedPhaseSource c n (-x) = countedPhaseSource c n x := by
  have reflected := Lp.coeFn_compMeasurePreserving (countedPhaseSource c n) negMeasurePreserving
  change ∀ᵐ x : ℝ ∂volume, reflectL2 (countedPhaseSource c n) x = countedPhaseSource c n (-x) at reflected
  rw [phase_source_even] at reflected
  exact reflected.mono fun _ h => h.symm

private theorem seed_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    seedRaw c.value (-x) = seedRaw c.value x := by simp only [seedRaw, powerRaw, abs_neg]

private theorem phase_settled_positive (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, 0 < x → x ≤ q → rho n < x → countedPhaseSource c n x = bφ c n*seedRaw c.value x := by
  filter_upwards [actual_settled_count_difference c n, Lp.coeFn_smul (phase c n)⁻¹ (delta c n)]
    with x atx scaleRead positive inside covered
  have npos : 0 < N n := by positivity
  have settled : q/x < N n := (div_lt_iff₀ positive).mpr (by
    have paid := (div_lt_iff₀ npos).mp covered
    rwa [mul_comm] at paid)
  change ((phase c n)⁻¹ • delta c n : BurnolL2) x = _
  rw [scaleRead, Pi.smul_apply, smul_eq_mul, atx positive inside settled, mul_assoc]

private theorem compact_seed_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (seedRaw c.value) (symmetricInterval q) (volume : Measure ℝ) :=
  actual_seed_integrable c.value c.belowOne

private theorem centre_seed_integrable (c : BurnolCompletedMellinCoordinate) :
    Integrable (Set.indicator box (seedRaw c.value)) volume :=
  (integrable_indicator_iff (measurableSet_symmetricInterval r₀)).mpr
    ((compact_seed_integrable c).mono_set fun _ h => abs_le.mp ((abs_le.mpr h).trans (by norm_num)))

private def seedExterior (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  originalPhysicalCutoff q (countedHomogeneousSplit c).2 -
    GapEuler.gapMean q c • (FiniteMobiusResolventFlux.box q-FiniteMobiusResolventFlux.box r₀)

/-- The settled actual count reads the centre and the collar of the same seed. -/
def countedSeedSplit (c : BurnolCompletedMellinCoordinate) : L¹ × BurnolL2 :=
  ((centre_seed_integrable c).toL1 (Set.indicator box (seedRaw c.value)), seedExterior c)

private theorem seed_exterior_read (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, seedExterior c x =
      if r₀ < |x| ∧ |x| ≤ q then seedRaw c.value x else 0 := by
  let power := (countedHomogeneousSplit c).2
  let edge := originalPhysicalCutoff q power
  let u := FiniteMobiusResolventFlux.box q
  let v := FiniteMobiusResolventFlux.box r₀
  let mean := GapEuler.gapMean q c
  have seed (x : ℝ) : seedRaw c.value x = ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ)-mean := by
    unfold seedRaw
    rw [mul_sub, mean_power c, powerRaw]
    ring
  filter_upwards [Lp.coeFn_sub edge (mean • (u-v)), Lp.coeFn_smul mean (u-v), Lp.coeFn_sub u v,
    originalPhysicalCutoff_coeFn q power, homogeneous_tail_read c, FiniteMobiusResolventFlux.box_read q,
    FiniteMobiusResolventFlux.box_read r₀] with x difference scalar subtraction edgeRead powerRead uRead vRead
  change seedExterior c x = _ at difference
  change power x = _ at powerRead
  change u x = _ at uRead
  change v x = _ at vRead
  rw [difference, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, subtraction, Pi.sub_apply, edgeRead, uRead, vRead]
  by_cases small : x ∈ box
  · have inside : x ∈ symmetricInterval q := abs_le.mp ((abs_le.mpr small).trans (by norm_num))
    rw [indicator_of_mem small, indicator_of_mem inside, indicator_of_mem inside, powerRead,
      if_neg (not_lt_of_ge (abs_le.mpr small)), sub_self, mul_zero, sub_self,
      if_neg (fun h => (not_lt_of_ge (abs_le.mpr small)) h.1)]
  · have outside : r₀ < |x| := lt_of_not_ge (fun h => small (abs_le.mp h))
    rw [indicator_of_notMem small, sub_zero]
    by_cases inside : x ∈ symmetricInterval q
    · rw [indicator_of_mem inside, indicator_of_mem inside, powerRead, if_pos outside,
        mul_one, if_pos ⟨outside, abs_le.mpr inside⟩, seed]
    · rw [indicator_of_notMem inside, indicator_of_notMem inside, mul_zero, sub_zero,
        if_neg (fun h => inside (abs_le.mp h.2))]

private theorem phase_exterior (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)).2 = bφ c n • (countedSeedSplit c).2 := by
  have covered : ∀ᵐ x : ℝ ∂volume, r₀ < |x| → |x| ≤ q →
      countedPhaseSource c n x = bφ c n*seedRaw c.value x := by
    have read := phase_settled_positive c n
    filter_upwards [read, negMeasurePreserving.quasiMeasurePreserving.ae read, phase_parity c n]
      with x direct opposite parity live inside
    have nonzero : x ≠ 0 := abs_pos.mp ((by norm_num : 0 < r₀).trans live)
    rcases lt_or_gt_of_ne nonzero with negative | positive
    · change 0 < -x → -x ≤ q → rho n < -x → _ at opposite
      rw [abs_of_neg negative] at live inside
      rw [← parity, opposite (neg_pos.mpr negative) inside ((rho_le_half n).trans_lt live), seed_even]
    · rw [abs_of_pos positive] at live inside
      exact direct positive inside ((rho_le_half n).trans_lt live)
  have source := originalPhysicalCutoff_coeFn q (countedPhaseSource c n)
  rw [phase_source_compact] at source
  apply Lp.ext
  filter_upwards [cutoff_split_read r₀ (countedPhaseSource c n), covered, source, seed_exterior_read c,
    Lp.coeFn_smul (bφ c n) (seedExterior c)] with x split settled compact seed scalar
  change _ = (bφ c n • seedExterior c : BurnolL2) x
  rw [split.2, scalar, Pi.smul_apply, smul_eq_mul, seed]
  by_cases small : x ∈ box
  · rw [indicator_of_mem small, sub_self, if_neg (fun h => (not_lt_of_ge (abs_le.mpr small)) h.1), mul_zero]
  · have outside : r₀ < |x| := lt_of_not_ge (fun h => small (abs_le.mp h))
    rw [indicator_of_notMem small, sub_zero]
    by_cases inside : x ∈ symmetricInterval q
    · rw [if_pos ⟨outside, abs_le.mpr inside⟩, settled outside (abs_le.mpr inside)]
    · rw [if_neg (fun h => inside (abs_le.mp h.2)), mul_zero, compact, indicator_of_notMem inside]

private theorem phase_uncovered_mass (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ∫ x in Ioc (0 : ℝ) (rho n), ‖countedPhaseSource c n x‖) atTop (𝓝 0) := by
  obtain ⟨budget, budget_nonnegative, rate⟩ := actual_counted_source_tail_bound c
  let β := c.value.re
  have indices : Tendsto N atTop atTop := by
    simpa only [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  let C := budget*(2*q)^(1/2 : ℝ)
  have goes : Tendsto (fun n : Nat => C*(N n)^(β-1)) atTop (𝓝 0) := by
    have power := (tendsto_rpow_neg_atTop (sub_pos.mpr c.belowOne)).comp indices
    simpa only [neg_sub, Function.comp_def, mul_zero] using power.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg (fun _ => norm_nonneg _)) _ goes
  filter_upwards with n
  let M : ℝ := (n+1 : Nat)
  have mp : 0 < M := by dsimp only [M]; positivity
  have np : 0 < N n := by positivity
  have width : 0 ≤ rho n := by positivity
  have half : N n/2 ≤ M := by dsimp only [M]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have rate' : ‖delta c n‖ ≤ budget*((N n/2)^(-(1/2 : ℝ))) :=
    (rate n).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) half (by norm_num)) budget_nonnegative)
  have scale : ‖(phase c n)⁻¹‖ = (N n)^β := by
    rw [norm_inv]
    change ‖((N n : ℝ) : ℂ)^(-s₀ c)‖⁻¹ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos np, neg_re, ← Real.rpow_neg np.le, neg_neg]
    simp only [β, Complex.star_def, Complex.conj_re]
  have field : ‖countedPhaseSource c n‖ ≤ (N n)^β*(budget*((N n/2)^(-(1/2 : ℝ)))) := by
    rw [countedPhaseSource, norm_smul, scale]
    exact mul_le_mul_of_nonneg_left rate' (Real.rpow_nonneg np.le _)
  have rootHalf : (N n/2)^(-(1/2 : ℝ)) = (N n)^(-(1/2 : ℝ))*(2 : ℝ)^(1/2 : ℝ) := by
    rw [Real.div_rpow np.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), neg_neg]
  have rootWidth : (rho n)^(1/2 : ℝ) = q^(1/2 : ℝ)*(N n)^(-(1/2 : ℝ)) := by
    change (q/N n)^(1/2 : ℝ) = _
    rw [Real.div_rpow (by norm_num) np.le, div_eq_mul_inv, Real.rpow_neg np.le]
  calc
    _ ≤ ‖countedPhaseSource c n‖*(rho n)^(1/2 : ℝ) := positive_window_L1_bound _ width _
    _ ≤ ((N n)^β*(budget*((N n/2)^(-(1/2 : ℝ)))))*(rho n)^(1/2 : ℝ) :=
      mul_le_mul_of_nonneg_right field (Real.rpow_nonneg width _)
    _ = C*((N n)^β*(N n)^(-(1/2 : ℝ))*(N n)^(-(1/2 : ℝ))) := by
      rw [rootHalf, rootWidth]
      dsimp only [C]
      rw [Real.mul_rpow (by norm_num) (by norm_num)]
      ring
    _ = _ := by
      rw [← Real.rpow_add np, ← Real.rpow_add np, show β+-(1/2 : ℝ)+-(1/2 : ℝ) = β-1 by ring]

private theorem seed_uncovered_mass (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ∫ x in Ioc (0 : ℝ) (rho n), ‖seedRaw c.value x‖) atTop (𝓝 0) := by
  have integrable : IntegrableOn (fun x => ‖seedRaw c.value x‖) pos (volume : Measure ℝ) :=
    ((compact_seed_integrable c).mono_set fun x (h : x ∈ pos) =>
      ⟨(by norm_num : (-q : ℝ) ≤ 0).trans h.1.le, h.2.trans (by norm_num)⟩).norm
  have antitone : Antitone (fun n : Nat => Ioc (0 : ℝ) (rho n)) := by
    intro m n less
    apply Ioc_subset_Ioc_right
    have grow : N m ≤ N n := by
      change ((m+2 : Nat) : ℝ) ≤ ((n+2 : Nat) : ℝ)
      exact_mod_cast Nat.add_le_add_right less 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) grow
  have rhoLimit : Tendsto rho atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat q).comp (tendsto_add_atTop_nat 2)
  have empty : (⋂ n : Nat, Ioc (0 : ℝ) (rho n)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have every := Set.mem_iInter.mp hx
    obtain ⟨n, before⟩ := (rhoLimit.eventually (gt_mem_nhds (every 0).1)).exists
    exact before.not_ge (every n).2
  have source := tendsto_setIntegral_of_antitone (f := fun x => ‖seedRaw c.value x‖)
    (μ := (volume : Measure ℝ)) (fun _ => measurableSet_Ioc) antitone
    ⟨0, integrable.mono_set (Ioc_subset_Ioc_right (rho_le_half 0))⟩
  simpa only [empty, setIntegral_empty] using source

private theorem centre_phase_error (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ‖(splitAtPhysicalCutoff r₀ (countedPhaseSource c n)).1 - bφ c n • (countedSeedSplit c).1‖ ≤
      2*((∫ x in Ioc 0 (rho n), ‖countedPhaseSource c n x‖)+‖bφ c n‖*(∫ x in Ioc 0 (rho n), ‖seedRaw c.value x‖)) := by
  let e := fun x : ℝ => ‖countedPhaseSource c n x-bφ c n*seedRaw c.value x‖
  let input := (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)).1
  let seed := (countedSeedSplit c).1
  let b := bφ c n
  have paid := (centre_seed_integrable c).coeFn_toL1
  have error : (fun x : ℝ => ‖(input-b • seed : L¹) x‖) =ᵐ[volume] Set.indicator box e := by
    filter_upwards [cutoff_split_read r₀ (countedPhaseSource c n), paid,
      Lp.coeFn_sub input (b • seed), Lp.coeFn_smul b seed] with x split seedRead subRead smulRead
    change seed x = _ at seedRead
    rw [subRead, Pi.sub_apply, smulRead, Pi.smul_apply, smul_eq_mul, seedRead]
    have centre : input x = _ := split.1
    rw [centre]
    by_cases inside : x ∈ box
    · rw [indicator_of_mem inside, indicator_of_mem inside, indicator_of_mem inside]
    · rw [indicator_of_notMem inside, indicator_of_notMem inside, indicator_of_notMem inside,
        mul_zero, sub_self, norm_zero]
  have even : ∀ᵐ x : ℝ ∂volume, e (-x) = e x := by
    filter_upwards [phase_parity c n] with x h
    dsimp only [e]
    rw [h, seed_even]
  have source : IntegrableOn (countedPhaseSource c n : ℝ → ℂ) pos (volume : Measure ℝ) := by
    have : IsFiniteMeasure μ₊ := ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩
    exact ((Lp.memLp (countedPhaseSource c n)).mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have seedInt : IntegrableOn (seedRaw c.value) pos (volume : Measure ℝ) :=
    (compact_seed_integrable c).mono_set fun x (h : x ∈ pos) =>
      ⟨(by norm_num : (-q : ℝ) ≤ 0).trans h.1.le, h.2.trans (by norm_num)⟩
  have eInt : IntegrableOn e pos (volume : Measure ℝ) := (source.sub (seedInt.const_mul b)).norm
  have positive : Integrable (Set.indicator pos e) volume := (integrable_indicator_iff measurableSet_Ioc).mpr eInt
  have negative : Integrable (fun x : ℝ => Set.indicator pos e (-x)) volume :=
    negMeasurePreserving.integrable_comp_of_integrable positive
  have total : (∫ x, Set.indicator pos e x+Set.indicator pos e (-x)) =
      (∫ x, Set.indicator pos e x)+(∫ x, Set.indicator pos e (-x)) := by
    simpa only [Pi.add_apply] using integral_add positive negative
  change ‖input-b • seed‖ ≤ _
  rw [L1.norm_eq_integral_norm, integral_congr_ae error, integral_congr_ae (even_cut_reconstruction e even),
    total, integral_neg_eq_self (Set.indicator pos e), ← two_mul, integral_indicator measurableSet_Ioc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  let small := Ioc (0 : ℝ) (rho n)
  have inclusion : small ⊆ pos := Ioc_subset_Ioc_right (rho_le_half n)
  have concentrated : (∫ x in pos, e x) = ∫ x in small, e x := by
    have split : (∫ x in pos, small.indicator e x) = ∫ x in small, e x := by
      rw [integral_indicator (measurableSet_Ioc (a := 0) (b := rho n)),
        Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr inclusion]
    rw [← split]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (phase_settled_positive c n), ae_restrict_mem measurableSet_Ioc]
      with x covered member
    by_cases inside : x ∈ small
    · rw [indicator_of_mem inside]
    · have live : rho n < x := lt_of_not_ge (fun h => inside ⟨member.1,h⟩)
      rw [indicator_of_notMem inside]
      dsimp only [e, b]
      rw [covered member.1 (member.2.trans (by norm_num)) live, sub_self, norm_zero]
  rw [concentrated]
  have first := (source.mono_set inclusion).norm
  have second := ((seedInt.mono_set inclusion).norm).const_mul ‖b‖
  have compare : ∀ᵐ x : ℝ ∂volume.restrict small,
      e x ≤ ‖countedPhaseSource c n x‖+‖b‖*‖seedRaw c.value x‖ := by
    filter_upwards with x
    dsimp only [e, b]
    rw [← norm_mul]
    exact norm_sub_le _ _
  have upper := integral_mono_ae (eInt.mono_set inclusion) (first.add second) compare
  change (∫ x in small, e x) ≤ ∫ x in small, ‖countedPhaseSource c n x‖+‖b‖*‖seedRaw c.value x‖ at upper
  rw [integral_add first second, integral_const_mul] at upper
  exact upper

/-- The original phase resolves the full regular source coefficient on the
same settled compact seed in the strong mixed topology. -/
theorem actual_counted_phase_source_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => splitAtPhysicalCutoff r₀ (countedPhaseSource c n)) atTop
      (𝓝 ((-(1/2 : ℂ)) • countedSeedSplit c)) := by
  have coeff : Tendsto (bφ c) atTop (𝓝 (-(1/2 : ℂ))) := actual_phase_count_limit c
  have centre := coeff.smul_const (countedSeedSplit c).1
  have outer := coeff.smul_const (countedSeedSplit c).2
  have mass := (phase_uncovered_mass c).add (coeff.norm.mul (seed_uncovered_mass c))
  simp only [mul_zero, add_zero] at mass
  have error : Tendsto (fun n : Nat => (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)).1-
      bφ c n • (countedSeedSplit c).1) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall (centre_phase_error c))
      (by simpa only [mul_zero] using mass.const_mul (2 : ℝ))
  have first := (error.add centre).congr' (Eventually.of_forall fun _ => sub_add_cancel _ _)
  rw [zero_add] at first
  have second := outer.congr' (Eventually.of_forall fun n => (phase_exterior c n).symm)
  exact first.prodMk_nhds second

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
