import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.Margin.Trace
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletRate
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RegularQuadrature
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def seedRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x| ≤ q then positionSource coordinate |x| else 0

def raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)

def eventRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n ∈ DualSourceRaw.channels x, positionSource coordinate ((n : ℝ) * |x|)

theorem seed_measurable (coordinate : BurnolCompletedMellinCoordinate) : Measurable (seedRaw coordinate) := by
  have profile : Measurable (fun x : ℝ => positionSource coordinate |x|) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x nonzero
    have positive : 0 < |x| := abs_pos.mpr (by simpa only [mem_compl_iff, mem_singleton_iff] using nonzero)
    exact ((positionSource_continuousAt coordinate positive).comp continuous_abs.continuousAt).continuousWithinAt
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) profile measurable_const

theorem raw_measurable (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : StronglyMeasurable (raw coordinate N) := by
  have kernel : StronglyMeasurable (fun p : ℝ × ℝ => seedRaw coordinate (p.1 * p.2)) :=
    ((seed_measurable coordinate).comp (by fun_prop)).stronglyMeasurable
  have continuousRead : StronglyMeasurable (fun x : ℝ => ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) :=
    kernel.integral_prod_left'
  apply StronglyMeasurable.sub _ continuousRead
  apply Finset.stronglyMeasurable_fun_sum
  intro n _
  exact ((seed_measurable coordinate).comp (by fun_prop)).stronglyMeasurable

/-- The full continuous channel vanishes only after the actual mean-zero source interval is covered. -/
theorem continuous_raw_zero (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (covered : q ≤ (N : ℝ) * |x|) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) = 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have even (a : ℝ) (positive : 0 < a) : seedRaw coordinate (a * x) = seedRaw coordinate (a * |x|) := by
    simp only [seedRaw, abs_mul, abs_of_pos positive, abs_abs]
  have scaled : (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) =
      |x|⁻¹ • ∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), seedRaw coordinate t := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => even a inside.1),
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ absolute.ne', zero_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ) * |x|)]
  have intervalRead : (∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), seedRaw coordinate t) =
      ∫ t : ℝ in Ioc 0 q, positionSource coordinate t := by
    have pointwise : EqOn (seedRaw coordinate) ((Ioc 0 q).indicator (positionSource coordinate))
        (Ioc 0 ((N : ℝ) * |x|)) := by
      intro t inside
      simp only [seedRaw, abs_of_pos inside.1, indicator_apply, mem_Ioc, inside.1, true_and]
    rw [setIntegral_congr_fun measurableSet_Ioc pointwise, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc le_rfl covered)]
  rw [scaled, intervalRead, PositionSource.positive_mass_zero, smul_zero]

theorem seed_channel (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0)
    (n : ℕ) (positive : 0 < n) :
    seedRaw coordinate ((n : ℝ) * x) =
      if n ∈ DualSourceRaw.channels x then positionSource coordinate ((n : ℝ) * |x|) else 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have incidence : (n : ℝ) * |x| ≤ q ↔ n ∈ DualSourceRaw.channels x := by
    simp only [DualSourceRaw.channels, Finset.mem_Icc, show 1 ≤ n from positive, true_and,
      Nat.le_floor_iff' positive.ne', le_div_iff₀ absolute]
  simp only [seedRaw, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), incidence]

theorem raw_event (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (complete : q / |x| < (N : ℝ)) : raw coordinate N x = eventRaw coordinate x := by
  classical
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have subset : DualSourceRaw.channels x ⊆ Finset.Ico 1 N := by
    intro n inside
    have members := Finset.mem_Icc.mp inside
    have bounded : (n : ℝ) ≤ q / |x| := (Nat.le_floor_iff' (by omega : n ≠ 0)).mp members.2
    exact Finset.mem_Ico.mpr ⟨members.1, by exact_mod_cast bounded.trans_lt complete⟩
  rw [raw, continuous_raw_zero coordinate N x nonzero ((div_lt_iff₀ absolute).mp complete).le, sub_zero]
  calc
    _ = ∑ n ∈ Finset.Ico 1 N, if n ∈ DualSourceRaw.channels x then
        positionSource coordinate ((n : ℝ) * |x|) else 0 := by
      apply Finset.sum_congr rfl
      intro n inside
      exact seed_channel coordinate x nonzero n (Finset.mem_Ico.mp inside).1
    _ = _ := by
      rw [← Finset.sum_filter]
      unfold eventRaw
      congr 1
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun member => member.2, fun member => ⟨subset member, member⟩⟩

theorem raw_eventually (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0) :
    ∀ᶠ N : ℕ in atTop, raw coordinate N x = eventRaw coordinate x := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (q / |x|))] with N complete
  exact raw_event coordinate N x nonzero complete

theorem event_aestronglyMeasurable (coordinate : BurnolCompletedMellinCoordinate) :
    AEStronglyMeasurable (eventRaw coordinate) volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun N => (raw_measurable coordinate N).aestronglyMeasurable)
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  apply tendsto_const_nhds.congr'
  filter_upwards [raw_eventually coordinate x nonzero] with N read
  exact read.symm

theorem event_outside (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (outside : q < |x|) :
    eventRaw coordinate x = 0 := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have index : ⌊q / |x|⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one absolute).mpr outside)
  rw [eventRaw, DualSourceRaw.channels, index]
  simp

theorem event_collar (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (lower : q / 2 < |x|) (upper : |x| ≤ q) : eventRaw coordinate x = positionSource coordinate |x| := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q / 2).trans lower
  have index : ⌊q / |x|⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ q / |x|)]
    constructor
    · norm_num
      exact (le_div_iff₀ absolute).mpr (by simpa using upper)
    · norm_num
      exact (div_lt_iff₀ absolute).mpr (by linarith)
  rw [eventRaw, DualSourceRaw.channels, index, Finset.Icc_self, Finset.sum_singleton]
  simp

theorem event_endpoint (coordinate : BurnolCompletedMellinCoordinate) :
    eventRaw coordinate q = -Kernel.A coordinate := by
  rw [event_collar coordinate q (by norm_num) (by norm_num), abs_of_pos (by norm_num : (0 : ℝ) < q)]
  exact OriginalRieszFinitePairing.CoPoisson.Energy.Margin.positionSource_endpoint coordinate

private theorem overflow_bound (eta : ℂ) (etaPositive : 0 < eta.re) (etaBelow : eta.re < 1) (x : ℝ) (positive : 0 < x)
    (N : ℕ) (lower : q ≤ (N : ℝ) * x) (width : (N : ℝ) * x - q ≤ x) :
    ‖(x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ eta / eta -
      (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta‖ ≤ q ^ (eta.re - 1) := by
  have integral : (∫ t : ℝ in q..((N : ℝ) * x), (t : ℂ) ^ (eta - 1)) =
      ((((N : ℝ) * x : ℝ) : ℂ) ^ eta - (q : ℂ) ^ eta) / eta := by
    rw [integral_cpow (Or.inl (by simp only [sub_re, one_re]; linarith [etaPositive])), sub_add_cancel]
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := q) (b := (N : ℝ) * x) (C := q ^ (eta.re - 1))
    (f := fun t : ℝ => (t : ℂ) ^ (eta - 1)) (fun t inside => by
      have located : t ∈ Ioc q ((N : ℝ) * x) := by simpa only [uIoc_of_le lower] using inside
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ((by norm_num : (0 : ℝ) < q).trans located.1)]
      simp only [sub_re, one_re]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) located.1.le (by linarith [etaBelow]))
  rw [abs_of_nonneg (sub_nonneg.mpr lower)] at bound
  have factor : (x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ eta / eta -
      (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta =
      (x : ℂ)⁻¹ * ∫ t : ℝ in q..((N : ℝ) * x), (t : ℂ) ^ (eta - 1) := by
    rw [integral]
    ring
  rw [factor, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ x⁻¹ * (q ^ (eta.re - 1) * ((N : ℝ) * x - q)) :=
      mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr positive.le)
    _ ≤ x⁻¹ * (q ^ (eta.re - 1) * x) := by gcongr
    _ = _ := by field_simp

private theorem power_quadrature (eta : ℂ) (etaPositive : 0 < eta.re) (etaBelow : eta.re < 1)
    (zero : riemannZeta (1 - eta) = 0) (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, (((n : ℝ) * x : ℝ) : ℂ) ^ (eta - 1)) -
      (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta‖ ≤
      (DirichletRate.constant (1 - eta) + 1) * q ^ (eta.re - 1) := by
  let M : ℕ := ⌊q / x⌋₊
  let N : ℕ := M + 1
  have indexPositive : 0 < N := Nat.succ_pos M
  have basePositive : (0 : ℝ) < N := by exact_mod_cast indexPositive
  have lower : q ≤ (N : ℝ) * x := by
    have actual := Nat.lt_floor_add_one (q / x)
    have scaled := (div_lt_iff₀ positive).mp actual
    dsimp only [N, M]
    push_cast
    linarith
  have width : (N : ℝ) * x - q ≤ x := by
    have actual := (le_div_iff₀ positive).mp (Nat.floor_le (by positivity : (0 : ℝ) ≤ q / x))
    dsimp only [N, M]
    push_cast
    linarith
  have counted : (∑ n ∈ Finset.Icc 1 M, (((n : ℝ) * x : ℝ) : ℂ) ^ (eta - 1)) =
      (x : ℂ) ^ (eta - 1) *
        (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-(1 - eta))) := by
    rw [Finset.mul_sum]
    have indices : Finset.Icc 1 M = Finset.Ico 1 N := by simp only [N, Finset.Ico_add_one_right_eq_Icc]
    rw [indices]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) positive.le,
      Complex.ofReal_natCast, neg_sub]
    ring
  have continuousTerm : (x : ℂ) ^ (eta - 1) *
      (N : ℂ) ^ (1 - (1 - eta)) / (1 - (1 - eta)) =
      (x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ eta / eta := by
    rw [sub_sub_cancel, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), cpow_one,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg basePositive.le positive.le, Complex.ofReal_natCast]
    ring
  have decomposition : (∑ n ∈ Finset.Icc 1 M, (((n : ℝ) * x : ℝ) : ℂ) ^ (eta - 1)) -
      (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta =
      (x : ℂ) ^ (eta - 1) * FiniteForcing.coefficient (1 - eta) N +
      ((x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ eta / eta -
        (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta) := by
    rw [counted, ← continuousTerm]
    unfold FiniteForcing.coefficient
    ring
  have arithmetic : ‖(x : ℂ) ^ (eta - 1) * FiniteForcing.coefficient (1 - eta) N‖ ≤
      DirichletRate.constant (1 - eta) * q ^ (eta.re - 1) := by
    have positiveSource : 0 < (1 - eta).re := by simp only [sub_re, one_re]; linarith
    have belowSource : (1 - eta).re < 1 := by simp only [sub_re, one_re]; linarith
    have rate := DirichletRate.coefficient_rate (1 - eta) positiveSource belowSource N indexPositive
    rw [zero, sub_zero] at rate
    simp only [sub_re, one_re, neg_sub] at rate
    have constantNonnegative : 0 ≤ DirichletRate.constant (1 - eta) := by
      have realPart : 0 < (1 - eta).re := by
        simp only [sub_re, one_re]
        linarith [etaBelow]
      unfold DirichletRate.constant
      positivity
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive]
    simp only [sub_re, one_re]
    calc
      _ ≤ x ^ (eta.re - 1) *
          (DirichletRate.constant (1 - eta) * (N : ℝ) ^ (eta.re - 1)) :=
        mul_le_mul_of_nonneg_left rate (Real.rpow_nonneg positive.le _)
      _ = DirichletRate.constant (1 - eta) * (((N : ℝ) * x) ^ (eta.re - 1)) := by
        rw [Real.mul_rpow basePositive.le positive.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by norm_num) lower (by linarith [etaBelow])) constantNonnegative
  change ‖(∑ n ∈ Finset.Icc 1 M, _) - _‖ ≤ _
  rw [decomposition]
  exact (norm_add_le _ _).trans ((add_le_add arithmetic (overflow_bound eta etaPositive etaBelow x positive N lower width)).trans_eq (by ring))


/-- The reversal exponent is used as the exact scalar face 1 - star c, not as a replacement coordinate. -/
theorem singular_quadrature (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, (((n : ℝ) * x : ℝ) : ℂ) ^ (-star coordinate.value)) -
      (x : ℂ)⁻¹ * (q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value)‖ ≤
      (DirichletRate.constant (star coordinate.value) + 1) * q ^ (-coordinate.value.re) := by
  have etaPositive : 0 < (1 - star coordinate.value).re := by
    simp only [sub_re, one_re, star_def, conj_re]
    linarith [coordinate.belowOne]
  have etaBelow : (1 - star coordinate.value).re < 1 := by
    simp only [sub_re, one_re, star_def, conj_re]
    linarith [coordinate.rightHalf]
  have selected : riemannZeta (1 - (1 - star coordinate.value)) = 0 := by
    rw [sub_sub_cancel]
    simpa only [star_def, zero, map_zero] using riemannZeta_conj coordinate.value
  have actual := power_quadrature (1 - star coordinate.value) etaPositive etaBelow selected x positive
  simpa only [show (1 - star coordinate.value) - 1 = -star coordinate.value by ring,
    sub_sub_cancel, sub_re, one_re, star_def, conj_re, sub_sub_cancel_left] using actual

private def compactBound (f : ℝ → ℂ) (regular : Continuous f) : ℝ :=
  max 0 (isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) q) regular.continuousOn).choose

private theorem compactBound_nonnegative (f : ℝ → ℂ) (regular : Continuous f) : 0 ≤ compactBound f regular := le_max_left _ _

private theorem compactBound_spec (f : ℝ → ℂ) (regular : Continuous f) (x : ℝ) (inside : x ∈ Icc 0 q) :
    ‖f x‖ ≤ compactBound f regular :=
  ((isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) q) regular.continuousOn).choose_spec x inside).trans (le_max_right _ _)

def returnBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  compactBound (burnolRieszReturnRaw coordinate) (burnolRieszReturnRaw_continuous coordinate)

def returnSlopeBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  compactBound (burnolRieszReturnRawDerivative coordinate) (burnolRieszReturnRawDerivative_continuous coordinate)

theorem return_bound_nonnegative (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ returnBound coordinate :=
  compactBound_nonnegative _ _

theorem return_slope_nonnegative (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ returnSlopeBound coordinate :=
  compactBound_nonnegative _ _

theorem return_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (inside : x ∈ Icc 0 q) :
    ‖burnolRieszReturnRaw coordinate x‖ ≤ returnBound coordinate := compactBound_spec _ _ x inside

theorem return_slope_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (inside : x ∈ Icc 0 q) :
    ‖burnolRieszReturnRawDerivative coordinate x‖ ≤ returnSlopeBound coordinate := compactBound_spec _ _ x inside

theorem return_lipschitz (coordinate : BurnolCompletedMellinCoordinate) (x y : ℝ)
    (hx : x ∈ Icc 0 q) (hy : y ∈ Icc 0 q) :
    ‖burnolRieszReturnRaw coordinate y - burnolRieszReturnRaw coordinate x‖ ≤ returnSlopeBound coordinate * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (burnolRieszReturnRaw_hasDerivAt coordinate t).hasDerivWithinAt)
    (fun t inside => return_slope_bound coordinate t inside) (convex_Icc _ _) hx hy

theorem return_quadrature (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..q, burnolRieszReturnRaw coordinate t‖ ≤ returnSlopeBound coordinate * q + returnBound coordinate :=
  RegularQuadrature.quadrature_bound _ (burnolRieszReturnRaw_continuous coordinate).continuousOn
    (returnSlopeBound coordinate) (returnBound coordinate) (return_slope_nonnegative coordinate) (return_bound_nonnegative coordinate)
    (fun a ha b hb => return_lipschitz coordinate a b ha hb) (return_bound coordinate) x positive

private theorem position_mean_balance (coordinate : BurnolCompletedMellinCoordinate) :
    (1 / 2 : ℂ) * ((q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value)) -
      (∫ t : ℝ in (0 : ℝ)..q, burnolRieszReturnRaw coordinate t) = (q : ℂ) * GapEuler.gapMean q coordinate := by
  have power : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-star coordinate.value)) volume 0 q :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [neg_re, star_def, conj_re]; linarith [coordinate.belowOne])
  have returned : IntervalIntegrable (burnolRieszReturnRaw coordinate) volume 0 q :=
    (burnolRieszReturnRaw_continuous coordinate).intervalIntegrable _ _
  have actual := PositionSource.positive_mass_zero coordinate
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)] at actual
  unfold positionSource at actual
  rw [intervalIntegral.integral_sub ((power.const_mul _).sub intervalIntegrable_const) returned,
    intervalIntegral.integral_sub (power.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at actual
  have powerRead := integral_cpow_neg_on_burnolGap (star coordinate.value)
    (by simpa only [star_def, conj_re] using coordinate.belowOne)
  change (∫ t : ℝ in Ioc 0 q, (t : ℂ) ^ (-star coordinate.value)) =
    (q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value) at powerRead
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)] at powerRead
  rw [powerRead] at actual
  simp only [sub_zero, Complex.real_smul] at actual
  linear_combination actual

/-- The source bound retains the power remainder, return quadrature and complete constant contact. -/
def bound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  (1 / 2 : ℝ) * (DirichletRate.constant (star coordinate.value) + 1) * q ^ (-coordinate.value.re) +
    (returnSlopeBound coordinate * q + returnBound coordinate) + ‖GapEuler.gapMean q coordinate‖

theorem bound_nonnegative (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ bound coordinate := by
  have positive : 0 < (star coordinate.value).re := by
    simp only [star_def, conj_re]
    linarith [coordinate.rightHalf]
  have slope := return_slope_nonnegative coordinate
  have base := return_bound_nonnegative coordinate
  unfold bound DirichletRate.constant
  positivity

private theorem positive_sum_bound (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (x : ℝ) (positive : 0 < x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, positionSource coordinate ((n : ℝ) * x)‖ ≤ bound coordinate := by
  let M : ℕ := ⌊q / x⌋₊
  let P : ℂ := ∑ n ∈ Finset.Icc 1 M, (((n : ℝ) * x : ℝ) : ℂ) ^ (-star coordinate.value)
  let R : ℂ := ∑ n ∈ Finset.Icc 1 M, burnolRieszReturnRaw coordinate ((n : ℝ) * x)
  let J : ℂ := ∫ t : ℝ in (0 : ℝ)..q, burnolRieszReturnRaw coordinate t
  let G := GapEuler.gapMean q coordinate
  have sourceSum : (∑ n ∈ Finset.Icc 1 M, positionSource coordinate ((n : ℝ) * x)) =
      (1 / 2 : ℂ) * P - (M : ℂ) * G - R := by
    simp only [positionSource, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, P, R, G]
  have decomposition : (∑ n ∈ Finset.Icc 1 M, positionSource coordinate ((n : ℝ) * x)) =
      (1 / 2 : ℂ) * (P - (x : ℂ)⁻¹ * (q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value)) -
      (R - (x : ℂ)⁻¹ * J) - ((M : ℂ) - (q : ℂ) / (x : ℂ)) * G := by
    rw [sourceSum]
    have mean := position_mean_balance coordinate
    change (1 / 2 : ℂ) * ((q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value)) - J = (q : ℂ) * G at mean
    linear_combination (x : ℂ)⁻¹ * mean
  have constantDefect : ‖(M : ℂ) - (q : ℂ) / (x : ℂ)‖ ≤ 1 := by
    have lower := Nat.floor_le (by positivity : (0 : ℝ) ≤ q / x)
    have upper := Nat.lt_floor_add_one (q / x)
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr lower)]
    linarith
  have singular : ‖(1 / 2 : ℂ) * (P - (x : ℂ)⁻¹ * (q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value))‖ ≤
      (1 / 2 : ℝ) * (DirichletRate.constant (star coordinate.value) + 1) * q ^ (-coordinate.value.re) := by
    rw [norm_mul]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (singular_quadrature coordinate zero x positive) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)
  have regular : ‖R - (x : ℂ)⁻¹ * J‖ ≤ returnSlopeBound coordinate * q + returnBound coordinate := return_quadrature coordinate x positive
  have contact : ‖((M : ℂ) - (q : ℂ) / (x : ℂ)) * G‖ ≤ ‖G‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right constantDefect (norm_nonneg G)).trans_eq (one_mul _)
  change ‖∑ n ∈ Finset.Icc 1 M, _‖ ≤ _
  rw [decomposition]
  exact (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans
    ((add_le_add (add_le_add singular regular) contact).trans_eq (by rfl)))

theorem event_bound (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (x : ℝ) : ‖eventRaw coordinate x‖ ≤ bound coordinate := by
  by_cases atZero : x = 0
  · subst x
    simp only [eventRaw, DualSourceRaw.channels, abs_zero, div_zero, Nat.floor_zero,
      Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1), Finset.sum_empty, norm_zero]
    exact bound_nonnegative coordinate
  by_cases outside : q < |x|
  · rw [event_outside coordinate x outside, norm_zero]
    exact bound_nonnegative coordinate
  · exact positive_sum_bound coordinate zero |x| (abs_pos.mpr atZero)

/-- L² is generated only for the completed event after original zeta cancellation. -/
theorem event_memLp_two (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : MemLp (eventRaw coordinate) 2 volume := by
  have dominant : MemLp ((symmetricInterval q).indicator (fun _ : ℝ => (bound coordinate : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval q) _ (Or.inr (by simp [symmetricInterval]))
  apply dominant.mono (event_aestronglyMeasurable coordinate)
  filter_upwards with x
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bound_nonnegative coordinate)]
    exact event_bound coordinate zero x
  · rw [indicator_of_notMem inside, event_outside coordinate x (lt_of_not_ge (fun small => inside (abs_le.mp small))), norm_zero]

/-- The bounded source event supplies the actual ambient result, without promoting any finite input to L². -/
def value (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) : BurnolL2 :=
  (event_memLp_two coordinate zero).toLp (eventRaw coordinate)

theorem value_coeFn (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    (value coordinate zero : ℝ → ℂ) =ᵐ[volume] eventRaw coordinate := (event_memLp_two coordinate zero).coeFn_toLp

theorem value_support (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff q (value coordinate zero) = value coordinate zero := by
  apply OriginalRieszFiniteColumns.cutoff_eq_self_of_ae_zero
  filter_upwards [value_coeFn coordinate zero] with x read outside
  rw [read, event_outside coordinate x (lt_of_not_ge (fun small => outside (abs_le.mp small)))]

theorem event_left_trace (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (eventRaw coordinate) (𝓝[<] q) (𝓝 (-Kernel.A coordinate)) := by
  have source : Tendsto (positionSource coordinate) (𝓝[<] q) (𝓝 (positionSource coordinate q)) :=
    (positionSource_continuousAt coordinate (by norm_num : (0 : ℝ) < q)).tendsto.mono_left nhdsWithin_le_nhds
  rw [OriginalRieszFinitePairing.CoPoisson.Energy.Margin.positionSource_endpoint] at source
  apply source.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : q / 2 < q)] with x inside
  have positive : 0 < x := (by norm_num : (0 : ℝ) < q / 2).trans inside.1
  simpa only [abs_of_pos positive] using
    (event_collar coordinate x (by rw [abs_of_pos positive]; exact inside.1) (by rw [abs_of_pos positive]; exact inside.2.le)).symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
