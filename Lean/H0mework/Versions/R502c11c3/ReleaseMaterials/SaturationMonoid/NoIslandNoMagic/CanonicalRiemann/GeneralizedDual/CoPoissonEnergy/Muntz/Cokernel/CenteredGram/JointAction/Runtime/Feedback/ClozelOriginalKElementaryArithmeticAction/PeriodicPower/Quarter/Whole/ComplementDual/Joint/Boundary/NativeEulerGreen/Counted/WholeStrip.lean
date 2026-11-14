import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.Fixed

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward (actual_log_return_count_field)
open scoped Topology

local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "D" => DualSource.source
local notation "lead" => ForcingPrimitive.leadingCoefficient

/-- The complete base retains the actual Unit and return before assuming a zero. -/
def baseLimit (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  freeUnit (star c.value) ConstantDual.value + ReturnCounting.value c

theorem actual_base_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (KCountingSource.finite c) atTop (𝓝 (baseLimit c)) := by
  have count := (original_reverse_free_limit c).add (ReturnCounting.finite_tendsto c)
  apply count.congr'
  filter_upwards with N
  rw [elementary_reverse_finite, sub_add_cancel]

theorem actual_floor_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N => D N (input c)) atTop (𝓝 (floorFromResponses c)) := by
  let R := burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
  let A := nativeGamma c-originCoefficient c
  have count := ConstantDual.original_tendsto
  have acted := (R.continuous.tendsto ConstantDual.value).comp count
  have unit := count.sub (acted.const_smul ((1-star c.value)/2))
  have drive := ((ResponseCounting.finite_tendsto false).const_smul (nativeBeta c)).sub
    ((ResponseCounting.finite_tendsto true).const_smul A)
  have response := (R.continuous.tendsto _).comp drive
  have complete := (unit.const_smul A).sub (response.const_smul (1/2 : ℂ))
  apply complete.congr'
  filter_upwards with N
  exact (actual_finite_floor_action c N).symm

/-- Both limits execute the same normalized count on the actual input. -/
theorem actual_floor_base (c : BurnolCompletedMellinCoordinate) :
    floorFromResponses c = lead c • poissonPair (logProgramme c) - baseLimit c := by
  have source : input c = lead c • E (S (logBFirst c 0) : Hq) -
      E (S (burnolRieszSingleFourierSource c) : Hq) - elementarySource c := by
    simp only [input, nativeSmooth, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul]
  have complete := ((actual_log_return_reverse c).const_smul (lead c)).sub (actual_base_tendsto c)
  apply tendsto_nhds_unique (actual_floor_tendsto c)
  apply complete.congr'
  filter_upwards with N
  have linear : D N (input c) = lead c • D N (E (S (logBFirst c 0) : Hq)) -
      ReturnCounting.finite c N - D N (elementarySource c) := by
    simp only [source, ReturnCounting.finite, Constructor.returnState, CountingDual.dual_eq_adjoint,
      map_sub, map_smul]
  rw [linear, elementary_reverse_finite]
  module

private def homogeneous (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) ^ (-star c.value)

private theorem zeta_star (c : BurnolCompletedMellinCoordinate) :
    riemannZeta (star c.value) = star (riemannZeta c.value) := by
  simpa only [star_def] using riemannZeta_conj c.value

private theorem coefficient_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (FiniteForcing.coefficient (star c.value)) atTop (𝓝 (riemannZeta (star c.value))) := by
  have positive : 0 < (star c.value).re := by
    simp only [star_def, conj_re]
    linarith [c.rightHalf]
  have below : (star c.value).re < 1 := by simpa only [star_def, conj_re] using c.belowOne
  exact DirichletCoefficient.coefficient_tendsto_riemannZeta _ positive (fun one => by simp [one] at below)

/-- The complete L² count has precisely the homogeneous term of its raw integer-minus-continuous action. -/
theorem actual_base_raw (c : BurnolCompletedMellinCoordinate) :
    (baseLimit c : ℝ → ℂ) =ᵐ[volume] fun x =>
      (1/2 : ℂ)*homogeneous c x*riemannZeta (star c.value) - PositionCounting.eventRaw c x := by
  obtain ⟨index, strict, converges⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (actual_base_tendsto c)).exists_seq_tendsto_ae
  have raw : ∀ᵐ x ∂volume, ∀ N : ℕ, KCountingSource.finite c N x = KCountingSource.raw c N x :=
    ae_all_iff.mpr (KCountingSource.finite_coeFn c)
  filter_upwards [converges, raw, volume.ae_ne (0 : ℝ)] with x same read nonzero
  have arithmetic := (coefficient_limit c).const_mul ((1/2 : ℂ)*homogeneous c x)
  have stable : Tendsto (fun N => PositionCounting.raw c N x) atTop
      (𝓝 (PositionCounting.eventRaw c x)) :=
    tendsto_const_nhds.congr' ((PositionCounting.raw_eventually c x nonzero).mono (fun _ h => h.symm))
  have point : Tendsto (fun N => KCountingSource.raw c N x) atTop
      (𝓝 ((1/2 : ℂ)*homogeneous c x*riemannZeta (star c.value) - PositionCounting.eventRaw c x)) := by
    apply (arithmetic.sub stable).congr'
    filter_upwards with N
    exact (KCountingSource.raw_synthesis c N x nonzero).symm
  exact tendsto_nhds_unique
    (same.congr' (Eventually.of_forall (fun N => read (index N))))
    (point.comp strict.tendsto_atTop)

theorem actual_floor_raw (c : BurnolCompletedMellinCoordinate) :
    (floorFromResponses c : ℝ → ℂ) =ᵐ[volume] fun x =>
      fullFloorRaw c x - (1/2 : ℂ)*homogeneous c x*riemannZeta (star c.value) := by
  rw [actual_floor_base]
  filter_upwards [Lp.coeFn_sub (lead c • poissonPair (logProgramme c)) (baseLimit c),
    Lp.coeFn_smul (lead c) (poissonPair (logProgramme c)),
    actual_log_return_count_field c, actual_base_raw c] with x difference scalar logRead base
  rw [difference, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, logRead, base,
    actual_counted_position_source]
  change lead c*logReturnFloor c x - _ = _
  ring

theorem actual_floor_exterior (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x ∂volume, q < |x| →
      floorFromResponses c x = -(1/2 : ℂ)*homogeneous c x*riemannZeta (star c.value) := by
  filter_upwards [actual_floor_raw c] with x read outside
  rw [read, fullFloorRaw, actual_floor_outer_zero _ _ _ outside]
  ring

private theorem homogeneous_not_memLp (c : BurnolCompletedMellinCoordinate) :
    ¬ MemLp (homogeneous c) 2 volume := by
  intro source
  have square := (memLp_two_iff_integrable_sq_norm source.aestronglyMeasurable).mp source
  have localSquare : IntegrableOn (fun x : ℝ => ‖homogeneous c x‖ ^ 2) (Ioo 0 q) := square.integrableOn
  have power : IntegrableOn (fun x : ℝ => x ^ (-2 * c.value.re)) (Ioo 0 q) := by
    apply localSquare.congr_fun _ measurableSet_Ioo
    intro x hx
    have positive : 0 < x := hx.1
    change ‖((|x| : ℝ) : ℂ) ^ (-star c.value)‖ ^ 2 = x ^ (-2*c.value.re)
    rw [abs_of_pos positive, Complex.norm_cpow_eq_rpow_re_of_pos positive,
      ← Real.rpow_mul_natCast positive.le]
    congr 1
    simp only [neg_re, star_def, conj_re, Nat.cast_ofNat]
    ring
  have integrable := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : 0 < q)).mp power
  linarith [c.rightHalf]

/-- The original raw floor is L² exactly when its source-generated singular coefficient vanishes. -/
theorem actual_raw_floor_memLp_iff (c : BurnolCompletedMellinCoordinate) :
    MemLp (fullFloorRaw c) 2 volume ↔ riemannZeta c.value = 0 := by
  refine ⟨fun source => ?_, actual_full_floor_memLp c⟩
  by_contra nonzero
  let a : ℂ := riemannZeta (star c.value) / 2
  have live : a ≠ 0 := by
    unfold a
    rw [zeta_star]
    have starred : star (riemannZeta c.value) ≠ 0 := fun gone => nonzero (by
      simpa only [star_star, star_zero] using congrArg star gone)
    exact div_ne_zero starred (by norm_num)
  have tail : MemLp (a • homogeneous c) 2 volume := by
    refine MemLp.ae_eq ?_ (source.sub (Lp.memLp (floorFromResponses c)))
    filter_upwards [actual_floor_raw c] with x actual
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [actual]
    unfold a
    ring
  apply homogeneous_not_memLp c
  simpa only [smul_smul, inv_mul_cancel₀ live, one_smul] using tail.const_smul a⁻¹

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
