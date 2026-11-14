import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Rate

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped Topology ENNReal

open private input_equation from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted
open private compensation_bound from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Rate

local notation "q" => (1/4 : ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "R" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "D" => DualSource.source
local notation "decay" => fun n : Nat => ((n+1 : Nat) : ℝ)^(-(1/2 : ℝ))
local notation "ζ" => fun c => riemannZeta (s₀ c)
local notation "Z" => fun c => FiniteForcing.coefficient (s₀ c)
local notation "delta" => fun c (n : Nat) => floorFromResponses c+ζ c • elementarySource c-compensated c (n+2)

private theorem constant_count_tail (n : Nat) :
    ‖ConstantDual.value-D (n+2) ConstantDual.seed‖ ≤ 2*decay n := by
  let M : ℝ := (n+1 : Nat)
  let N : ℝ := (n+2 : Nat)
  let r := q/N
  have mp : 0 < M := by dsimp only [M]; positivity
  have mN : M ≤ N := by dsimp only [M, N]; exact_mod_cast Nat.le_succ (n+1)
  have np := mp.trans_le mN
  have rp : 0 ≤ r := div_nonneg (by norm_num) np.le
  have finite : volume (symmetricInterval r) ≠ ∞ := by
    rw [symmetricInterval, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  let majorant : BurnolL2 := indicatorConstLp 2 (measurableSet_symmetricInterval r) finite (2 : ℂ)
  have compare : ‖ConstantDual.value-D (n+2) ConstantDual.seed‖ ≤ ‖majorant‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub ConstantDual.value (D (n+2) ConstantDual.seed),
      ConstantDual.value_coeFn, ConstantDual.finite_coeFn (n+2),
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_symmetricInterval r) (hμs := finite) (c := (2 : ℂ))]
      with x difference full finiteRead envelope
    change majorant x = _ at envelope
    rw [difference, Pi.sub_apply, full, finiteRead, envelope]
    by_cases member : x ∈ symmetricInterval r
    · rw [indicator_of_mem member, Complex.norm_ofNat]
      exact (norm_sub_le _ _).trans ((add_le_add (ConstantDual.sawtooth_bounds x).1
        (ConstantDual.finite_bounds (n+2) x).1).trans_eq (by norm_num))
    · have outside : r < |x| := lt_of_not_ge (fun h => member (abs_le.mp h))
      have live : 0 < |x| := rp.trans_lt outside
      have covered : q/|x| < N := (div_lt_iff₀ live).mpr (by
        have beat := (div_lt_iff₀ np).mp outside
        rwa [mul_comm] at beat)
      rw [ConstantDual.finite_stabilizes (n+2) x covered, sub_self, indicator_of_notMem member, norm_zero]
  have mass : ‖majorant‖ = 2*(2*r)^(1/2 : ℝ) := by
    dsimp only [majorant]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), Complex.norm_ofNat, measureReal_def,
      symmetricInterval, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    norm_num [show r- -r=2*r by ring]
  have small : 2*r ≤ M⁻¹ := by
    calc
      _ = (1/2 : ℝ)/N := by dsimp only [r]; ring
      _ ≤ 1/N := div_le_div_of_nonneg_right (by norm_num) np.le
      _ ≤ _ := by simpa only [one_div] using one_div_le_one_div_of_le mp mN
  have root : (2*r)^(1/2 : ℝ) ≤ decay n := by
    calc
      _ ≤ (M⁻¹)^(1/2 : ℝ) := Real.rpow_le_rpow (by positivity) small (by norm_num)
      _ = _ := by
        change (M⁻¹)^(1/2 : ℝ) = M^(-(1/2 : ℝ))
        rw [Real.inv_rpow mp.le, Real.rpow_neg mp.le]
  rw [mass] at compare
  exact compare.trans (mul_le_mul_of_nonneg_left root (by norm_num))

private theorem actual_floor_source_tail (c : BurnolCompletedMellinCoordinate) :
    ∃ budget : ℝ, 0 ≤ budget ∧ ∀ n : Nat,
      ‖floorFromResponses c-D (n+2) (OriginalCanonicalNativeEulerGreen.Counted.input c)‖ ≤ budget*decay n := by
  let A := nativeGamma c-originCoefficient c
  let forcing : BurnolL2 := (-(A*((1-s₀ c)/2))) • ConstantDual.seed -
    (1/2 : ℂ) • (nativeBeta c • Response.wholeU-A • Response.wholeV)
  let input := OriginalCanonicalNativeEulerGreen.Counted.input c
  have generated : input = A • ConstantDual.seed+R c forcing := by
    change OriginalCanonicalNativeEulerGreen.Counted.input c = _
    rw [input_equation]
    dsimp only [OriginalCanonicalNativeEulerGreen.Counted.unitFactor, A, forcing]
    simp only [map_sub, map_smul]
    module
  let cost := ‖s₀ c • R c forcing+(2 : ℂ) • forcing‖
  obtain ⟨limit, converges, rate⟩ := CountedJointStrong.actual_resolvent_reverse_tail (barC c) forcing
  have finite (N : Nat) : D N input = A • D N ConstantDual.seed + D N (R c forcing) := by
    simp only [generated, CountingDual.dual_eq_adjoint, map_add, map_smul]
  have source := ((ConstantDual.original_tendsto.const_smul A).add converges).congr'
    (Eventually.of_forall fun N => (finite N).symm)
  have actual : floorFromResponses c = A • ConstantDual.value+limit :=
    tendsto_nhds_unique (actual_floor_tendsto c) source
  refine ⟨2*‖A‖+2*cost, by dsimp only [cost]; positivity, fun n => ?_⟩
  have difference : floorFromResponses c-D (n+2) input =
      A • (ConstantDual.value-D (n+2) ConstantDual.seed)+(limit-D (n+2) (R c forcing)) := by
    rw [actual, finite, smul_sub]
    abel
  have tail := rate (n+1) (by omega)
  change ‖limit-D (n+2) (R c forcing)‖ ≤ (2*decay n)*cost at tail
  rw [difference]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  exact (add_le_add (mul_le_mul_of_nonneg_left (constant_count_tail n) (norm_nonneg A)) tail).trans_eq (by ring)

/-- The same actual counted difference has a full pre-action L² tail budget. -/
theorem actual_counted_source_tail_bound (c : BurnolCompletedMellinCoordinate) :
    ∃ budget : ℝ, 0 ≤ budget ∧ ∀ n : Nat, ‖delta c n‖ ≤ budget*decay n := by
  obtain ⟨floorBudget, nonnegative, floorRate⟩ := actual_floor_source_tail c
  let unitCost := (|cutoffJetBudget c 0|+1/2)*‖elementarySource c‖
  refine ⟨floorBudget+unitCost, by dsimp only [unitCost]; positivity, fun n => ?_⟩
  have difference : delta c n =
      (floorFromResponses c-D (n+2) (OriginalCanonicalNativeEulerGreen.Counted.input c))+
        (ζ c-Z c (n+2)) • elementarySource c := by
    unfold compensated
    rw [sub_smul]
    abel
  have unit : ‖(ζ c-Z c (n+2)) • elementarySource c‖ ≤ unitCost*decay n := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (compensation_bound c n) (norm_nonneg _)).trans_eq (by
      dsimp only [unitCost]
      ring)
  rw [difference]
  exact (norm_add_le _ _).trans ((add_le_add (floorRate n) unit).trans_eq (by ring))

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
