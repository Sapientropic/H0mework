import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKExteriorCoPoissonAction OriginalKSourceResolventReconstruction
open scoped InnerProductSpace Topology
local notation "q" => (1/4 : ℝ)

private def Rbar (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)

private theorem Rbar_apply (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    Rbar c value = sourceResolvent c value := rfl

/-- The whole source is generated from the original constant and its actual Rbar response. -/
def unitResolventSource (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  (star c.value * GapEuler.gapMean q c) •
    (value - ((1-star c.value)/2) • sourceResolvent c value)

private theorem constant_euler_source :
    GapEuler.euler (ConstantDual.seed : TemperedDistribution ℝ ℂ) +
      (1/2 : ℂ) • (ConstantDual.seed : TemperedDistribution ℝ ℂ) = -GapEuler.edge q := by
  ext test
  have source := ConstantDual.seed_edge test
  rw [ConstantDual.edgeRead_apply] at source
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply]
  linear_combination -source

/-- Original gap-tail and the actual inverse generate this full L2 identity before counting. -/
theorem elementary_unit_resolvent (c : BurnolCompletedMellinCoordinate) :
    unitResolventSource c ConstantDual.seed = elementarySource c := by
  have gap := GapEuler.even_gapTail_euler q (by norm_num) c
  change GapEuler.euler (elementarySource c : TemperedDistribution ℝ ℂ) +
    (star c.value-1/2) • (elementarySource c : TemperedDistribution ℝ ℂ) =
      (-star c.value * GapEuler.gapMean q c) • GapEuler.edge q at gap
  have seed := constant_euler_source
  have inverse := sourceResolvent_euler c ConstantDual.seed
  have ratePositive : 0 < (sourceRate c).re := by
    simp only [sourceRate, sub_re, star_def, conj_re]
    norm_num
    linarith [c.rightHalf]
  have homogeneous : GapEuler.euler ((unitResolventSource c ConstantDual.seed - elementarySource c : BurnolL2) :
      TemperedDistribution ℝ ℂ) + sourceRate c •
      ((unitResolventSource c ConstantDual.seed - elementarySource c : BurnolL2) : TemperedDistribution ℝ ℂ) = 0 := by
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (unitResolventSource c ConstantDual.seed - elementarySource c)) + sourceRate c •
      Lp.toTemperedDistributionCLM ℂ volume 2 (unitResolventSource c ConstantDual.seed - elementarySource c) = 0
    simp only [unitResolventSource, map_sub, map_smul,
      Lp.toTemperedDistributionCLM_apply]
    unfold sourceRate at inverse ⊢
    linear_combination (norm := module)
      (star c.value * GapEuler.gapMean q c) • seed -
      (star c.value * GapEuler.gapMean q c * ((1-star c.value)/2)) • inverse - gap
  exact sub_eq_zero.mp (homogeneous_L2_unique (sourceRate c) ratePositive _ homogeneous)

private theorem reverse_resolvent (N : ℕ) (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    DualSource.source N (sourceResolvent c value) =
      sourceResolvent c (DualSource.source N value) := by
  have channel (radius : ℝ) : ContinuousChannels.channel 1 radius (Rbar c value) =
      Rbar c (ContinuousChannels.channel 1 radius value) := by
    simp only [ContinuousChannels.channel, map_smul]
    change (Real.sqrt radius : ℂ)⁻¹ • burnolMultiplicativeDilation (1*Real.log radius)
      (burnolDirectRightResolvent (star c.value/2) value) =
        (Real.sqrt radius : ℂ)⁻¹ • burnolDirectRightResolvent (star c.value/2)
          (burnolMultiplicativeDilation (1*Real.log radius) value)
    rw [burnolDirectRightResolvent_dilation]
  change DualSource.source N (Rbar c value) = Rbar c (DualSource.source N value)
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub, map_sum]
  congr 1
  exact (Rbar c).integral_comp_comm (ContinuousChannels.channel_integrable 1 N value)

theorem unit_resolvent_finite (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    DualSource.source N (elementarySource c) =
      unitResolventSource c (DualSource.source N ConstantDual.seed) := by
  rw [←elementary_unit_resolvent c, unitResolventSource, CountingDual.dual_eq_adjoint,
    map_smul, map_sub, map_smul]
  simp only [←CountingDual.dual_eq_adjoint]
  rw [reverse_resolvent]
  rfl

private theorem unit_source_continuous (c : BurnolCompletedMellinCoordinate) :
    Continuous (unitResolventSource c) := by
  have expression : unitResolventSource c = fun value =>
      (star c.value * GapEuler.gapMean q c) •
        (value - ((1-star c.value)/2) • Rbar c value) := rfl
  rw [expression]
  fun_prop

/-- The zero-owned compact arithmetic vector is now one source-generated unit resolvent field. -/
theorem elementary_reverse_unit_resolvent (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    elementaryReverseSource c zero = unitResolventSource c ConstantDual.value := by
  have generated := ((unit_source_continuous c).tendsto ConstantDual.value).comp ConstantDual.original_tendsto
  have actual := generated.congr' (Eventually.of_forall (fun N => (unit_resolvent_finite c N).symm))
  exact tendsto_nhds_unique (elementary_reverse_tendsto c zero) actual

/-- No mean is removed: the whole unit and the whole Rbar source are both read. -/
theorem elementary_reverse_actual_mean (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (elementaryReverseSource c zero)) =
      (star c.value * GapEuler.gapMean q c) *
        (burnolQuarterMeanCoefficient (burnolQuarterRestriction ConstantDual.value) -
          ((1-star c.value)/2) *
            burnolQuarterMeanCoefficient (burnolQuarterRestriction (sourceResolvent c ConstantDual.value))) := by
  rw [elementary_reverse_unit_resolvent, unitResolventSource, map_smul, map_sub, map_smul]
  unfold burnolQuarterMeanCoefficient
  simp only [inner_smul_right, inner_sub_right]
  ring

/-- The original core now consumes the computed unit field in its entire arithmetic effect. -/
def coreUnitResolventSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (unitResolventSource c ConstantDual.value) - (1/2 : ℂ) •
    (FullUnit.fullReverse c h 1 - fourierL2 (FullUnit.fullForward c h 0))

theorem core_reverse_unit_resolvent (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) :
    coreReverseSource c zero h = coreUnitResolventSource c h := by
  rw [coreReverseSource, elementary_reverse_unit_resolvent]
  rfl

theorem actual_core_unit_resolvent_action (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) :
    Tendsto (fun N : ℕ => DualSource.source N (sourceCore c h)) atTop
      (𝓝 (coreUnitResolventSource c h)) := by
  rw [←core_reverse_unit_resolvent c zero h]
  exact core_reverse_tendsto c zero h nonnegative

theorem original_core_unit_resolvent_ward (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (KCountingGram.value c) (sourceCore c h) =
      inner ℂ (sourceKernel c) (coreUnitResolventSource c h) := by
  rw [←core_reverse_unit_resolvent c zero h]
  exact original_core_arithmetic_ward c zero h nonnegative

end OriginalKElementaryArithmeticAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
