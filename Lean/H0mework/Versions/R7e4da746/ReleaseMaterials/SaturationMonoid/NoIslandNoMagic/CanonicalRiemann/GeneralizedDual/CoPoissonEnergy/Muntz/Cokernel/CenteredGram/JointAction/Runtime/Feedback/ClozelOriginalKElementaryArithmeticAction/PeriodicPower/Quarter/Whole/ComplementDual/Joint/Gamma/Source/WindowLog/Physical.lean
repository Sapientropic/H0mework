import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Graph
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaIterated.Kernel
import H0mework.Versions.R7e4da746.Arithmetic.RieszCanonicalRaw.RieszCanonicalRaw

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WindowLog

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorStrong
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.ConductorDual
open OriginalGamma.Source.KGamma OriginalGamma.Source.KGamma.Iterated
open private seedFourierLog from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

local notation "q" => (1/4 : ℝ)
local notation "F" => fourierL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "MZ" => burnolQuarterMeanZeroProjection
local notation "μ" => burnolQuarterMeanCoefficient
local notation "C" => ConstantDual.seed
local notation "Ev" => burnolAmbientEvenPart
local notation "KLog" => logSeedSynthesis C

private def positionCut (v : BurnolL2) : BurnolL2 := E (R v)

private theorem position_cut_raw (v : BurnolL2) :
    (positionCut v : ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator (v : ℝ → ℂ) := by
  have restricted : (R v : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)] (v : ℝ → ℂ) :=
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) v
  have read := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp restricted
  filter_upwards [burnolQuarterZeroExtension_coe (R v), read] with x cut raw
  change E (R v) x = _
  rw [cut]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, raw inside]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private theorem position_cut_log_pair (v logged : BurnolL2) (source : LogPair v logged) :
    LogPair (positionCut v) (positionCut logged) := by
  filter_upwards [position_cut_raw v, position_cut_raw logged, source] with x value logRead read
  rw [value, logRead]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, read]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside, mul_zero]

private theorem fourier_cut_log_pair (v logged : BurnolL2) (source : LogPair (F v) logged) :
    LogPair (F (positionCut v)) (quarterFourierCutLog (F v) logged) := by
  simpa only [quarterFourierCut_apply, LinearIsometryEquiv.symm_apply_apply, positionCut] using
    quarter_fourier_cut_log_pair (F v) logged source

private def centeredCut (v : BurnolL2) : BurnolL2 := E (MZ (R v))

private theorem centered_cut_eq (v : BurnolL2) :
    centeredCut v = positionCut v - μ (R v) • C := by
  change E (MZ (R v)) = E (R v) - μ (R v) • E (intervalConstant q)
  rw [burnolMeanZeroProjection_eq_sub_constant, map_sub, map_smul]

private def centeredPositionLog (v logged : BurnolL2) : BurnolL2 :=
  positionCut logged - μ (R v) • KLog

private def centeredFourierLog (v logged : BurnolL2) : BurnolL2 :=
  quarterFourierCutLog (F v) logged - μ (R v) • seedFourierLog

private theorem centered_position_log_pair (v logged : BurnolL2) (source : LogPair v logged) :
    LogPair (centeredCut v) (centeredPositionLog v logged) := by
  rw [centered_cut_eq]
  exact (dualFourierPaid% logPair_sub) _ _ _ _ (position_cut_log_pair _ _ source)
    ((dualFourierPaid% logPair_smul) _ _ _ (kGammaSeedPaid% seed_log_domain))

private theorem centered_fourier_log_pair (v logged : BurnolL2) (source : LogPair (F v) logged) :
    LogPair (F (centeredCut v)) (centeredFourierLog v logged) := by
  rw [centered_cut_eq, map_sub, map_smul]
  exact (dualFourierPaid% logPair_sub) _ _ _ _ (fourier_cut_log_pair _ _ source)
    ((dualFourierPaid% logPair_smul) _ _ _ (kGammaFourierPaid% seed_fourier_log_pair))

private theorem compact_fourier_cut_log_domain (state : BurnolQuarterIntervalL2) :
    MemLp (fun x : ℝ => (Real.log (|x|) : ℂ) * positionCut (F (E state)) x) 2 volume := by
  let c := Real.sqrt (2*q) * ‖state‖
  apply (Lp.memLp KLog).of_le_mul (c := c)
    ((by fun_prop : Measurable (fun x : ℝ => (Real.log (|x|) : ℂ))).mul
      (Lp.stronglyMeasurable (positionCut (F (E state)))).measurable).aestronglyMeasurable
  filter_upwards [position_cut_raw (F (E state)), burnolRadiusFourierL2_zeroExtension_ae_eq_raw state,
    (kGammaSeedPaid% seed_log_domain), ConstantDual.seed_coeFn] with x cut frequency logged seed
  change ‖(Real.log (|x|) : ℂ) * positionCut (F (E state)) x‖ ≤ c * ‖KLog x‖
  have frequencyRead : F (E state) x = burnolRadiusTruncatedFourierRaw q state x := frequency
  by_cases inside : x ∈ symmetricInterval q
  · have location : |x| ≤ q := abs_le.mpr inside
    rw [cut, indicator_of_mem inside, frequencyRead, logged, seed, ConstantDual.seedRaw,
      if_pos location, mul_one, norm_mul, mul_comm c]
    exact mul_le_mul_of_nonneg_left
      (burnolRadiusTruncatedFourierRaw_norm_le (by norm_num : (0 : ℝ) < q) state x) (norm_nonneg _)
  · rw [cut, indicator_of_notMem inside, mul_zero, norm_zero]
    exact mul_nonneg (by dsimp [c]; positivity) (norm_nonneg _)

private def compactCenteredPositionLog (state : BurnolQuarterIntervalL2) : BurnolL2 :=
  (compact_fourier_cut_log_domain state).toLp _ - μ (R (F (E state))) • KLog

private theorem compact_centered_position_log_pair (state : BurnolQuarterIntervalL2) :
    LogPair (centeredCut (F (E state))) (compactCenteredPositionLog state) := by
  rw [centered_cut_eq]
  exact (dualFourierPaid% logPair_sub) _ _ _ _ (compact_fourier_cut_log_domain state).coeFn_toLp
    ((dualFourierPaid% logPair_smul) _ _ _ (kGammaSeedPaid% seed_log_domain))

private theorem even_position_log_pair (v logged : BurnolL2) (source : LogPair v logged) :
    LogPair (Ev v) (Ev logged) :=
  (dualFourierPaid% logPair_smul) (1/2 : ℂ) _ _
    ((kGammaDualPaid% log_pair_add) _ _ _ _ source ((kGammaDualPaid% log_pair_reflect) _ _ source))

private theorem even_fourier_log_pair (v logged : BurnolL2) (source : LogPair (F v) logged) :
    LogPair (F (Ev v)) (Ev logged) := by
  have identity : F (Ev v) = Ev (F v) := by
    simp only [burnolAmbientEvenPart, map_smul, map_add, fourierL2_reflectL2_commute]
  rw [identity]
  exact even_position_log_pair _ _ source

private theorem double_fourier_log_pair (v logged : BurnolL2) (source : LogPair v logged) :
    LogPair (F (F v)) (reflectL2 logged) := by
  rw [fourierL2_fourierL2]
  exact (kGammaDualPaid% log_pair_reflect) _ _ source

private def firstLift (v : BurnolL2) : BurnolL2 :=
  E (burnolAmbientMeanZeroFirstCorrection v : BurnolQuarterIntervalL2)

private def secondLift (v : BurnolL2) : BurnolL2 :=
  E (burnolAmbientMeanZeroSecondCorrection v : BurnolQuarterIntervalL2)

private theorem correction_equations (v : BurnolL2) :
    firstLift v = centeredCut (Ev v) - centeredCut (F (secondLift v)) ∧
    secondLift v = centeredCut (F (Ev v)) - centeredCut (F (firstLift v)) := by
  have first := congrArg (fun z : BurnolQuarterMeanZeroCarrier => (z : BurnolQuarterIntervalL2))
    (burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs v))
  have second := congrArg (fun z : BurnolQuarterMeanZeroCarrier => (z : BurnolQuarterIntervalL2))
    (burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs v))
  change (burnolAmbientMeanZeroFirstCorrection v : BurnolQuarterIntervalL2) +
    (burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroSecondCorrection v) :
      BurnolQuarterIntervalL2) = MZ (R (Ev v)) at first
  change (burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection v) :
      BurnolQuarterIntervalL2) + (burnolAmbientMeanZeroSecondCorrection v :
      BurnolQuarterIntervalL2) = MZ (R (F (Ev v))) at second
  rw [burnolMeanZeroTruncatedFourier_coe] at first second
  have firstRead := congrArg (fun z : BurnolQuarterIntervalL2 => E z) first
  have secondRead := congrArg (fun z : BurnolQuarterIntervalL2 => E z) second
  rw [map_add] at firstRead secondRead
  change firstLift v + centeredCut (F (secondLift v)) = centeredCut (Ev v) at firstRead
  change centeredCut (F (firstLift v)) + secondLift v = centeredCut (F (Ev v)) at secondRead
  exact ⟨eq_sub_of_add_eq firstRead, eq_sub_of_add_eq (by rwa [add_comm] at secondRead)⟩

private def firstPositionLog (v p : BurnolL2) : BurnolL2 :=
  centeredPositionLog (Ev v) (Ev p) -
    compactCenteredPositionLog (burnolAmbientMeanZeroSecondCorrection v)

private def secondPositionLog (v f : BurnolL2) : BurnolL2 :=
  centeredPositionLog (F (Ev v)) (Ev f) -
    compactCenteredPositionLog (burnolAmbientMeanZeroFirstCorrection v)

private def firstFourierLog (v f : BurnolL2) : BurnolL2 :=
  centeredFourierLog (Ev v) (Ev f) -
    centeredFourierLog (F (secondLift v)) (reflectL2 (secondPositionLog v f))

private def secondFourierLog (v p : BurnolL2) : BurnolL2 :=
  centeredFourierLog (F (Ev v)) (reflectL2 (Ev p)) -
    centeredFourierLog (F (firstLift v)) (reflectL2 (firstPositionLog v p))

private theorem first_position_log_pair (v p : BurnolL2) (hp : LogPair v p) :
    LogPair (firstLift v) (firstPositionLog v p) := by
  rw [(correction_equations v).1]
  exact (dualFourierPaid% logPair_sub) _ _ _ _
    (centered_position_log_pair _ _ (even_position_log_pair v p hp))
    (compact_centered_position_log_pair (burnolAmbientMeanZeroSecondCorrection v))

private theorem second_position_log_pair (v f : BurnolL2) (hf : LogPair (F v) f) :
    LogPair (secondLift v) (secondPositionLog v f) := by
  rw [(correction_equations v).2]
  exact (dualFourierPaid% logPair_sub) _ _ _ _
    (centered_position_log_pair _ _ (even_fourier_log_pair v f hf))
    (compact_centered_position_log_pair (burnolAmbientMeanZeroFirstCorrection v))

private theorem first_fourier_log_pair (v f : BurnolL2) (hf : LogPair (F v) f) :
    LogPair (F (firstLift v)) (firstFourierLog v f) := by
  rw [(correction_equations v).1, map_sub]
  exact (dualFourierPaid% logPair_sub) _ _ _ _
    (centered_fourier_log_pair _ _ (even_fourier_log_pair v f hf))
    (centered_fourier_log_pair _ _ (double_fourier_log_pair _ _ (second_position_log_pair v f hf)))

private theorem second_fourier_log_pair (v p : BurnolL2) (hp : LogPair v p) :
    LogPair (F (secondLift v)) (secondFourierLog v p) := by
  rw [(correction_equations v).2, map_sub]
  exact (dualFourierPaid% logPair_sub) _ _ _ _
    (centered_fourier_log_pair _ _ (double_fourier_log_pair _ _ (even_position_log_pair v p hp)))
    (centered_fourier_log_pair _ _ (double_fourier_log_pair _ _ (first_position_log_pair v p hp)))

def physicalProjectionPositionLog (v p : BurnolL2) : BurnolL2 :=
  Ev p - Ev (firstPositionLog v p + secondFourierLog v p)

def physicalProjectionFourierLog (v f : BurnolL2) : BurnolL2 :=
  Ev f - Ev (firstFourierLog v f + reflectL2 (secondPositionLog v f))

/-- The original projection's two block solves preserve both logarithmic graph values. -/
theorem actual_physical_projection_log_pairs (v p f : BurnolL2)
    (hp : LogPair v p) (hf : LogPair (F v) f) :
    LogPair (evenBurnolPhysicalProjection q v) (physicalProjectionPositionLog v p) ∧
      LogPair (F (evenBurnolPhysicalProjection q v)) (physicalProjectionFourierLog v f) := by
  have projection : evenBurnolPhysicalProjection q v = Ev v - Ev (firstLift v + F (secondLift v)) :=
    burnolEvenOrthogonalProjection_eq_resolventFormula v
  rw [projection, map_sub]
  have position := (kGammaDualPaid% log_pair_add) _ _ _ _
    (first_position_log_pair v p hp) (second_fourier_log_pair v p hp)
  have frequency : LogPair (F (firstLift v + F (secondLift v)))
      (firstFourierLog v f + reflectL2 (secondPositionLog v f)) := by
    rw [map_add]
    exact (kGammaDualPaid% log_pair_add) _ _ _ _ (first_fourier_log_pair v f hf)
      (double_fourier_log_pair _ _ (second_position_log_pair v f hf))
  exact ⟨(dualFourierPaid% logPair_sub) _ _ _ _ (even_position_log_pair v p hp)
      (even_position_log_pair _ _ position),
    (dualFourierPaid% logPair_sub) _ _ _ _ (even_fourier_log_pair v f hf)
      (even_fourier_log_pair _ _ frequency)⟩

def actualProjectedGammaAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  physicalProjectionPositionLog (actualGammaKernel c) (actualGammaKernelPositionLog c) +
    F (reflectL2 (physicalProjectionFourierLog (actualGammaKernel c)
      (reflectL2 (actualGammaKernelFrequencyLog c))))

theorem actual_projected_gamma_action (c : BurnolCompletedMellinCoordinate) :
    GammaPair (evenBurnolPhysicalProjection q (actualGammaKernel c)) (actualProjectedGammaAction c) := by
  obtain ⟨position, inverse⟩ := actual_gamma_kernel_complete_log_sources c
  have frequency := (kGammaDualPaid% log_pair_reflect) _ _ inverse
  rw [fourierL2_symm_eq_reflect_fourierL2, reflectL2_reflectL2] at frequency
  obtain ⟨projectedPosition, projectedFrequency⟩ := actual_physical_projection_log_pairs
    _ _ _ position frequency
  have projectedInverse := (kGammaDualPaid% log_pair_reflect) _ _ projectedFrequency
  rw [← fourierL2_symm_eq_reflect_fourierL2] at projectedInverse
  exact gamma_pair_of_log_pairs _ _ _ projectedPosition projectedInverse

end OriginalGamma.Source.WindowLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
