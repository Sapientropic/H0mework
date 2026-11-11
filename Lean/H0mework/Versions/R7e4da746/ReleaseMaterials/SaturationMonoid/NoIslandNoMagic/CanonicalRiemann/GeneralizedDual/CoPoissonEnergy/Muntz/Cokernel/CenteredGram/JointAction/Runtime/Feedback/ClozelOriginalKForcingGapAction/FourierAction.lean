import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Fourier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Gate

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "rho" => burnolQuarterMeanCoefficient (Constructor.compact (Edge.raw q) (Edge.raw_continuous q)) +
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (Response.v : BurnolQuarterIntervalL2))
local notation "mu" => burnolQuarterMeanCoefficient (burnolTruncatedFourier (Response.u : BurnolQuarterIntervalL2))

def sourcePositionCoefficients (coordinate : BurnolCompletedMellinCoordinate) : Fin 2 → ℂ :=
  ![(mu+1)/star coordinate.value,-(rho/star coordinate.value)]

/-- This is a full source subtraction, with only its actual quarter restriction removed. -/
def gapZeroColumns (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  sourceColumns coordinate i-sourcePositionCoefficients coordinate i • ConstantDual.seed

private theorem seed_quarter : burnolQuarterRestriction ConstantDual.seed = (1 : ℂ) • intervalConstant q := by
  change burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) = _
  rw [burnolQuarterRestriction_zeroExtension,one_smul]

theorem sourceColumns_quarter (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    burnolQuarterRestriction (sourceColumns coordinate i) = sourcePositionCoefficients coordinate i • intervalConstant q := by
  fin_cases i
  · exact sourceY0_quarter coordinate
  · exact sourceY1_quarter coordinate

theorem gapZeroColumns_quarter (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    burnolQuarterRestriction (gapZeroColumns coordinate i) = 0 := by
  rw [gapZeroColumns,map_sub,map_smul,sourceColumns_quarter,seed_quarter]
  simp only [smul_smul,mul_one,sub_self]

private theorem reverse_dilation_pair (left right : BurnolL2) (h : ℝ) :
    inner ℂ left (burnolMultiplicativeDilation h right) =
      star (inner ℂ right (burnolMultiplicativeDilation (-h) left)) := by
  have flip := (burnolMultiplicativeDilation h).inner_map_eq_flip right left
  rw [← burnolMultiplicativeDilation_neg_eq_symm h] at flip
  simpa only [Complex.star_def,inner_conj_symm] using (congrArg star flip)

private theorem finitePair_constant_right_zeroQuarter (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (gap : burnolQuarterRestriction value = 0) (h : ℝ) (nonnegative : 0 ≤ h) :
    finitePair coordinate h value ConstantDual.seed = (1/2 : ℂ)*inner ℂ value (outwardConstantShell h) := by
  have qualified : burnolQuarterRestriction value = (0 : ℂ) • intervalConstant q := by rw [zero_smul];exact gap
  have inward := inward_constant_contact value 0 qualified h nonnegative
  simp only [star_zero,mul_zero] at inward
  have stationary := inward_constant_contact value 0 qualified 0 (by norm_num)
  simp only [burnolMultiplicativeDilation_zero,star_zero,mul_zero] at stationary
  simp only [finitePair,inner_add_right,inward,stationary,zero_add,mul_zero,sub_zero,
    outwardConstantShell,inner_sub_right,inner_smul_right]

private theorem finitePair_constant_left_zeroQuarter (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (gap : burnolQuarterRestriction value = 0) (h : ℝ) (nonnegative : 0 ≤ h) :
    finitePair coordinate h ConstantDual.seed value =
      (1/2 : ℂ)*star (inner ℂ value (outwardConstantShell h)) := by
  have qualified : burnolQuarterRestriction value = (0 : ℂ) • intervalConstant q := by rw [zero_smul];exact gap
  have inward := inward_constant_contact value 0 qualified h nonnegative
  simp only [star_zero,mul_zero] at inward
  have stationary := inward_constant_contact value 0 qualified 0 (by norm_num)
  simp only [burnolMultiplicativeDilation_zero,star_zero,mul_zero] at stationary
  have reverseStationary : inner ℂ ConstantDual.seed value = 0 := inner_eq_zero_symm.mp stationary
  have reversePositive := reverse_dilation_pair ConstantDual.seed value h
  have reverseNegative := reverse_dilation_pair ConstantDual.seed value (-h)
  simp only [neg_neg,inward,star_zero] at reverseNegative
  have outward : inner ℂ value (burnolMultiplicativeDilation (-h) ConstantDual.seed) =
      inner ℂ value (outwardConstantShell h) := by
    simp only [outwardConstantShell,inner_sub_right,inner_smul_right,stationary,mul_zero,sub_zero]
  simp only [finitePair,inner_add_right,reversePositive,reverseNegative,reverseStationary,
    outward,add_zero,mul_zero,sub_zero]

private theorem finitePair_constant (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    finitePair coordinate h ConstantDual.seed ConstantDual.seed =
      (Real.exp (-h/2) : ℂ)/2-pairedMellinTranslationCharacter coordinate.value h/2 := by
  have inward := inward_constant_contact _ _ seed_quarter h nonnegative
  simp only [star_one,mul_one] at inward
  have stationary := inward_constant_contact _ _ seed_quarter 0 (by norm_num)
  simp only [neg_zero,zero_div,Real.exp_zero,Complex.ofReal_one,burnolMultiplicativeDilation_zero,star_one,mul_one] at stationary
  have reversed := reverse_dilation_pair ConstantDual.seed ConstantDual.seed (-h)
  simp only [neg_neg,inward] at reversed
  have realScalar : star (Real.exp (-h/2) : ℂ) = (Real.exp (-h/2) : ℂ) := Complex.conj_ofReal _
  simp only [finitePair,inner_add_right,inward,reversed,stationary,star_div₀,star_ofNat,realScalar]
  ring

/-- Both actual Euler/R sources now produce full zero-quarter columns and one retained expanding shell. -/
def calculatedSourceGram (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (i j : Fin 2) : ℂ :=
  finitePair coordinate h (gapZeroColumns coordinate i) (gapZeroColumns coordinate j) +
  (1/2 : ℂ)*sourcePositionCoefficients coordinate j*
    inner ℂ (gapZeroColumns coordinate i) (outwardConstantShell h) +
  (1/2 : ℂ)*star (sourcePositionCoefficients coordinate i)*
    star (inner ℂ (gapZeroColumns coordinate j) (outwardConstantShell h)) +
  star (sourcePositionCoefficients coordinate i)*sourcePositionCoefficients coordinate j*
    ((Real.exp (-h/2) : ℂ)/2-pairedMellinTranslationCharacter coordinate.value h/2)

theorem sourceFiniteGram_calculated_position (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (i j : Fin 2) :
    sourceFiniteGram coordinate h i j = calculatedSourceGram coordinate h i j := by
  have decomposition (k : Fin 2) : sourceColumns coordinate k =
      gapZeroColumns coordinate k+sourcePositionCoefficients coordinate k • ConstantDual.seed := by
    simp only [gapZeroColumns,sub_add_cancel]
  have expanded : sourceFiniteGram coordinate h i j =
      finitePair coordinate h (gapZeroColumns coordinate i) (gapZeroColumns coordinate j) +
      sourcePositionCoefficients coordinate j*finitePair coordinate h (gapZeroColumns coordinate i) ConstantDual.seed +
      star (sourcePositionCoefficients coordinate i)*finitePair coordinate h ConstantDual.seed (gapZeroColumns coordinate j) +
      star (sourcePositionCoefficients coordinate i)*sourcePositionCoefficients coordinate j*
        finitePair coordinate h ConstantDual.seed ConstantDual.seed := by
    change finitePair coordinate h (sourceColumns coordinate i) (sourceColumns coordinate j) = _
    rw [decomposition i,decomposition j]
    simp only [finitePair,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      starRingEnd_apply]
    ring
  rw [expanded,finitePair_constant_right_zeroQuarter _ _ (gapZeroColumns_quarter coordinate i) h nonnegative,
    finitePair_constant_left_zeroQuarter _ _ (gapZeroColumns_quarter coordinate j) h nonnegative,
    finitePair_constant coordinate h nonnegative]
  unfold calculatedSourceGram
  ring

theorem sourceGramForcing_calculated_position (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (i j : Fin 2) :
    sourceGramForcing coordinate h i j =
      (star (sourceRate coordinate)+sourceRate coordinate)*calculatedSourceGram coordinate h i j := by
  rw [← sourceFiniteGram_source_action,sourceFiniteGram_calculated_position coordinate h nonnegative]

private theorem weighted_forcing_calculated_position (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    (star (sourceRate coordinate)+sourceRate coordinate)⁻¹ *
      (∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
        sourceGramForcing coordinate h i j) =
    ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
      calculatedSourceGram coordinate h i j := by
  have calculated :
      (∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
        sourceGramForcing coordinate h i j) =
      (star (sourceRate coordinate)+sourceRate coordinate)*
        ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
          calculatedSourceGram coordinate h i j := by
    simp only [Fin.sum_univ_two]
    rw [sourceGramForcing_calculated_position coordinate h nonnegative 0 0,
      sourceGramForcing_calculated_position coordinate h nonnegative 0 1,
      sourceGramForcing_calculated_position coordinate h nonnegative 1 0,
      sourceGramForcing_calculated_position coordinate h nonnegative 1 1]
    ring
  rw [calculated,← mul_assoc,inv_mul_cancel₀ (sourceRate_sum_ne_zero coordinate),one_mul]

private theorem original_shift_nonnegative : 0 ≤ Real.log stageZeroSonineQ := by
  apply Real.log_nonneg
  change 1 ≤ Real.sqrt 3
  exact Real.one_le_sqrt.mpr (by norm_num)

/-- The original source coefficients combine complete gap-zero vectors, before any physical projection. -/
def gapZeroPart (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∑ i : Fin 2, sourceCoefficients coordinate i • gapZeroColumns coordinate i

theorem generatedK_gap_decomposition (coordinate : BurnolCompletedMellinCoordinate) :
    generatedK coordinate = gapZeroPart coordinate +
      (∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i) • ConstantDual.seed := by
  unfold generatedK gapZeroPart
  simp only [Fin.sum_univ_two,sourceCoefficients,gapZeroColumns,sourceColumns,Matrix.cons_val_zero,Matrix.cons_val_one]
  module

private theorem gapZeroPart_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (gapZeroPart coordinate) = 0 := by
  simp only [gapZeroPart,map_sum,map_smul,gapZeroColumns_quarter,smul_zero,Finset.sum_const_zero]

/-- The energy is the genuine full L² Pythagorean decomposition; no physical Q margin is inferred. -/
theorem generatedK_gap_energy (coordinate : BurnolCompletedMellinCoordinate) :
    ‖generatedK coordinate‖^2 = ‖gapZeroPart coordinate‖^2 +
      ‖∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i‖^2/2 := by
  have contact : inner ℂ ConstantDual.seed (gapZeroPart coordinate) = 0 := by
    have paired : inner ℂ ConstantDual.seed (gapZeroPart coordinate) =
        inner ℂ (intervalConstant q) (burnolQuarterRestriction (gapZeroPart coordinate)) :=
      ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _
    rw [paired,gapZeroPart_quarter,inner_zero_right]
  have reverseContact := inner_eq_zero_symm.mp contact
  have orthogonal : inner ℂ (gapZeroPart coordinate)
      ((∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i) • ConstantDual.seed) = 0 := by
    rw [inner_smul_right,reverseContact,mul_zero]
  have seedInner := inward_constant_contact _ _ seed_quarter 0 (by norm_num)
  simp only [neg_zero,zero_div,Real.exp_zero,Complex.ofReal_one,burnolMultiplicativeDilation_zero,star_one,mul_one] at seedInner
  have seedNorm : ‖ConstantDual.seed‖^2 = (1/2 : ℝ) := by
    calc
      ‖ConstantDual.seed‖^2 = (inner ℂ ConstantDual.seed ConstantDual.seed).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) ConstantDual.seed).symm
      _ = 1/2 := by rw [seedInner];norm_num
  have split := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ orthogonal
  simp only [← pow_two] at split
  rw [generatedK_gap_decomposition,split,norm_smul,mul_pow,seedNorm]
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (rightHalf : 1/2<observation.coordinate.re)
local notation "c" => originalKCoordinate observation.coordinate
 (And.right (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial)) rightHalf

/-- The installed original source receipt actually consumes the generated full-L² energy. -/
theorem installed_kernel_gap_energy :
    ‖(installedOriginalKReceiptAt observation nontrivial rightHalf).kernel‖^2 = ‖gapZeroPart c‖^2 +
      ‖∑ i : Fin 2,sourceCoefficients c i*sourcePositionCoefficients c i‖^2/2 := by
  have sourceAnchor := installedOriginalKReceiptAt_eq_source observation nontrivial rightHalf
  have kernel : (installedOriginalKReceiptAt observation nontrivial rightHalf).kernel = generatedK c :=
    (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel) sourceAnchor).trans
      (generatedK_eq_original c).symm
  rw [kernel]
  exact generatedK_gap_energy c

/-- The actual residual consumes both source-generated gap laws and the full original forcing action. -/
theorem installed_residual_calculated_position :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual =
 ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
  calculatedSourceGram c (Real.log stageZeroSonineQ) i j := by
  rw [installed_fixedResidual_from_source_forcing]
  exact weighted_forcing_calculated_position c _ original_shift_nonnegative

theorem installed_calculated_position_on_original_evolution :
 let root:=runtimeEffectRoot observation nontrivial
 let visit:=runtimeEffectVisit observation nontrivial
 let registered:=runtimeEffectRootedActive observation nontrivial
 let receipt:=installedOriginalKReceiptAt observation nontrivial rightHalf
 let evolution:=root.canonicalCausalAnswerAndNext (ULift.up visit)
 HEq (evolution.generated,
       evolution.generated.projectionOutcome (runtimeEffectRecognition observation nontrivial).rootEffectProjection,
       evolution.nextCurrent,receipt.kernel,receipt.fixedResidual)
     (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit,
       registered.installedFiber,root.generatedNextCurrentAt visit,
       gapZeroPart c+(∑ i : Fin 2,sourceCoefficients c i*sourcePositionCoefficients c i) • ConstantDual.seed,
       ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
        calculatedSourceGram c (Real.log stageZeroSonineQ) i j) := by
  have actual := installed_source_action_on_original_evolution observation nontrivial rightHalf
  rw [weighted_forcing_calculated_position c _ original_shift_nonnegative,generatedK_gap_decomposition c] at actual
  exact actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
