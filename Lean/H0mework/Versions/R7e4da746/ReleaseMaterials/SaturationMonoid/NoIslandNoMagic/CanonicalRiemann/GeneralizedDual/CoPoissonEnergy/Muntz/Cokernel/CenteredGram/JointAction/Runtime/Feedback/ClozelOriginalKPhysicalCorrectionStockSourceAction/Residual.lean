import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.Character
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.FeeBound
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalKWholePaSourceRankAction OriginalKExpandedCompleteWindowSourceAction OriginalRieszSource
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "P" => burnolEvenAmbientProjection
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualCorrectionStockPairBoundaryTailFee (h : ℝ) (N : ℕ) : ℂ :=
  (1/2:ℂ)*(Kernel.A c-Kernel.beta c)*actualPairCorrectionTailIntegralFee observation nontrivial half h N

def actualCorrectionStockSiblingBoundaryTailFee (h : ℝ) (N : ℕ) : ℂ :=
  -(1/2:ℂ)*(Kernel.A c+Kernel.beta c)*actualSiblingCorrectionTailIntegralFee observation nontrivial half h N

def actualCorrectionStockQBTailFee (h : ℝ) (N : ℕ) : ℂ :=
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*(2*actualCorrectionStockPairBoundaryTailFee observation nontrivial half h N) +
    star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*star (2*actualCorrectionStockSiblingBoundaryTailFee observation nontrivial half h N)

def actualFinitePairCorrectionCvelPrice (h : ℝ) (N : ℕ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaPairedR observation nontrivial half h)) h +
    (Kernel.A c-Kernel.beta c)*actualPairCorrectionStockIntegralFee observation nontrivial half h N

def actualFiniteSiblingCorrectionCvelPrice (h : ℝ) (N : ℕ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaSiblingR observation nontrivial half h)) h -
    (Kernel.A c+Kernel.beta c)*actualSiblingCorrectionStockIntegralFee observation nontrivial half h N

def actualFiniteCorrectionPairBoundaryProgramme (h : ℝ) (N : ℕ) : ℂ :=
  let test := Q (actualNonPaPairedR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value h-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualFinitePairCorrectionCvelPrice observation nontrivial half h N -
    Kernel.A c*OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h h +
    Kernel.beta c*OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h h

def actualFiniteCorrectionSiblingBoundaryProgramme (h : ℝ) (N : ℕ) : ℂ :=
  let test := Q (actualNonPaSiblingR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value h-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualFiniteSiblingCorrectionCvelPrice observation nontrivial half h N -
    Kernel.A c*OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h h -
    Kernel.beta c*OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h h

def actualFiniteCorrectionQBPrice (h : ℝ) (N : ℕ) : ℂ :=
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*(2*actualFiniteCorrectionPairBoundaryProgramme observation nontrivial half h N) +
    star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*star (2*actualFiniteCorrectionSiblingBoundaryProgramme observation nontrivial half h N)

def actualFiniteCorrectionSourceCharacter (h : ℝ) (N : ℕ) : ℂ :=
  OriginalKNonPaSourceWardAction.actualWholePaUnitCrossPrice observation nontrivial half h +
    actualFiniteCorrectionQBPrice observation nontrivial half h N +
    2*(observation.coordinate/2-1/4)*inner ℂ
      (P (actualNonPaPairedR observation nontrivial half h)) (P (actualNonPaPairedR observation nontrivial half h)) +
    2*star (observation.coordinate/2-1/4)*inner ℂ
      (P (actualNonPaSiblingR observation nontrivial half h)) (P (actualNonPaSiblingR observation nontrivial half h)) +
    2*OriginalKOutsideQuarterSourceAction.actualOutsideQuarterFlux observation nontrivial half h

def actualCorrectionSourceTailBudget (h : ℝ) : ℝ :=
  (2*‖2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h‖)*
    ((1/2:ℝ)*‖Kernel.A c-Kernel.beta c‖*(3/2:ℝ)*
        ‖burnolAmbientMeanZeroFirstCorrection (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)‖*
        ‖actualCoupledQuarterPlus‖*|h| +
      (1/2:ℝ)*‖Kernel.A c+Kernel.beta c‖*(3/2:ℝ)*
        ‖burnolAmbientMeanZeroFirstCorrection (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)‖*
        ‖actualCoupledQuarterMinus‖*|h|)

theorem actual_current_consumes_finite_correction_and_same_tail (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (n N : ℕ) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
    actualFiniteCorrectionSourceCharacter observation nontrivial half h N + actualCorrectionStockQBTailFee observation nontrivial half h N := by
  rw [actual_current_consumes_correction_stock_source observation nontrivial half h nonnegative bounded n N]
  unfold actualCorrectionStockSourceCharacter actualFiniteCorrectionSourceCharacter
    actualCorrectionStockQBPrice actualFiniteCorrectionQBPrice actualCorrectionStockQBTailFee
    actualCorrectionStockPairBoundaryProgramme actualCorrectionStockSiblingBoundaryProgramme
    actualFiniteCorrectionPairBoundaryProgramme actualFiniteCorrectionSiblingBoundaryProgramme
    actualCorrectionStockPairBoundaryTailFee actualCorrectionStockSiblingBoundaryTailFee
    actualPairCorrectionStockCvelPrice actualSiblingCorrectionStockCvelPrice
    actualFinitePairCorrectionCvelPrice actualFiniteSiblingCorrectionCvelPrice
  dsimp only
  simp only [star_add,star_sub,star_mul,star_neg,star_div₀,star_one,star_ofNat]
  ring

theorem actual_correction_source_QB_tail_bound (h : ℝ) (N : ℕ) :
    ‖actualCorrectionStockQBTailFee observation nontrivial half h N‖ ≤
      actualCorrectionSourceTailBudget observation nontrivial half h * (1/4:ℝ)^N := by
  have pair := actual_correction_tail_integral_source_bound
    (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) actualCoupledQuarterPlus h N
  have sibling := actual_correction_tail_integral_source_bound
    (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) actualCoupledQuarterMinus h N
  change ‖actualPairCorrectionTailIntegralFee observation nontrivial half h N‖ ≤ _ at pair
  change ‖actualSiblingCorrectionTailIntegralFee observation nontrivial half h N‖ ≤ _ at sibling
  have normhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  have pairBound : ‖actualCorrectionStockPairBoundaryTailFee observation nontrivial half h N‖ ≤
      (1/2:ℝ)*‖Kernel.A c-Kernel.beta c‖ *
        (((3/2:ℝ)*((1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)‖))*‖actualCoupledQuarterPlus‖)*|h| := by
    unfold actualCorrectionStockPairBoundaryTailFee
    rw [norm_mul,norm_mul,normhalf]
    exact (mul_le_mul_of_nonneg_left pair (mul_nonneg (by norm_num) (norm_nonneg _))).trans_eq (by ring)
  have siblingBound : ‖actualCorrectionStockSiblingBoundaryTailFee observation nontrivial half h N‖ ≤
      (1/2:ℝ)*‖Kernel.A c+Kernel.beta c‖ *
        (((3/2:ℝ)*((1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)‖))*‖actualCoupledQuarterMinus‖)*|h| := by
    unfold actualCorrectionStockSiblingBoundaryTailFee
    rw [norm_mul,norm_mul,norm_neg,normhalf]
    exact (mul_le_mul_of_nonneg_left sibling (mul_nonneg (by norm_num) (norm_nonneg _))).trans_eq (by ring)
  unfold actualCorrectionStockQBTailFee
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_star]
  have normtwo : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
  simp only [normtwo]
  have combined := add_le_add
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left pairBound (by norm_num : 0≤(2:ℝ))) (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) (norm_nonneg (OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h))))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left siblingBound (by norm_num : 0≤(2:ℝ))) (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) (norm_nonneg (OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h))))
  exact combined.trans_eq (by unfold actualCorrectionSourceTailBudget; rw [norm_mul,normtwo]; ring)

theorem actual_current_finite_correction_source_error_budget (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (n N : ℕ) :
    ‖OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n -
      actualFiniteCorrectionSourceCharacter observation nontrivial half h N‖ ≤
      actualCorrectionSourceTailBudget observation nontrivial half h * (1/4:ℝ)^N := by
  rw [actual_current_consumes_finite_correction_and_same_tail observation nontrivial half h nonnegative bounded n N,add_sub_cancel_left]
  exact actual_correction_source_QB_tail_bound observation nontrivial half h N

theorem actual_correction_source_QB_tail_closure (h : ℝ) :
    Tendsto (actualCorrectionStockQBTailFee observation nontrivial half h) atTop (𝓝 0) := by
  have rate := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num : (1/4:ℝ) < 1)
  have budget := (tendsto_const_nhds : Tendsto (fun _ : ℕ => actualCorrectionSourceTailBudget observation nontrivial half h) atTop (𝓝 (actualCorrectionSourceTailBudget observation nontrivial half h))).mul rate
  simp only [mul_zero] at budget
  exact squeeze_zero_norm (fun N => actual_correction_source_QB_tail_bound observation nontrivial half h N) budget

/-- Finite source inverse stocks themselves generate the original Cross limit with their faithful source tail. -/
theorem actual_finite_correction_source_character_closure (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    Tendsto (actualFiniteCorrectionSourceCharacter observation nontrivial half h) atTop
      (𝓝 (OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)) := by
  have source := actual_correction_source_QB_tail_closure observation nontrivial half h
  have finite := (tendsto_const_nhds : Tendsto (fun _ : ℕ => OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h) atTop (𝓝 (OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h))).sub source
  simp only [sub_zero] at finite
  have equation : (fun N => OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h -
      actualCorrectionStockQBTailFee observation nontrivial half h N) = actualFiniteCorrectionSourceCharacter observation nontrivial half h := by
    funext N
    have generated := actual_current_consumes_finite_correction_and_same_tail observation nontrivial half h nonnegative bounded 0 N
    rw [←(OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action observation nontrivial half h nonnegative bounded 0)] at generated
    exact (eq_sub_of_add_eq generated.symm).symm
  rw [equation] at finite
  exact finite

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
