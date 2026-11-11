import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourcePhysicalProjection.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourcePhysicalProjection
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKForcingGapAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "Γ[" coordinate "]" => ∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i

/-- Treating X as already physical omits this exact original R field; it is not declared nonzero. -/
theorem omit_physical_projection_changes_R (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (burnolDirectRightResolvent (coordinate.value/2) (gapZeroPart coordinate)) -
    burnolQuarterRestriction (burnolDirectRightResolvent (coordinate.value/2)
      (physicalGapZeroPart coordinate : BurnolL2)) =
    (2*Γ[coordinate]*constantResponseMean/coordinate.value) • intervalConstant (1/4 : ℝ) := by
  have gap : burnolQuarterRestriction (gapZeroPart coordinate) = (0 : ℂ) • intervalConstant (1/4 : ℝ) := by
    simp only [gapZeroPart,map_sum,map_smul,gapZeroColumns_quarter,smul_zero,Finset.sum_const_zero,zero_smul]
  have right : 1/4 < (coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have omitted := right_resolvent_quarter_constant (coordinate.value/2) right
    (gapZeroPart coordinate) 0 gap
  rw [omitted,original_R_physicalGapZeroPart_quarter]
  simp only [neg_zero,zero_div,zero_smul,zero_sub,←neg_smul]
  congr 1
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (rightHalf : 1/2<observation.coordinate.re)
local notation "c" => originalKCoordinate observation.coordinate
  (And.right (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial)) rightHalf
local notation "h" => Real.log stageZeroSonineQ
local notation "PX" => physicalGapZeroPart c
local notation "Gamma" => Γ[c]

/-- Removing the projected C column retains every actual residual cross/contact price. -/
theorem installed_omit_physical_unit_effect :
    (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual -
      finitePair c h (PX : BurnolL2) (PX : BurnolL2) =
      Gamma*finitePair c h (PX : BurnolL2) constantPhysicalVector +
      star Gamma*finitePair c h constantPhysicalVector (PX : BurnolL2) +
      star Gamma*Gamma*finitePair c h constantPhysicalVector constantPhysicalVector := by
  rw [installed_residual_physical_decomposition]
  ring

/-- An explicit zero source coefficient removes all C costs and all of its R/Pa contribution. -/
theorem installed_physical_coefficient_zero (coefficientZero : Gamma=0) :
    (installedOriginalKReceiptAt observation nontrivial rightHalf).kernel = (PX : BurnolL2) ∧
    (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual = finitePair c h (PX : BurnolL2) (PX : BurnolL2) ∧
    burnolQuarterRestriction (burnolDirectRightResolvent ((c).value/2) (PX : BurnolL2)) = 0 ∧
    OriginalKCombCofinalPaAction.E (PX : BurnolL2) = 0 ∧
    OriginalKCombCofinalPaAction.Q (PX : BurnolL2) = burnolCompletedMellinRieszVector c ∧
    ‖gapZeroPart c‖^2-‖PX‖^2 = 0 := by
  have projection := physicalGapZeroPart_source c
  have originalKernel := congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel)
    (installedOriginalKReceiptAt_eq_source observation nontrivial rightHalf)
  have residual := installed_residual_physical_decomposition observation nontrivial rightHalf
  have field := original_R_physicalGapZeroPart_quarter c
  have paQ := physicalGapZeroPart_Pa_Q c observation.mathlibZero
  have loss := physicalGapZeroPart_loss_energy c
  simp only [coefficientZero,zero_smul,sub_zero] at projection
  simp only [coefficientZero,star_zero,zero_mul,add_zero] at residual
  simp only [coefficientZero,mul_zero,zero_mul,zero_div,zero_smul] at field
  simp only [coefficientZero,neg_zero,zero_smul,sub_zero] at paQ
  simp only [coefficientZero,norm_zero] at loss
  norm_num at loss
  exact ⟨originalKernel.trans (congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) projection.symm),
    residual,field,paQ.1,paQ.2,loss⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourcePhysicalProjection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
