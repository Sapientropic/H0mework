import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourcePhysicalProjection.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Kernel

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourcePhysicalProjection
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKForcingGapAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q" => (1/4 : ℝ)
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "Γ[" coordinate "]" => ∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i

/-- This projection is applied only after the two actual full source columns have been generated. -/
def physicalGapZeroPart (coordinate : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection (gapZeroPart coordinate)

private theorem gapZeroPart_from_original (coordinate : BurnolCompletedMellinCoordinate) :
    gapZeroPart coordinate = (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
      Γ[coordinate] • ConstantDual.seed := by
  have source := generatedK_gap_decomposition coordinate
  rw [generatedK_eq_original] at source
  linear_combination (norm := module) -source

private theorem gapZeroPart_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (gapZeroPart coordinate) = 0 := by
  simp only [gapZeroPart,map_sum,map_smul,gapZeroColumns_quarter,smul_zero,Finset.sum_const_zero]

private theorem original_position_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      Γ[coordinate] • intervalConstant q := by
  have read := congrArg burnolQuarterRestriction (generatedK_gap_decomposition coordinate)
  rw [generatedK_eq_original,map_add,map_smul,gapZeroPart_quarter] at read
  change _ = 0+Γ[coordinate] •
    burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) at read
  simpa only [burnolQuarterRestriction_zeroExtension,zero_add] using read

/-- The Fourier gap is read from the same original K, without assigning a new physical qualification to X. -/
theorem gapZeroPart_fourier_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (fourierL2 (gapZeroPart coordinate)) =
      burnolQuarterMeanCoefficient
        (burnolQuarterRestriction (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) •
          intervalConstant q - Γ[coordinate] • burnolTruncatedFourier (intervalConstant q) := by
  have qualified := (burnolCompletedMellinRieszVector coordinate).property.1.2
  have centered : burnolQuarterMeanZeroProjection
      (burnolQuarterRestriction (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) = 0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr qualified
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  rw [gapZeroPart_from_original,map_sub,map_smul,map_sub,map_smul]
  conv_lhs => rw [sub_eq_zero.mp centered]
  rfl

theorem physicalGapZeroPart_source (coordinate : BurnolCompletedMellinCoordinate) :
    physicalGapZeroPart coordinate = burnolCompletedMellinRieszVector coordinate -
      Γ[coordinate] • constantPhysical := by
  have constantFixed : burnolEvenAmbientProjection ConstantDual.seed = constantPhysical :=
    Subtype.ext constantPhysicalVector_projection
  have fixed : burnolEvenAmbientProjection (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      burnolCompletedMellinRieszVector coordinate :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  unfold physicalGapZeroPart
  rw [gapZeroPart_from_original,map_sub,map_smul,constantFixed,fixed]

theorem physicalGapZeroPart_loss_source (coordinate : BurnolCompletedMellinCoordinate) :
    gapZeroPart coordinate-(physicalGapZeroPart coordinate : BurnolL2) =
      -Γ[coordinate] • (ConstantDual.seed-constantPhysicalVector) := by
  rw [gapZeroPart_from_original,physicalGapZeroPart_source]
  change (burnolCompletedMellinRieszVector coordinate : BurnolL2)-Γ[coordinate] • ConstantDual.seed -
    ((burnolCompletedMellinRieszVector coordinate : BurnolL2)-Γ[coordinate] • constantPhysicalVector) = _
  module

/-- Exact energy lost at the actual physical projection, with the full C correction retained. -/
theorem physicalGapZeroPart_loss_energy (coordinate : BurnolCompletedMellinCoordinate) :
    ‖gapZeroPart coordinate‖^2-‖physicalGapZeroPart coordinate‖^2 =
      ‖Γ[coordinate]‖^2*‖ConstantDual.seed-constantPhysicalVector‖^2 := by
  have orthogonal := (evenBurnolClosedFace q).toSubmodule.starProjection_inner_eq_zero
    (gapZeroPart coordinate) (physicalGapZeroPart coordinate : BurnolL2) (physicalGapZeroPart coordinate).property
  change inner ℂ (gapZeroPart coordinate-(physicalGapZeroPart coordinate : BurnolL2))
    (physicalGapZeroPart coordinate : BurnolL2) = 0 at orthogonal
  have split := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ orthogonal
  simp only [←pow_two,sub_add_cancel] at split
  rw [physicalGapZeroPart_loss_source,norm_smul,mul_pow,norm_neg] at split
  change ‖gapZeroPart coordinate‖^2 = _+‖physicalGapZeroPart coordinate‖^2 at split
  linarith

theorem physicalGapZeroPart_loss_calculated (coordinate : BurnolCompletedMellinCoordinate) :
    (((‖gapZeroPart coordinate‖^2-‖physicalGapZeroPart coordinate‖^2 : ℝ)) : ℂ) =
      ((‖Γ[coordinate]‖^2 : ℝ) : ℂ)*constantResponseMean/2 := by
  rw [physicalGapZeroPart_loss_energy,Complex.ofReal_mul,constantPhysicalVector_loss_energy]
  ring

theorem physicalGapZeroPart_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (physicalGapZeroPart coordinate : BurnolL2) =
      (Γ[coordinate]*constantResponseMean) • intervalConstant q := by
  rw [physicalGapZeroPart_source]
  change burnolQuarterRestriction ((burnolCompletedMellinRieszVector coordinate : BurnolL2)-
    Γ[coordinate] • constantPhysicalVector) = _
  rw [map_sub,map_smul,original_position_quarter,constantPhysicalVector_quarter]
  module

/-- The actual original R parameter c/2 acts on the calculated physical source field. -/
theorem original_R_physicalGapZeroPart_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (burnolDirectRightResolvent (coordinate.value/2)
      (physicalGapZeroPart coordinate : BurnolL2)) =
      (-2*Γ[coordinate]*constantResponseMean/coordinate.value) • intervalConstant q := by
  have right : 1/4 < (coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have acted := OriginalKGapMeanRSourceAction.original_R_quarter_source_action
    (coordinate.value/2) right (physicalGapZeroPart coordinate)
  have mean : FiniteMobiusResolventFlux.actualMean (physicalGapZeroPart coordinate : BurnolL2) =
      Γ[coordinate]*constantResponseMean := by
    rw [FiniteMobiusResolventFlux.actual_mean_physical]
    exact burnolConstantGapCoefficient_eq _ (by change (0 : ℝ)<1/4;norm_num) _ _ (physicalGapZeroPart_quarter coordinate).symm
  rw [mean] at acted
  change burnolQuarterRestriction _ = _ at acted
  convert! acted using 1
  congr 1
  ring

/-- All physical test vectors consume the paid complete G R action and its original source prices. -/
theorem original_R_physicalGapZeroPart_test (coordinate : BurnolCompletedMellinCoordinate)
    (left : BurnolPaAmbientCarrier) :
    inner ℂ (left : BurnolL2) (burnolDirectRightResolvent (coordinate.value/2)
      (physicalGapZeroPart coordinate : BurnolL2)) =
      inner ℂ (left : BurnolL2) (burnolDirectRightResolvent (coordinate.value/2)
        (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
      (Γ[coordinate]/2)*star (OriginalKGapProjectionEulerSource.actualFourierGapRPrice
        (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius left)) := by
  have source := (OriginalKGapProjectionEulerSource.actual_physical_gap_R_prices coordinate left).1
  rw [OriginalKGapProjectionEulerSource.actual_gap_mean_whole_source] at source
  change inner ℂ (left : BurnolL2)
    (burnolDirectRightResolvent (coordinate.value/2) ((2 : ℂ) • constantPhysicalVector)) = _ at source
  change inner ℂ (left : BurnolL2)
    (burnolDirectRightResolventCLM coordinate ((2 : ℂ) • constantPhysicalVector)) = _ at source
  rw [map_smul,inner_smul_right] at source
  rw [physicalGapZeroPart_source]
  change inner ℂ (left : BurnolL2) (burnolDirectRightResolvent (coordinate.value/2)
    ((burnolCompletedMellinRieszVector coordinate : BurnolL2)-Γ[coordinate] • constantPhysicalVector)) = _
  change inner ℂ (left : BurnolL2) (burnolDirectRightResolventCLM coordinate
    ((burnolCompletedMellinRieszVector coordinate : BurnolL2)-Γ[coordinate] • constantPhysicalVector)) = _
  rw [map_sub,map_smul,inner_sub_right,inner_smul_right]
  change _ - Γ[coordinate]*inner ℂ (left : BurnolL2)
    (burnolDirectRightResolvent (coordinate.value/2) constantPhysicalVector) = _
  change 2*inner ℂ (left : BurnolL2)
    (burnolDirectRightResolvent (coordinate.value/2) constantPhysicalVector) = _ at source
  change inner ℂ (left : BurnolL2)
    (burnolDirectRightResolvent (coordinate.value/2) (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
    Γ[coordinate]*inner ℂ (left : BurnolL2)
      (burnolDirectRightResolvent (coordinate.value/2) constantPhysicalVector) = _
  linear_combination -(Γ[coordinate]/2)*source

/-- Pa and Pa-perp are applied only on the actual physical carrier. -/
theorem physicalGapZeroPart_Pa_Q (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    OriginalKCombCofinalPaAction.E (physicalGapZeroPart coordinate : BurnolL2) =
      -Γ[coordinate] • OriginalKCombCofinalPaAction.E (constantPhysical : BurnolL2) ∧
    OriginalKCombCofinalPaAction.Q (physicalGapZeroPart coordinate : BurnolL2) =
      burnolCompletedMellinRieszVector coordinate -
        Γ[coordinate] • OriginalKCombCofinalPaAction.Q (constantPhysical : BurnolL2) := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have fixed (value : BurnolPaAmbientCarrier) : burnolEvenAmbientProjection (value : BurnolL2) = value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  have Econstant : OriginalKCombCofinalPaAction.E (constantPhysical : BurnolL2) =
      burnolCompactCoPoissonClosedRange.toSubmodule.starProjection constantPhysical := by
    change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (burnolEvenAmbientProjection (constantPhysical : BurnolL2)) = _
    rw [fixed]
  have Qconstant : OriginalKCombCofinalPaAction.Q (constantPhysical : BurnolL2) =
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection constantPhysical := by
    change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (burnolEvenAmbientProjection (constantPhysical : BurnolL2)) = _
    rw [fixed]
  have paZero : burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolCompletedMellinRieszVector coordinate) = 0 := by
    exact congrArg (fun value : ↥burnolCompactCoPoissonClosedRange.toSubmodule =>
      (value : BurnolPaAmbientCarrier))
      (Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal orthogonal)
  rw [Econstant,Qconstant]
  constructor
  · rw [physicalGapZeroPart_source]
    change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolEvenAmbientProjection ((burnolCompletedMellinRieszVector coordinate : BurnolL2)-
        Γ[coordinate] • (constantPhysical : BurnolL2))) = _
    rw [map_sub,map_smul,fixed,fixed,map_sub,map_smul,
      paZero,zero_sub,neg_smul]
  · rw [physicalGapZeroPart_source]
    change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolEvenAmbientProjection ((burnolCompletedMellinRieszVector coordinate : BurnolL2)-
        Γ[coordinate] • (constantPhysical : BurnolL2))) = _
    rw [map_sub,map_smul,fixed,fixed,map_sub,map_smul,
      Submodule.starProjection_eq_self_iff.mpr orthogonal]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourcePhysicalProjection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
