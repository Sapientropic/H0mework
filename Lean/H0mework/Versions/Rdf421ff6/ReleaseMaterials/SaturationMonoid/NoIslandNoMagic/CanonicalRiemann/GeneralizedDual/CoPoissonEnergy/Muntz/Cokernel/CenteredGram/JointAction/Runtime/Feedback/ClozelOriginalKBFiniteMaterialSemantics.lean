import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKBFiniteSourceCalculation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteRSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKBFiniteCalculation.Semantics

open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKFixedBoundarySourceFibre
open OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
open scoped InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "ι" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private theorem S_whole (value : M) :
    wholeZeroMean (fourierL2 (ι (value : Hq))) = ι (S value : Hq) := rfl

private theorem H_whole (h : ℝ) (value : M) :
    wholeZeroMean (burnolMultiplicativeDilation h (ι (value : Hq))) =
      ι (meanZeroDilation h value : Hq) := rfl

private theorem commutator_eval (h : ℝ) (input : E) (value : M)
    (read : input.eval sourceEnvironment = ι (value : Hq)) :
    (commutatorCode h input).eval sourceEnvironment = ι (sourceCommutator h value : Hq) := by
  change wholeZeroMean (burnolMultiplicativeDilation h (wholeZeroMean (fourierL2 (input.eval sourceEnvironment)))) +
    (-1 : ℂ) • wholeZeroMean (burnolMultiplicativeDilation (-h)
      (wholeZeroMean (fourierL2 (input.eval sourceEnvironment)))) = _
  rw [read, S_whole, H_whole, H_whole, neg_one_smul]
  change ι (meanZeroDilation h (S value) : Hq) + -ι (meanZeroDilation (-h) (S value) : Hq) =
    ι ((meanZeroDilation h (S value) : Hq) - (meanZeroDilation (-h) (S value) : Hq))
  rw [map_sub, sub_eq_add_neg]

private theorem first_U_eval (h : ℝ) :
    (firstUCode h).eval sourceEnvironment = ι (sourceFirst h : Hq) := by
  have drive : (driveUCode h).eval sourceEnvironment = ι (sourceDrive h : Hq) := by
    change wholeZeroMean (burnolMultiplicativeDilation h (etaCode.eval sourceEnvironment)) +
      (commutatorCode h vCode).eval sourceEnvironment +
      wholeZeroMean (fourierL2 ((commutatorCode h uCode).eval sourceEnvironment)) = _
    rw [commutator_eval h vCode Response.v original_S_source_eval,
      commutator_eval h uCode Response.u original_B_source_eval]
    change ι (meanZeroDilation h Response.eta : Hq) + ι (sourceCommutator h Response.v : Hq) +
      ι (S (sourceCommutator h Response.u) : Hq) =
        ι ((meanZeroDilation h Response.eta : Hq) + (sourceCommutator h Response.v : Hq) +
          (S (sourceCommutator h Response.u) : Hq))
    simp only [map_add]
  change wholeBInverse ((driveUCode h).eval sourceEnvironment) = _
  rw [drive, wholeBInverse_faithful]
  rfl

private theorem second_U_eval (h : ℝ) :
    (secondUCode h).eval sourceEnvironment = ι (sourceSecond h : Hq) := by
  change wholeZeroMean (fourierL2 ((firstUCode h).eval sourceEnvironment)) = _
  rw [first_U_eval]
  rfl

private theorem first_V_eval (h : ℝ) :
    (firstVCode h).eval sourceEnvironment = ι (sourceVFirst h : Hq) := by
  have difference : (Expr.add uCode
      (Expr.linear (((-1 : ℂ) • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom) etaCode)).eval
        sourceEnvironment = ι ((Response.u - Response.eta : M) : Hq) := by
    change uCode.eval sourceEnvironment + (-1 : ℂ) • ι (Response.eta : Hq) = _
    rw [original_B_source_eval, neg_one_smul]
    change ι (Response.u : Hq) + -ι (Response.eta : Hq) = ι ((Response.u : Hq) - (Response.eta : Hq))
    rw [map_sub, sub_eq_add_neg]
  have drive : (driveVCode h).eval sourceEnvironment = ι (sourceDriveV h : Hq) := by
    change wholeZeroMean (burnolMultiplicativeDilation h
      (wholeZeroMean (fourierL2 (etaCode.eval sourceEnvironment)))) +
      (commutatorCode h (Expr.add uCode
        (Expr.linear (((-1 : ℂ) • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom) etaCode))).eval sourceEnvironment +
      wholeZeroMean (fourierL2 ((commutatorCode h vCode).eval sourceEnvironment)) = _
    rw [commutator_eval h _ (Response.u - Response.eta) difference,
      commutator_eval h vCode Response.v original_S_source_eval]
    change ι (meanZeroDilation h (S Response.eta) : Hq) +
      ι (sourceCommutator h (Response.u - Response.eta) : Hq) +
      ι (S (sourceCommutator h Response.v) : Hq) =
        ι ((meanZeroDilation h (S Response.eta) : Hq) +
          (sourceCommutator h (Response.u - Response.eta) : Hq) +
          (S (sourceCommutator h Response.v) : Hq))
    simp only [map_add]
  change wholeBInverse ((driveVCode h).eval sourceEnvironment) = _
  rw [drive, wholeBInverse_faithful]
  rfl

private theorem second_V_eval (h : ℝ) :
    (secondVCode h).eval sourceEnvironment = ι (sourceVSecond h : Hq) := by
  change wholeZeroMean (fourierL2 ((firstVCode h).eval sourceEnvironment)) = _
  rw [first_V_eval]
  rfl

private theorem loss_eval (h : ℝ) (input : E) (value : M)
    (read : input.eval sourceEnvironment = ι (value : Hq)) :
    (lossCode h input).eval sourceEnvironment = fullWindowLoss h value := by
  rw [loss_code_eval, read]
  rw [H_whole]
  have inventory := outward_full_source_inventory h value
  linear_combination (norm := module) inventory

private theorem f0_eval (c : BurnolCompletedMellinCoordinate) :
    (f0Code c).eval sourceEnvironment = regularForcing c 0 := by
  change fourierL2 (uCode.eval sourceEnvironment) + (-1 : ℂ) • vCode.eval sourceEnvironment +
    (1/2 - sourceRate c) • ConstantDual.seed = _
  rw [original_B_source_eval, original_S_source_eval, neg_one_smul]
  simp only [regularForcing, Matrix.cons_val_zero, Response.wholeU, Response.wholeV, sub_eq_add_neg]
  rfl

private theorem f0_minus_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (f0MinusCode c h).eval sourceEnvironment = f0MinusSource c h := by
  change fourierL2 ((firstUCode h).eval sourceEnvironment) +
    (-1 : ℂ) • (secondUCode h).eval sourceEnvironment +
    (-1 : ℂ) • (lossCode h vCode).eval sourceEnvironment +
    (1/2 - sourceRate c) • burnolMultiplicativeDilation (-h) ConstantDual.seed = _
  rw [first_U_eval, second_U_eval, loss_eval h vCode Response.v original_S_source_eval]
  simp only [neg_one_smul, f0MinusSource, sub_eq_add_neg]
  rfl

private theorem f0_plus_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (f0PlusCode c h).eval sourceEnvironment = f0PlusSource c h := by
  change fourierL2 ((secondVCode h).eval sourceEnvironment +
    wholeZeroMean (burnolMultiplicativeDilation (-h) (etaCode.eval sourceEnvironment))) +
    (-1 : ℂ) • (firstVCode h).eval sourceEnvironment +
    fourierL2 ((lossCode h uCode).eval sourceEnvironment) +
    (1/2 - sourceRate c) • burnolMultiplicativeDilation h ConstantDual.seed = _
  rw [second_V_eval, first_V_eval, loss_eval h uCode Response.u original_B_source_eval]
  simp only [neg_one_smul]
  change fourierL2 (ι (sourceVSecond h : Hq) + ι (meanZeroDilation (-h) Response.eta : Hq)) +
    -ι (sourceVFirst h : Hq) + fourierL2 (fullWindowLoss h Response.u) + _ = _
  rw [←map_add]
  simp only [f0PlusSource, sub_eq_add_neg]
  rfl

private theorem forcing_eval (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (forcingCode c i).eval sourceEnvironment = regularForcing c i := by
  fin_cases i
  · exact f0_eval c
  · change fourierL2 ((f0Code c).eval sourceEnvironment) +
      (2 * sourceRate c) • fourierL2 ConstantDual.seed = _
    rw [f0_eval]
    change fourierL2 (regularForcing c 0) +
      (2 * OriginalKSourceResolventReconstruction.sourceRate c) • fourierL2 ConstantDual.seed = _
    have source := OriginalKForcingGapAction.fourier_forcing0_source c
    exact (eq_sub_iff_add_eq).mp source

private theorem forcing_plus_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    (forcingPlusCode c h i).eval sourceEnvironment = forcingPlus c h i := by
  fin_cases i
  · exact f0_plus_eval c h
  · change fourierL2 ((f0MinusCode c h).eval sourceEnvironment) +
      (2 * sourceRate c) • burnolMultiplicativeDilation h (fourierL2 ConstantDual.seed) = _
    rw [f0_minus_eval]
    rfl

private theorem forcing_minus_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    (forcingMinusCode c h i).eval sourceEnvironment = forcingMinus c h i := by
  fin_cases i
  · exact f0_minus_eval c h
  · change fourierL2 ((f0PlusCode c h).eval sourceEnvironment) +
      (2 * sourceRate c) • burnolMultiplicativeDilation (-h) (fourierL2 ConstantDual.seed) = _
    rw [f0_plus_eval]
    rfl

private theorem endpoint_read (value : M) :
    endpointRead (ι (value : Hq)) = burnolMeanZeroFourierRaw value q := by
  change (4 : ℂ) * inner ℂ
    (burnolQuarterRestriction.adjoint (Constructor.endpointColumn (-q) : Hq)) (ι (value : Hq)) = _
  rw [ContinuousLinearMap.adjoint_inner_left, burnolQuarterRestriction_zeroExtension]
  change (4 : ℂ) * inner ℂ (Constructor.endpointColumn (-q)) value = _
  rw [OriginalCommonInverseForcing.InverseEuler.endpointColumn_inner]
  norm_num; ring

private theorem coefficient_source_eval (c : BurnolCompletedMellinCoordinate) :
    (coefficientSourceCode c).eval sourceEnvironment = ι (burnolRieszSingleFourierSource c : Hq) := by
  change wholeBInverse (ι (burnolAmbientMeanZeroFourier
    (burnolAmbientCompletedMellinKernelFormula c) : Hq)) = _
  rw [wholeBInverse_faithful]
  rfl

private theorem coefficient_A_eval (c : BurnolCompletedMellinCoordinate) (input : E) :
    (coefficientAActionCode c input).eval sourceEnvironment = Kernel.A c • input.eval sourceEnvironment := by
  rw [coefficient_A_code_eval, coefficient_source_eval, endpoint_read]
  rfl

private theorem coefficient_beta_eval (c : BurnolCompletedMellinCoordinate) (input : E) :
    (coefficientBetaActionCode c input).eval sourceEnvironment = Kernel.beta c • input.eval sourceEnvironment := by
  rw [coefficient_beta_code_eval, coefficient_source_eval, S_whole, endpoint_read]
  rfl

private theorem input_column_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    (inputColumnCode c h i).eval sourceEnvironment = calculatedInputColumn c h i := by
  change pairedMellinTranslationCharacter c.value h •
    (sourceInputCode c (forcingCode c i)).eval sourceEnvironment + (-1 : ℂ) •
      ((1/2 : ℂ) • ((sourceInputCode c (forcingPlusCode c h i)).eval sourceEnvironment +
        (sourceInputCode c (forcingMinusCode c h i)).eval sourceEnvironment)) = _
  rw [source_input_code_eval, source_input_code_eval, source_input_code_eval,
    forcing_eval, forcing_plus_eval, forcing_minus_eval, neg_one_smul]
  simp only [calculatedInputColumn, regularInput, sourceInput,
    OriginalKSourceResolventReconstruction.sourceResolvent, sub_eq_add_neg]

/-- Both B drives, full loss, and the original source endpoint coefficients feed the actual R input. -/
theorem boundary_input_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (boundaryInputCode c h).eval sourceEnvironment = calculatedBoundaryInput c h := by
  change (coefficientAActionCode c (inputColumnCode c h 0)).eval sourceEnvironment +
    (coefficientBetaActionCode c (inputColumnCode c h 1)).eval sourceEnvironment = _
  rw [coefficient_A_eval, coefficient_beta_eval, input_column_eval, input_column_eval]
  simp only [calculatedBoundaryInput, Fin.sum_univ_two,
    OriginalKSourceResolventReconstruction.sourceCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem boundary_action_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) (input : E) :
    (boundaryActionCode c h input).eval sourceEnvironment = finiteBoundaryAction c h (input.eval sourceEnvironment) := by
  change pairedMellinTranslationCharacter c.value h • input.eval sourceEnvironment + (-1 : ℂ) •
    ((1/2 : ℂ) • (burnolMultiplicativeDilation h (input.eval sourceEnvironment) +
      burnolMultiplicativeDilation (-h) (input.eval sourceEnvironment))) = _
  rw [neg_one_smul]
  simp only [finiteBoundaryAction, sub_eq_add_neg]

private theorem jump_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (jumpCode c h).eval sourceEnvironment = rawBoundaryJump c h := by
  change (coefficientAActionCode c (boundaryActionCode c h constantCode)).eval sourceEnvironment +
    (coefficientBetaActionCode c (boundaryActionCode c h _)).eval sourceEnvironment = _
  rw [coefficient_A_eval, coefficient_beta_eval, boundary_action_eval, boundary_action_eval]
  change Kernel.A c • finiteBoundaryAction c h ConstantDual.seed +
    Kernel.beta c • finiteBoundaryAction c h ((-1 : ℂ) • fourierL2 ConstantDual.seed) = _
  rw [neg_one_smul, rawBoundaryJump_source]
  simp only [OriginalKSourceResolventReconstruction.sourceCoefficients,
    Matrix.cons_val_zero, Matrix.cons_val_one, finiteBoundaryAction, map_neg, smul_neg]
  module

/-- The installed AST evaluates to the full original-R normal, using the generated input equality. -/
theorem code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) (_nonnegative : 0 ≤ h) :
    (code c h).eval sourceEnvironment = calculatedSourceNormal c h := by
  rw [normal_code_eval, boundary_input_code_eval, jump_code_eval]
  rfl

end OriginalKBFiniteCalculation.Semantics
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
