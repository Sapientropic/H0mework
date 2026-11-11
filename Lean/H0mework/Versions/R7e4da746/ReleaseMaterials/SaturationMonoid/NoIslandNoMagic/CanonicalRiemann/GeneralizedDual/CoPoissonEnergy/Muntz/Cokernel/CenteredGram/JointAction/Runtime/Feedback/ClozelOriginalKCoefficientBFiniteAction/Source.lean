import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteRControls
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKBFiniteSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCoefficientBFiniteAction
open Complex BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceFiniteUpdate OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
open OriginalKSourceResolventReconstruction OriginalKFixedBoundarySourceFibre
open scoped InnerProductSpace
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroOneMinusSquare
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def sourceEta (c : BurnolCompletedMellinCoordinate) : M :=
  burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula c)
def sourceB (c : BurnolCompletedMellinCoordinate) : M := burnolMeanZeroBlockInverse (sourceEta c)
def sourceSB (c : BurnolCompletedMellinCoordinate) : M := S (sourceB c)
def elementarySource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c)

theorem sourceB_original (c : BurnolCompletedMellinCoordinate) :
    sourceB c = burnolRieszSingleFourierSource c := rfl

/-- This is the coefficient B column executed by the installed source-only AST. -/
theorem coefficient_source_calculation (c : BurnolCompletedMellinCoordinate) :
    (OriginalKBFiniteCalculation.coefficientSourceCode c).eval OriginalKBFiniteCalculation.sourceEnvironment =
      E (sourceB c : Hq) := by
  change OriginalKBFiniteCalculation.wholeBInverse (E (sourceEta c : Hq)) = _
  exact OriginalKBFiniteCalculation.wholeBInverse_faithful _

theorem source_pair_equation (c : BurnolCompletedMellinCoordinate) :
    B (sourceB c) = sourceEta c := burnolRieszSingleFourierSource_equation c

private theorem finite_B_balance (h : ℝ) (nonnegative : 0 ≤ h) (value : M) :
    B (meanZeroDilation h value) = meanZeroDilation h (B value) +
      sourceCommutator h (S value) + S (sourceCommutator h value) := by
  change meanZeroDilation h value - S (S (meanZeroDilation h value)) =
    meanZeroDilation h (value - S (S value)) + sourceCommutator h (S value) + S (sourceCommutator h value)
  rw [map_sub, sourceCommutator_action h nonnegative, sourceCommutator_action h nonnegative, map_sub]
  module

def sourceDriveB (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M :=
  meanZeroDilation h (sourceEta c) + sourceCommutator h (sourceSB c) + S (sourceCommutator h (sourceB c))
def sourceFirstB (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M := burnolMeanZeroBlockInverse (sourceDriveB c h)
def sourceSecondB (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M := S (sourceFirstB c h)

theorem source_B_finite_action (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    B (meanZeroDilation h (sourceB c)) = sourceDriveB c h := by
  rw [finite_B_balance h nonnegative, source_pair_equation]
  rfl

theorem sourceFirstB_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceFirstB c h = meanZeroDilation h (sourceB c) := by
  have inverseLeft : burnolMeanZeroBlockInverse * B = 1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  have read := congrArg burnolMeanZeroBlockInverse (source_B_finite_action c h nonnegative)
  change (burnolMeanZeroBlockInverse * B) (meanZeroDilation h (sourceB c)) = sourceFirstB c h at read
  rw [inverseLeft] at read
  exact read.symm

theorem sourceSecondB_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceSecondB c h = meanZeroDilation (-h) (sourceSB c) := by
  rw [sourceSecondB, sourceFirstB_actual c h nonnegative, finite_fourier_intertwining h nonnegative]
  rfl

def sourceDriveSB (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M :=
  meanZeroDilation h (S (sourceEta c)) + sourceCommutator h (sourceB c - sourceEta c) +
    S (sourceCommutator h (sourceSB c))
def sourceFirstSB (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M := burnolMeanZeroBlockInverse (sourceDriveSB c h)
def sourceSecondSB (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M := S (sourceFirstSB c h)

private theorem source_SB_equation (c : BurnolCompletedMellinCoordinate) : B (sourceSB c) = S (sourceEta c) := by
  have read := congrArg S (source_pair_equation c)
  change S (sourceB c - S (S (sourceB c))) = _ at read
  rw [map_sub] at read
  exact read

theorem source_SB_finite_action (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    B (meanZeroDilation h (sourceSB c)) = sourceDriveSB c h := by
  rw [finite_B_balance h nonnegative, source_SB_equation]
  have pair : S (sourceSB c) = sourceB c - sourceEta c := by
    have read := source_pair_equation c
    change sourceB c - S (sourceSB c) = sourceEta c at read
    linear_combination (norm := module) -read
  rw [pair]
  rfl

theorem sourceFirstSB_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceFirstSB c h = meanZeroDilation h (sourceSB c) := by
  have inverseLeft : burnolMeanZeroBlockInverse * B = 1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  have read := congrArg burnolMeanZeroBlockInverse (source_SB_finite_action c h nonnegative)
  change (burnolMeanZeroBlockInverse * B) (meanZeroDilation h (sourceSB c)) = sourceFirstSB c h at read
  rw [inverseLeft] at read
  exact read.symm

theorem sourceSecondSB_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceSecondSB c h + meanZeroDilation (-h) (sourceEta c) = meanZeroDilation (-h) (sourceB c) := by
  rw [sourceSecondSB, sourceFirstSB_actual c h nonnegative, finite_fourier_intertwining h nonnegative]
  have read := congrArg (meanZeroDilation (-h)) (source_pair_equation c)
  change meanZeroDilation (-h) (sourceB c - S (sourceSB c)) = meanZeroDilation (-h) (sourceEta c) at read
  rw [map_sub] at read
  linear_combination (norm := module) -read

/-- The original projection source reconstructs K before either finite action is generated. -/
def sourceKernel (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  elementarySource c + E (sourceSB c : Hq) - fourierL2 (E (sourceB c : Hq))

theorem sourceKernel_original (c : BurnolCompletedMellinCoordinate) :
    sourceKernel c = (burnolCompletedMellinRieszVector c : BurnolL2) :=
  (Kernel.original_kernel_reconstruction c).symm

def sourceKernelPlus (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation h (elementarySource c) + E (sourceFirstSB c h : Hq) -
    fourierL2 (E (sourceSecondSB c h + meanZeroDilation (-h) (sourceEta c) : Hq)) -
      fourierL2 (fullWindowLoss h (sourceB c))
def sourceKernelMinus (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation (-h) (elementarySource c) + E (sourceSecondB c h : Hq) -
    fourierL2 (E (sourceFirstB c h : Hq)) + fullWindowLoss h (sourceSB c)

theorem source_kernel_plus_action (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMultiplicativeDilation h (sourceKernel c) = sourceKernelPlus c h := by
  unfold sourceKernel
  rw [map_sub, map_add]
  have reverse : burnolMultiplicativeDilation h (fourierL2 (E (sourceB c : Hq))) =
      fourierL2 (burnolMultiplicativeDilation (-h) (E (sourceB c : Hq))) := by
    simpa only [neg_neg] using (fourierL2_burnolMultiplicativeDilation (-h) (E (sourceB c : Hq))).symm
  rw [reverse, outward_full_source_inventory, map_add]
  rw [←inward_extension h nonnegative, ←sourceFirstSB_actual c h nonnegative,
    ←sourceSecondSB_actual c h nonnegative]
  unfold sourceKernelPlus
  module

theorem source_kernel_minus_action (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    burnolMultiplicativeDilation (-h) (sourceKernel c) = sourceKernelMinus c h := by
  unfold sourceKernel
  rw [map_sub, map_add, ←fourierL2_burnolMultiplicativeDilation,
    outward_full_source_inventory, ←sourceSecondB_actual c h nonnegative,
    ←inward_extension h nonnegative, ←sourceFirstB_actual c h nonnegative]
  unfold sourceKernelMinus
  module

/-- Both true finite-window losses survive; neither is replaced by a scalar or Pa witness. -/
def sourceCore (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (elementarySource c) - (1/2 : ℂ) •
    (fullWindowLoss h (sourceSB c) - fourierL2 (fullWindowLoss h (sourceB c)))

def compactPosition (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M :=
  pairedMellinTranslationCharacter c.value h • sourceSB c - (1/2 : ℂ) •
    (sourceFirstSB c h + sourceSecondB c h)
def compactFourier (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M :=
  -pairedMellinTranslationCharacter c.value h • sourceB c + (1/2 : ℂ) •
    (sourceSecondSB c h + meanZeroDilation (-h) (sourceEta c) + sourceFirstB c h)
def compactCorrection (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  E (compactPosition c h : Hq) + fourierL2 (E (compactFourier c h : Hq))

theorem source_boundary_full_inventory (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    finiteBoundaryAction c h (sourceKernel c) = sourceCore c h + compactCorrection c h := by
  unfold finiteBoundaryAction
  rw [source_kernel_plus_action c h nonnegative, source_kernel_minus_action c h nonnegative]
  unfold sourceCore compactCorrection compactPosition compactFourier sourceKernelPlus sourceKernelMinus sourceKernel
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, map_add, map_sub, map_smul]
  unfold finiteBoundaryAction
  module

/-- The calculated original-R normal retains the whole compact difference vector. -/
theorem calculated_normal_full_inventory (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    calculatedSourceNormal c h = sourceCore c h + compactCorrection c h := by
  rw [calculated_source_normal_actual c h nonnegative, contact_source_word_actual,
    ←generatedK_boundary_action, generatedK_eq_original, ←sourceKernel_original]
  exact source_boundary_full_inventory c h nonnegative

private theorem physical_extension_zero (test : BurnolPaAmbientCarrier) (value : M) :
    inner ℂ (test : BurnolL2) (E (value : Hq)) = 0 := by
  change inner ℂ (test : BurnolL2) (burnolQuarterRestriction.adjoint (value : Hq)) = 0
  rw [ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction]
  exact value.property _ test.property.1.1

private theorem physical_fourier_extension_zero (test : BurnolPaAmbientCarrier) (value : M) :
    inner ℂ (test : BurnolL2) (fourierL2 (E (value : Hq))) = 0 := by
  have twice : fourierL2 (fourierL2 (test : BurnolL2)) = test := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp test.property.2
  have read := fourierL2.inner_map_map (fourierL2 (test : BurnolL2)) (E (value : Hq))
  rw [twice] at read
  rw [read]
  change inner ℂ (fourierL2 (test : BurnolL2)) (burnolQuarterRestriction.adjoint (value : Hq)) = 0
  rw [ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction]
  exact value.property _ test.property.1.2

/-- Only the actual physical qualification kills the two computed compact mean-zero feet. -/
theorem compactCorrection_physical_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (test : BurnolPaAmbientCarrier) : inner ℂ (test : BurnolL2) (compactCorrection c h) = 0 := by
  rw [compactCorrection, inner_add_right, physical_extension_zero, physical_fourier_extension_zero, add_zero]

theorem physical_cotest_core (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h)
    (test : BurnolPaAmbientCarrier) :
    inner ℂ (test : BurnolL2) (calculatedSourceNormal c h) = inner ℂ (test : BurnolL2) (sourceCore c h) := by
  rw [calculated_normal_full_inventory c h nonnegative, inner_add_right,
    compactCorrection_physical_cotest, add_zero]

theorem original_K_self_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (calculatedSourceNormal c h) =
      inner ℂ (sourceKernel c) (sourceCore c h) := by
  rw [sourceKernel_original]
  exact physical_cotest_core c h nonnegative (burnolCompletedMellinRieszVector c)

/-- The existing full-input R/H action reads the same new self-source equation. -/
theorem original_R_H_input_jump_price (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (OriginalKFullAdjointSource.sourceAdjointField c) (calculatedBoundaryInput c h) +
      inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (rawBoundaryJump c h) =
        inner ℂ (sourceKernel c) (sourceCore c h) := by
  have read := original_K_self_cotest c h nonnegative
  change inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
    (burnolDirectRightResolvent (c.value/2) (calculatedBoundaryInput c h) + rawBoundaryJump c h) = _ at read
  rw [inner_add_right, OriginalKFullAdjointSource.original_R_full_input] at read
  exact read

theorem original_fixedResidual_core (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (fixed : h = Real.log stageZeroSonineQ) :
    burnolPaFixedShiftResidual c zero = -inner ℂ (sourceKernel c) (sourceCore c h) := by
  rw [original_fixedResidual_calculated_source c zero h nonnegative fixed, generatedK_eq_original,
    original_K_self_cotest c h nonnegative]

def coreWithoutBLoss (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (elementarySource c) - (1/2 : ℂ) • fullWindowLoss h (sourceSB c)
def coreWithoutSBLoss (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (elementarySource c) + (1/2 : ℂ) • fourierL2 (fullWindowLoss h (sourceB c))

theorem delete_B_loss_exact (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (fixed : h = Real.log stageZeroSonineQ) :
    (coreWithoutBLoss c h + compactCorrection c h) - calculatedSourceNormal c h =
      -(1/2 : ℂ) • fourierL2 (fullWindowLoss h (sourceB c)) ∧
    (-inner ℂ (sourceKernel c) (coreWithoutBLoss c h)) - burnolPaFixedShiftResidual c zero =
      (1/2 : ℂ) * inner ℂ (sourceKernel c) (fourierL2 (fullWindowLoss h (sourceB c))) := by
  rw [calculated_normal_full_inventory c h nonnegative, original_fixedResidual_core c zero h nonnegative fixed]
  constructor
  · unfold sourceCore coreWithoutBLoss
    module
  · simp only [sourceCore, coreWithoutBLoss, inner_sub_right, inner_smul_right]
    ring

theorem delete_SB_loss_exact (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (fixed : h = Real.log stageZeroSonineQ) :
    (coreWithoutSBLoss c h + compactCorrection c h) - calculatedSourceNormal c h =
      (1/2 : ℂ) • fullWindowLoss h (sourceSB c) ∧
    (-inner ℂ (sourceKernel c) (coreWithoutSBLoss c h)) - burnolPaFixedShiftResidual c zero =
      -(1/2 : ℂ) * inner ℂ (sourceKernel c) (fullWindowLoss h (sourceSB c)) := by
  rw [calculated_normal_full_inventory c h nonnegative, original_fixedResidual_core c zero h nonnegative fixed]
  constructor
  · unfold sourceCore coreWithoutSBLoss
    module
  · simp only [sourceCore, coreWithoutSBLoss, inner_add_right, inner_sub_right, inner_smul_right]
    ring

private theorem boundary_zero (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    finiteBoundaryAction c 0 value = 0 := by
  have character : pairedMellinTranslationCharacter c.value 0 = 1 := by
    norm_num [pairedMellinTranslationCharacter, fullMellinTranslationCharacter, reciprocalMellinTranslationCharacter]
  rw [finiteBoundaryAction, character]
  simp only [one_smul, neg_zero, burnolMultiplicativeDilation_zero]
  module

/-- h=0 preserves the original coefficient source pair, both means, and the zero boundary. -/
theorem source_zero_override (c : BurnolCompletedMellinCoordinate) :
    sourceDriveB c 0 = sourceEta c ∧ sourceDriveSB c 0 = S (sourceEta c) ∧
    sourceFirstB c 0 = sourceB c ∧ sourceSecondB c 0 = sourceSB c ∧
    sourceFirstSB c 0 = sourceSB c ∧ sourceSecondSB c 0 = sourceB c - sourceEta c ∧
    fullWindowLoss 0 (sourceB c) = 0 ∧ fullWindowLoss 0 (sourceSB c) = 0 ∧
    sourceCore c 0 = 0 ∧ compactCorrection c 0 = 0 := by
  have bFirst : sourceFirstB c 0 = sourceB c := by
    simpa only [meanZeroDilation_zero] using sourceFirstB_actual c 0 le_rfl
  have bSecond : sourceSecondB c 0 = sourceSB c := by rw [sourceSecondB, bFirst];rfl
  have sbFirst : sourceFirstSB c 0 = sourceSB c := by
    simpa only [meanZeroDilation_zero] using sourceFirstSB_actual c 0 le_rfl
  have sbRead := sourceSecondSB_actual c 0 le_rfl
  rw [neg_zero, meanZeroDilation_zero, meanZeroDilation_zero] at sbRead
  have sbSecond : sourceSecondSB c 0 = sourceB c - sourceEta c := eq_sub_of_add_eq sbRead
  have lossB := fullWindowLoss_zero (sourceB c)
  have lossSB := fullWindowLoss_zero (sourceSB c)
  have core : sourceCore c 0 = 0 := by
    rw [sourceCore, boundary_zero, lossB, lossSB, map_zero, sub_self, smul_zero, sub_zero]
  have inventory := source_boundary_full_inventory c 0 le_rfl
  rw [boundary_zero, core, zero_add] at inventory
  exact ⟨by simp only [sourceDriveB, meanZeroDilation_zero, sourceCommutator_zero, map_zero, add_zero],
    by simp only [sourceDriveSB, meanZeroDilation_zero, sourceCommutator_zero, map_zero, add_zero],
    bFirst, bSecond, sbFirst, sbSecond, lossB, lossSB, core, inventory.symm⟩

end OriginalKCoefficientBFiniteAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
