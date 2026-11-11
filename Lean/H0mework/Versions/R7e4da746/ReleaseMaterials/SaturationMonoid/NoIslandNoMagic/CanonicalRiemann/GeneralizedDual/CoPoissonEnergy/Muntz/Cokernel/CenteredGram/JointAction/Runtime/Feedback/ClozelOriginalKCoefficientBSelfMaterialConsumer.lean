import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBSelfMaterialSemantics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteMaterialConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteBornProjection

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCoefficientBSelfCalculation.MaterialConsumer

open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
open scoped InnerProductSpace

theorem fixed_nonnegative : 0 ≤ OriginalKBFiniteCalculation.fixedShift := by
  apply Real.log_nonneg
  norm_num [stageZeroSonineQ]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => OriginalKBFiniteCalculation.fixedShift
local notation "material" => runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

theorem installed_source_raw :
    (material).1.environment = sourceEnvironment ∧
    (material).1.expression = cotestCode c h := by
  rw [runtimeCoefficientBSelfCalculationResultAt_source]
  exact ⟨rfl, rfl⟩

/-- The actual calculation value consumes both generated source subtrees. -/
theorem installed_source_calculated_value :
    (material).2.2.1 = inner ℂ (sourceKernel c) (sourceCore c h) • ConstantDual.seed := by
  rw [runtimeCoefficientBSelfCalculationResultAt_source]
  exact (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value Base
    (reader observation nontrivial half)
    ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)).trans
      (Semantics.cotest_code_eval c h)

theorem installed_source_complete_history :
    (material).2.1.2.length = remaining (cotestCode c h) ∧
    0 < (material).2.1.2.length := by
  rw [runtimeCoefficientBSelfCalculationResultAt_source]
  exact ⟨result_history observation nontrivial half _, result_history_nonempty observation nontrivial half _⟩

/-- Both mathematical reads are projections of the original installed K source receipt. -/
theorem installed_receipt_source :
    (receipt).kernel = sourceKernel c ∧
    (receipt).fixedResidual = burnolPaFixedShiftResidual c observation.mathlibZero := by
  have anchor := installedOriginalKReceiptAt_eq_source observation nontrivial half.down
  constructor
  · exact (congrArg (fun value : OriginalRieszFiniteSource.Receipt => value.kernel) anchor).trans
      (sourceKernel_original c).symm
  · exact congrArg (fun value : OriginalRieszFiniteSource.Receipt => value.fixedResidual) anchor

theorem installed_source_value :
    (material).2.2.1 = -(receipt).fixedResidual • ConstantDual.seed := by
  rw [installed_source_calculated_value, (installed_receipt_source observation nontrivial half).2,
    original_fixedResidual_core c observation.mathlibZero h fixed_nonnegative rfl, neg_neg]

/-- The literal source trace writes this complete price boundary in the original frame environment. -/
theorem installed_bound_source_relation :
    SourceOperationScalarPresentation.relationMap (R := ℤ)
      (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment
      ((OriginalKCombReceiptFeedback.bSelfSourceTrace observation nontrivial depth half).relationWords (R := ℤ)) =
      Finsupp.single
        ((material).1.expression.subst
          (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)) (1 : ℤ) -
      Finsupp.single ((material).2.1.1.subst
        (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)) (1 : ℤ) :=
  (OriginalKCombReceiptFeedback.bSelfSourceTrace observation nontrivial depth half).relation_boundary (R := ℤ)

theorem installed_bound_endpoint_price :
    ((material).2.1.1.subst
      (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)).eval
        (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment =
          -(receipt).fixedResidual • ConstantDual.seed := by
  have before : ((material).1.expression.subst
      (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)).eval
        (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment =
          -(receipt).fixedResidual • ConstantDual.seed := by
    rw [Expr.eval_subst]
    change (material).1.expression.eval (material).1.environment = _
    rw [(installed_source_raw observation nontrivial half depth).1,
      (installed_source_raw observation nontrivial half depth).2, Semantics.cotest_code_eval]
    exact (installed_source_calculated_value observation nontrivial half depth).symm.trans
      (installed_source_value observation nontrivial half depth)
  exact (OriginalKCombReceiptFeedback.bSelfSourceTrace observation nontrivial depth half).sound.symm.trans before

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "installed_bound_source_relation"

private theorem original_constant_ne_zero : (ConstantDual.seed : BurnolL2) ≠ 0 := by
  intro zero
  have read := congrArg burnolQuarterRestriction zero
  rw [map_zero] at read
  exact intervalConstant_ne_zero (by norm_num : (0 : ℝ) < 1/4)
    (by simpa only [ConstantDual.seed, burnolQuarterRestriction_zeroExtension] using read)

/-- This is a faithful value read, not a zero premise for the source calculation. -/
theorem installed_source_value_zero_iff :
    (material).2.2.1 = 0 ↔ (receipt).fixedResidual = 0 := by
  rw [installed_source_value]
  constructor
  · intro zero
    exact neg_eq_zero.mp ((smul_eq_zero.mp zero).resolve_right original_constant_ne_zero)
  · intro zero
    simp only [zero, neg_zero, zero_smul]

/-- The installed cotest, original full R price, physical fee and common born quotient share one root. -/
theorem actual_coefficient_source_on_original_whole_next (ordinal : Nat) :
    type_of% (actual_B_R_source_on_original_whole_next observation nontrivial half depth ordinal) ∧
    type_of% (runtimeCoefficientBSelfCalculationReadoutAt_factorizes observation nontrivial depth half) ∧
    ((material).2.2.1 = -(receipt).fixedResidual • ConstantDual.seed) ∧
    type_of% (installed_bound_source_relation observation nontrivial half depth) ∧
    type_of% (installed_bound_endpoint_price observation nontrivial half depth) ∧
    (calculatedSourceNormal c h = sourceCore c h + compactCorrection c h) ∧
    (inner ℂ (receipt).kernel (compactCorrection c h) = 0) ∧
    (inner ℂ (OriginalKFullAdjointSource.sourceAdjointField c) (calculatedBoundaryInput c h) +
      inner ℂ (receipt).kernel (rawBoundaryJump c h) = -(receipt).fixedResidual) ∧
    (((receipt).boundary h : BurnolL2) =
      (burnolEvenAmbientProjection (calculatedSourceNormal c h) : BurnolL2)) ∧
    (calculatedSourceNormal c h - ((receipt).boundary h : BurnolL2) = sourceProjectionLoss c h) ∧
    (‖calculatedSourceNormal c h‖^2 = ‖((receipt).boundary h : BurnolL2)‖^2 +
      ‖sourceProjectionLoss c h‖^2) ∧
    type_of% (OriginalKBFiniteCalculation.BornProjection.completion_projection_square
      observation nontrivial half depth ordinal) ∧
    ∀ word, type_of% (OriginalKBFiniteCalculation.BornProjection.complete_source_relations_target_kernel
      observation nontrivial half depth ordinal word) := by
  have source := installed_receipt_source observation nontrivial half
  have physical := OriginalKBFiniteCalculation.MaterialConsumer.installed_original_receipt_reads
    observation nontrivial half depth ordinal
  have boundary := physical.2.2.1
  have loss := physical.2.2.2.1
  have energy := physical.2.2.2.2
  have originalValue := OriginalKBFiniteCalculation.MaterialConsumer.installed_source_value
    observation nontrivial half depth
  rw [originalValue] at boundary loss energy
  have compact : inner ℂ (receipt).kernel (compactCorrection c h) = 0 := by
    rw [source.1, sourceKernel_original]
    exact compactCorrection_physical_cotest c h (burnolCompletedMellinRieszVector c)
  have price : inner ℂ (OriginalKFullAdjointSource.sourceAdjointField c) (calculatedBoundaryInput c h) +
      inner ℂ (receipt).kernel (rawBoundaryJump c h) = -(receipt).fixedResidual := by
    rw [source.1, sourceKernel_original, original_R_H_input_jump_price c h fixed_nonnegative,
      source.2, original_fixedResidual_core c observation.mathlibZero h fixed_nonnegative rfl, neg_neg]
  exact ⟨actual_B_R_source_on_original_whole_next observation nontrivial half depth ordinal,
    runtimeCoefficientBSelfCalculationReadoutAt_factorizes observation nontrivial depth half,
    installed_source_value observation nontrivial half depth,
    installed_bound_source_relation observation nontrivial half depth,
    installed_bound_endpoint_price observation nontrivial half depth,
    calculated_normal_full_inventory c h fixed_nonnegative, compact, price, boundary, loss, energy,
    OriginalKBFiniteCalculation.BornProjection.completion_projection_square observation nontrivial half depth ordinal,
    OriginalKBFiniteCalculation.BornProjection.complete_source_relations_target_kernel
      observation nontrivial half depth ordinal⟩

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_coefficient_source_on_original_whole_next"

end OriginalKCoefficientBSelfCalculation.MaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
