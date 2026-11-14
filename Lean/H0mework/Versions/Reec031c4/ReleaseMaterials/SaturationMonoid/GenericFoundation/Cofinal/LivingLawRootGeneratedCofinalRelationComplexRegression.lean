import H0mework.Versions.R453de275.Realization.Perfectification.Cofinal.LivingLawRootGeneratedCofinalRelationComplexKernel
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.LivingLawRootGeneratedCofinalHistorySettlementRegression
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.LivingLawRootGeneratedCofinalHistoryCochainCommonOccurrenceRegression

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalRelationGeneratedComplexRegression

open CategoryTheory
open CofinalRelationGeneratedComplex
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CochainRelationPresentation

noncomputable section

namespace PositiveSource

open CofinalHistoryCochainCommonOccurrenceRegression
open CofinalHistorySettlementRegression
open SourceNativeRootAuthorityRegression

abbrev N := CofinalHistoryCochainCommonOccurrenceRegression.N
abbrev V := CofinalHistoryCochainCommonOccurrenceRegression.V

def historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw
    BaseSource :=
  CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw.create Bool
    (fun occurrence =>
      .occur occurrence (.singleton (RootedAccountedUnfolding.zero occurrence)))
    (fun _occurrence => rfl)
    (fun _occurrence => quotientStableSeed)
    (fun _occurrence => quotientStableContinuationOccurrence)

def commonLaw := ofHistoryCommonLaw historyLaw

def authority : SourceNativeAuthoritySource N V where
  restructuringSource := RestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal RestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := questionWorld.source.lawSurface
  projectionLaw := commonLaw.toProjectionLaw

def living : SourceNativeLivingAuthoritySource N V where
  base := authority
  terminalHandoff := authority.emptyFaithfulTerminalHandoff
    (fun _current => by
      change IsEmpty PEmpty
      infer_instance)

def root : SourceNativeLivingRootClosure N V where
  source := living
  emitted := questionWorld.emitted
  compiler_commutes := questionWorld.compiler_commutes

def visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot :=
  .finite root.toAuthoritativeRoot.toRoot.initialVisit

def installation : SourceNativeProjectionLaw.InstallationAt
    historyLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.refl historyLaw.toProjectionLaw

def step := ofHistoryStep (root := root) historyLaw installation visit

theorem source_root_ledger_next :
    step.history.seed =
        (historyLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).seed ∧
      step.history.actualContinuation =
        (historyLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).continuation.root ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (installation.embed PUnit.unit) step.sourceOccurrence)
        (historyLaw.toProjectionLaw.outcomeAt PUnit.unit step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ofHistoryStep_source_root_ledger_next (root := root) historyLaw installation visit

theorem source_d_squared
    (value : (step.cochainFace.termPresentation (-1)).cokernel) :
    FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
        (step.cochainFace.termPresentation 1)
        (step.cochainFace.differentialPresentedMap 0 1
          (step.cochainFace.differentialPresentedMap (-1) 0 value)) = 0 :=
  ofHistoryStep_consumes_generated_d_squared (root := root)
    historyLaw installation visit value

theorem fixed_root_relation_true_mem_closure :
    Finsupp.single true (1 : ℤ) ∈ step.history.relationClosure := by
  have sameEvents : step.history.observedEvents 1 =
      quotientStableFace.observedEvents 1 := by
    rfl
  apply step.history.relationStage_le_closure 1
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation (Finsupp.single true 1) ∈
    step.history.observedEvents 1
  have eventMem : PresentedRelationEventAt.relation (Finsupp.single true 1) ∈
      quotientStableFace.observedEvents 1 := by
    rw [quotientStable_observedEvents_one]
    simp
  rw [sameEvents]
  exact eventMem

theorem fixed_root_relation_differential_ne_zero :
    (natComplex step.history).d 0 1 ≠ 0 := by
  let relation : step.history.relationClosure :=
    ⟨Finsupp.single true 1, fixed_root_relation_true_mem_closure⟩
  intro zero
  have vanish := congrArg
    (fun f : (natComplex step.history).X 0 ⟶
        (natComplex step.history).X 1 => f.hom relation) zero
  rw [natComplex_d_zero_one] at vanish
  have value_zero : (Finsupp.single true (1 : ℤ) : Bool →₀ ℤ) = 0 :=
    congrArg Subtype.val vanish
  have at_true := congrArg (fun f : Bool →₀ ℤ => f true) value_zero
  norm_num at at_true

theorem true_generator_is_in_fixed_root_history :
    true ∈ step.history.generatorSupport 1 := by
  have sameSupport : step.history.generatorSupport 1 =
      quotientStableFace.generatorSupport 1 := by
    rfl
  rw [sameSupport, quotientStable_support_one]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self true)

theorem fixed_root_actual_evaluator_ne_zero :
    sourceEvaluator step.history true ≠ 0 := by
  intro vanish
  have read := sourceEvaluator_reads_actual_generator step.history 1 true
    true_generator_is_in_fixed_root_history
  rw [vanish, map_zero] at read
  have value_zero : (Finsupp.single true (1 : ℤ) : Bool →₀ ℤ) = 0 :=
    congrArg Subtype.val read.symm
  have at_true := congrArg (fun f : Bool →₀ ℤ => f true) value_zero
  norm_num at at_true

theorem fixed_root_relation_image_nonzero :
    step.faithful.freeEvaluation (Finsupp.single true (1 : ℤ)) ≠ 0 := by
  have image : step.faithful.freeEvaluation (Finsupp.single true (1 : ℤ)) =
      sourceEvaluator step.history true := by
    have single := step.faithful.freeEvaluation_single true (1 : ℤ)
    change step.faithful.freeEvaluation (Finsupp.single true (1 : ℤ)) =
      (1 : ℤ) • sourceEvaluator step.history true at single
    simpa only [one_smul] using single
  rw [image]
  exact fixed_root_actual_evaluator_ne_zero

theorem fixed_root_relations_unsound :
    ¬ step.faithful.RelationsSound := by
  intro sound
  have killed := sound fixed_root_relation_true_mem_closure
  change step.faithful.freeEvaluation (Finsupp.single true (1 : ℤ)) = 0 at killed
  exact fixed_root_relation_image_nonzero killed

theorem fixed_root_settleRelations_unsound :
    ∃ obstruction : CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.GeneratedUnsoundRelationObstructionAt
        step.faithful,
      step.faithful.settleRelations = .unsound obstruction := by
  cases settled : step.faithful.settleRelations with
  | sound soundness =>
      exact False.elim (fixed_root_relations_unsound soundness.sound)
  | unsound obstruction =>
      exact ⟨obstruction, rfl⟩

/-- The original residual consumer keeps the nonzero relation image and the
same fixed-root ledger/next; no sound completion map is assumed. -/
theorem fixed_root_full_residual_ledger_next :
    ∃ (obstruction : CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.GeneratedUnsoundRelationObstructionAt
        step.faithful)
      (coordinate : CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.GeneratedRelationResidualCoordinateAt
        step.faithful),
      step.faithful.settleWithResidual = .unsound obstruction coordinate ∧
      coordinate.coordinate ≠ 0 ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit := by
  cases disposition_eq : step.faithful.settleWithResidual with
  | faithful soundness _ _ =>
      exact False.elim (fixed_root_relations_unsound soundness.sound)
  | unsound obstruction coordinate =>
      exact ⟨obstruction, coordinate, rfl, coordinate.coordinate_ne_zero,
        step.wholeLedgerWriteBack_eq_root, step.nextCurrent_eq_root⟩
  | kernelResidual soundness _ _ =>
      exact False.elim (fixed_root_relations_unsound soundness.sound)
  | coverageResidual soundness _ _ =>
      exact False.elim (fixed_root_relations_unsound soundness.sound)

end PositiveSource

end

open CofinalHistorySettlementRegression

theorem actual_relation_generates_nonzero_differential :
    (natComplex quotientStableFace).d 0 1 ≠ 0 := by
  intro zero
  let relation : quotientStableFace.relationClosure :=
    ⟨Finsupp.single true 1, quotientStable_relation_true_mem_closure⟩
  have vanish := congrArg
    (fun f : (natComplex quotientStableFace).X 0 ⟶
        (natComplex quotientStableFace).X 1 => f.hom relation) zero
  rw [natComplex_d_zero_one] at vanish
  have value_zero : (Finsupp.single true (1 : ℤ) : Bool →₀ ℤ) = 0 :=
    congrArg Subtype.val vanish
  have at_true := congrArg (fun f : Bool →₀ ℤ => f true) value_zero
  norm_num at at_true

#print axioms completion_zero_iff_generated_boundary
#print axioms sourceEvaluator_reads_actual_generator
#print axioms ofHistory_reads_original_projection
#print axioms ofHistoryStep_source_root_ledger_next
#print axioms ofHistoryStep_consumes_generated_d_squared
#print axioms PositiveSource.fixed_root_relation_differential_ne_zero
#print axioms PositiveSource.fixed_root_relation_image_nonzero
#print axioms PositiveSource.fixed_root_relations_unsound
#print axioms PositiveSource.fixed_root_settleRelations_unsound
#print axioms PositiveSource.fixed_root_full_residual_ledger_next


end CofinalRelationGeneratedComplexRegression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
