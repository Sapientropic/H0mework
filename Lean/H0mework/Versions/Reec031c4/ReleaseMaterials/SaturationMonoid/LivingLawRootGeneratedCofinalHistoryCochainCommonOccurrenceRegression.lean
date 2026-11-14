import H0mework.Versions.Rb81a4438.Realization.Completion.CommonCochainOccurrence
import H0mework.Arithmetic.PrimeShadow.LivingLawRootSourceNativeAuthorityRegression

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryCochainCommonOccurrenceRegression

open CofinalHistorySettlement
open CofinalHistorySettlementFace
open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainCommonOccurrence.RootGeneratedCofinalHistoryCochainCommonStepAt
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CochainRelationPresentation
open DerivedAdicCofiber
open FiniteAdditiveRelationPresentation
open SourceNativeRootAuthorityRegression
open SourceNativeLedgerCompilerRegression

noncomputable section

abbrev N := SourceNativeLedgerCompilerRegression.N
abbrev V := SourceNativeLedgerCompilerRegression.V
abbrev BaseSource := RestructuringSource.toLedgerSource

def zeroComplex : IntegralCochainComplex ℤ := HomologicalComplex.zero

def relationEvent : PresentedRelationEventAt Empty := .relation 0

def historyLaw : SourceNativeCofinalHistoryMaterialLaw BaseSource :=
  SourceNativeCofinalHistoryMaterialLaw.create Empty
    (fun occurrence =>
      .occur occurrence (.singleton (RootedAccountedUnfolding.zero occurrence)))
    (fun _occurrence => rfl)
    (fun _occurrence => RootedAccountedUnfolding.zero relationEvent)
    (fun _occurrence => RootedAccountedUnfolding.zero (fun _ =>
      RootedAccountedUnfolding.zero relationEvent))

def commonLaw : SourceNativeCofinalHistoryCochainMaterialLaw BaseSource :=
  SourceNativeCofinalHistoryCochainMaterialLaw.create historyLaw
    (fun _occurrence => RootedAccountedUnfolding.zero zeroComplex)
    (fun _occurrence => RootedAccountedUnfolding.zero (fun generator =>
      Empty.elim generator))

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

def visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot :=
  .finite root.toAuthoritativeRoot.toRoot.initialVisit

def recognition : SourceNativeCofinalHistoryCochainRecognitionAt root :=
  SourceNativeCofinalHistoryCochainRecognitionAt.create commonLaw
    (SourceNativeProjectionLaw.InstallationAt.refl commonLaw.toProjectionLaw)

abbrev step : RootGeneratedCofinalHistoryCochainCommonStepAt
    recognition visit := recognition.generateStepAt visit

theorem common_disposition_is_total :
    Nonempty (CommonDisposition step) :=
  step.disposition_is_total

theorem sibling_roots_are_the_same_occurrence :
    step.history.root = step.cochainFace.root ∧
      step.faithful.root = step.history.root :=
  ⟨step.history_root_eq_cochain_root,
    step.faithful_root_eq_history_root⟩

theorem cochain_square_is_consumed
    (value : (step.cochainFace.termPresentation 0).cokernel) :
    finiteAdditiveRelationPresentation_cokernelEquiv _
        (step.cochainFace.termPresentation 2)
        (step.cochainFace.differentialPresentedMap 1 2
          (step.cochainFace.differentialPresentedMap 0 1 value)) = 0 :=
  step.cochain_d_squared 0 1 2 value

theorem common_step_preserves_root_ledger_next :
    HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (recognition.installation.embed PUnit.unit) step.sourceOccurrence)
        (recognition.materialLaw.toProjectionLaw.outcomeAt
          PUnit.unit step.sourceOccurrence) :=
  ⟨step.wholeLedgerWriteBack_eq_root,
    step.nextCurrent_eq_root,
    step.installedCochain_factorizes⟩

theorem common_source_action_is_root_installed :
    step.history.seed =
        (recognition.materialLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).seed ∧
      step.history.actualContinuation =
        (recognition.materialLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).continuation.root ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (recognition.installation.embed PUnit.unit) step.sourceOccurrence)
        (recognition.materialLaw.toProjectionLaw.outcomeAt
          PUnit.unit step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  step.sourceHistoryAction_root_ledger_next

example : True := by
  fail_if_success exact step.callerHistoryEquivalence
  fail_if_success exact step.callerFaithfulEquivalence
  fail_if_success exact step.callerDeterminant
  fail_if_success exact step.callerSeparator
  exact True.intro

#print axioms common_disposition_is_total
#print axioms sibling_roots_are_the_same_occurrence
#print axioms cochain_square_is_consumed
#print axioms common_step_preserves_root_ledger_next
#print axioms common_source_action_is_root_installed

/-! ## Direct persistent-residual consumer on the same common face shape -/

namespace NegativeInfiniteRank

abbrev Carrier := Finsupp Nat Int
abbrev ZeroCarrier := Fin 0 → ℤ

def oneDegreeComplex : IntegralCochainComplex ℤ where
  X degree := if degree = 0 then ModuleCat.of ℤ Carrier
    else ModuleCat.of ℤ ZeroCarrier
  d _ _ := 0

def negativeRelationEvent : PresentedRelationEventAt Empty := .relation 0

def negativeHistoryLaw : SourceNativeCofinalHistoryMaterialLaw BaseSource :=
  SourceNativeCofinalHistoryMaterialLaw.create Empty
    (fun occurrence =>
      .occur occurrence (.singleton (RootedAccountedUnfolding.zero occurrence)))
    (fun _occurrence => rfl)
    (fun _occurrence => RootedAccountedUnfolding.zero negativeRelationEvent)
    (fun _occurrence => RootedAccountedUnfolding.zero (fun _ =>
      RootedAccountedUnfolding.zero negativeRelationEvent))

def negativeCommonLaw : SourceNativeCofinalHistoryCochainMaterialLaw BaseSource :=
  SourceNativeCofinalHistoryCochainMaterialLaw.create negativeHistoryLaw
    (fun _occurrence => RootedAccountedUnfolding.zero oneDegreeComplex)
    (fun _occurrence => RootedAccountedUnfolding.zero (fun _generator =>
      (0 : Carrier)))

def negativeAuthority : SourceNativeAuthoritySource N V where
  restructuringSource := RestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal RestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := questionWorld.source.lawSurface
  projectionLaw := negativeCommonLaw.toProjectionLaw

def negativeLiving : SourceNativeLivingAuthoritySource N V where
  base := negativeAuthority
  terminalHandoff := negativeAuthority.emptyFaithfulTerminalHandoff
    (fun _current => by
      change IsEmpty PEmpty
      infer_instance)

def negativeRoot : SourceNativeLivingRootClosure N V where
  source := negativeLiving
  emitted := questionWorld.emitted
  compiler_commutes := questionWorld.compiler_commutes

def negativeVisit : SourceNativeTemporalVisitAt
    negativeRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite negativeRoot.toAuthoritativeRoot.toRoot.initialVisit

def negativeRecognition : SourceNativeCofinalHistoryCochainRecognitionAt negativeRoot :=
  SourceNativeCofinalHistoryCochainRecognitionAt.create negativeCommonLaw
    (SourceNativeProjectionLaw.InstallationAt.refl negativeCommonLaw.toProjectionLaw)

abbrev negativeStep : RootGeneratedCofinalHistoryCochainCommonStepAt
    negativeRecognition negativeVisit := negativeRecognition.generateStepAt negativeVisit

theorem negative_relationClosure_bot : negativeStep.history.relationClosure =
    (⊥ : Submodule ℤ (Empty →₀ ℤ)) := by
  apply bot_unique
  refine iSup_le fun stage => ?_
  intro relation _relation_mem
  rw [Submodule.mem_bot]
  ext generator
  exact Empty.elim generator

theorem negative_completion_subsingleton :
    Subsingleton negativeStep.history.CompletionCarrier := by
  have source_subsingleton : Subsingleton (negativeStep.history.generatorStage 0) := by
    constructor
    intro left right
    apply Subtype.ext
    ext generator
    exact Empty.elim generator
  have compact_zero : negativeStep.history.CompactAt 0 := by
    apply (negativeStep.history.compactAt_iff_presentedEpi 0).mpr
    apply (negativeStep.history.stageGeneratorToCompletion_surjective_iff_presentedEpi
      0).mp
    intro value
    refine ⟨0, ?_⟩
    symm
    refine Submodule.Quotient.induction_on
      (p := negativeStep.history.relationInGeneratorClosure) value ?_
    intro representative
    have representative_eq_zero : representative = 0 := by
      apply Subtype.ext
      ext generator
      exact Empty.elim generator
    subst representative
    rfl
  have presented_surjective :
      Function.Surjective (negativeStep.history.stageGeneratorToCompletion 0) :=
    (negativeStep.history.stageGeneratorToCompletion_surjective_iff_presentedEpi
      0).mpr ((negativeStep.history.compactAt_iff_presentedEpi 0).mp compact_zero)
  constructor
  intro left right
  obtain ⟨leftSource, left_eq⟩ := presented_surjective left
  obtain ⟨rightSource, right_eq⟩ := presented_surjective right
  rw [← left_eq, ← right_eq]
  exact congrArg (negativeStep.history.stageGeneratorToCompletion 0)
    (source_subsingleton.elim _ _)

theorem negative_relations_sound : negativeStep.faithful.RelationsSound := by
  intro relation relation_mem
  have relation_zero : relation = 0 := by
    have relation_bot : relation ∈ (⊥ : Submodule ℤ (Empty →₀ ℤ)) := by
      rw [← negative_relationClosure_bot]
      exact relation_mem
    exact (Submodule.mem_bot ℤ).mp relation_bot
  subst relation
  rw [LinearMap.mem_ker]
  simp [RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation,
    RootGeneratedCofinalFaithfulRealizationAt.actualGeneratorEvaluator]

theorem negative_coverage_not_vanishes
    (soundness : GeneratedRelationSoundnessAt negativeStep.faithful) :
    ¬ negativeStep.faithful.CoverageResidualVanishes soundness := by
  intro coverage
  letI : Subsingleton negativeStep.history.CompletionCarrier :=
    negative_completion_subsingleton
  have range_zero :
      LinearMap.range (negativeStep.faithful.completionEvaluation soundness) = ⊥ := by
    apply le_antisymm
    · rintro value ⟨sourceValue, rfl⟩
      rw [Submodule.mem_bot]
      have source_zero : sourceValue = 0 := Subsingleton.elim _ _
      subst sourceValue
      exact map_zero _
    · exact bot_le
  let nonzero : Carrier := Finsupp.single 0 1
  have class_ne :
      (Submodule.Quotient.mk nonzero :
        negativeStep.faithful.CokernelResidual soundness) ≠ 0 := by
    intro equality
    have mem := (Submodule.Quotient.eq
      (LinearMap.range (negativeStep.faithful.completionEvaluation soundness))).mp
      equality
    rw [range_zero] at mem
    rw [Submodule.mem_bot] at mem
    change nonzero - 0 = 0 at mem
    rw [sub_zero] at mem
    simp [nonzero] at mem
  exact class_ne (coverage.2.elim _ _)

theorem negative_common_face_exposes_residual :
    ∃ soundness : GeneratedRelationSoundnessAt negativeStep.faithful,
      ∃ obstruction : GeneratedCoverageResidualObstructionAt
          negativeStep.faithful soundness,
        ∃ coordinate : GeneratedCoverageResidualCoordinateAt
            negativeStep.faithful soundness,
          negativeStep.faithful.settleWithResidual =
              .coverageResidual soundness obstruction coordinate ∧
            coordinate.coordinate ≠ 0 ∧
            coordinate.representative ∉
              LinearMap.range
                (negativeStep.faithful.completionEvaluation soundness) := by
  generalize outcome_eq : negativeStep.faithful.settleWithResidual = outcome
  cases outcome with
  | faithful soundness coverage realization =>
      exact False.elim (negative_coverage_not_vanishes soundness coverage.vanishes)
  | unsound obstruction coordinate =>
      exact False.elim (obstruction.notSound negative_relations_sound)
  | kernelResidual soundness obstruction coordinate =>
      have coordinate_zero :
          (coordinate.coordinate : negativeStep.history.CompletionCarrier) = 0 := by
        letI : Subsingleton negativeStep.history.CompletionCarrier :=
          negative_completion_subsingleton
        exact Subsingleton.elim _ _
      exact False.elim (coordinate.coordinate_ne_zero coordinate_zero)
  | coverageResidual soundness obstruction coordinate =>
      exact ⟨soundness, obstruction, coordinate, outcome_eq ▸ rfl,
        coordinate.coordinate_ne_zero,
        coordinate.representative_not_mem_range⟩

#print axioms negative_common_face_exposes_residual

end NegativeInfiniteRank

end
end CofinalHistoryCochainCommonOccurrenceRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
