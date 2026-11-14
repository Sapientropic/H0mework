import H0mework.Versions.Y.Realization.Completion.FaithfulInstallation
import H0mework.Realization.Perfectification.FiniteCompressionNoGo
import H0mework.Arithmetic.PrimeShadow.LivingLawRootSourceNativeAuthorityRegression

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalFaithfulSettlementFaceRegression

open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalHistorySettlementFace
open CofinalFaithfulSettlementFace
open CofinalFaithfulSettlementFace.RootGeneratedCofinalFaithfulSettlementStepAt
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CofinalPerfectCompressionNoGo
open SourceNativeRootAuthorityRegression
open SourceNativeLedgerCompilerRegression

noncomputable section

abbrev N := SourceNativeLedgerCompilerRegression.N
abbrev V := SourceNativeLedgerCompilerRegression.V
abbrev BaseSource :=
  SourceNativeRootAuthorityRegression.RestructuringSource.toLedgerSource

/-! ## One source history, two actual carrier readouts -/

def relationEvent : PresentedRelationEventAt Empty :=
  .relation 0

abbrev historyLaw : SourceNativeCofinalHistoryMaterialLaw BaseSource :=
  SourceNativeCofinalHistoryMaterialLaw.create Empty
    (fun occurrence =>
      .occur occurrence (.singleton (RootedAccountedUnfolding.zero occurrence)))
    (fun _occurrence => rfl)
    (fun _occurrence => RootedAccountedUnfolding.zero relationEvent)
    (fun _occurrence => RootedAccountedUnfolding.zero (fun _event =>
      RootedAccountedUnfolding.zero relationEvent))

/-- Two source actions with the same occurrence and history but different
generator evaluations remain distinguishable in the raw projection. -/
abbrev unitHistoryLaw : SourceNativeCofinalHistoryMaterialLaw BaseSource :=
  SourceNativeCofinalHistoryMaterialLaw.create Unit
    (fun occurrence =>
      .occur occurrence (.singleton (RootedAccountedUnfolding.zero occurrence)))
    (fun _occurrence => rfl)
    (fun _occurrence => RootedAccountedUnfolding.zero (.generator ()))
    (fun _occurrence => RootedAccountedUnfolding.zero (fun event =>
      RootedAccountedUnfolding.zero event))

def zeroUnitEvaluatorLaw : SourceNativeCofinalFaithfulMaterialLaw BaseSource Int :=
  SourceNativeCofinalFaithfulMaterialLaw.create unitHistoryLaw
    (fun _occurrence => RootedAccountedUnfolding.zero (fun _ : Unit => 0))

def oneUnitEvaluatorLaw : SourceNativeCofinalFaithfulMaterialLaw BaseSource Int :=
  SourceNativeCofinalFaithfulMaterialLaw.create unitHistoryLaw
    (fun _occurrence => RootedAccountedUnfolding.zero (fun _ : Unit => 1))

theorem distinct_evaluator_changes_source_projection
    {current : V.Current}
    (occurrence : BaseSource.source.toRootSource.actual.OccurrenceAt current) :
    (zeroUnitEvaluatorLaw.toProjectionLaw.project PUnit.unit occurrence PUnit.unit
      ).evaluator ≠
    (oneUnitEvaluatorLaw.toProjectionLaw.project PUnit.unit occurrence PUnit.unit
      ).evaluator := by
  intro equality
  have valueEquality := congrArg
    (fun evaluator : RootedAccountedUnfolding (Unit → Int) => evaluator.root ())
    equality
  change (0 : Int) = 1 at valueEquality
  norm_num at valueEquality

abbrev zeroMaterialLaw (Carrier : Type) [AddCommGroup Carrier] :
    SourceNativeCofinalFaithfulMaterialLaw BaseSource Carrier :=
  SourceNativeCofinalFaithfulMaterialLaw.create historyLaw
    (fun _occurrence => RootedAccountedUnfolding.zero (fun _ => 0))

def zeroAuthority (Carrier : Type) [AddCommGroup Carrier] :
    SourceNativeAuthoritySource N V where
  restructuringSource := SourceNativeRootAuthorityRegression.RestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal RestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := questionWorld.source.lawSurface
  projectionLaw := (zeroMaterialLaw Carrier).toProjectionLaw

def zeroLivingSource (Carrier : Type) [AddCommGroup Carrier] :
    SourceNativeLivingAuthoritySource N V where
  base := zeroAuthority Carrier
  terminalHandoff := (zeroAuthority Carrier).emptyFaithfulTerminalHandoff
    (fun _current => by
      change IsEmpty PEmpty
      infer_instance)

def zeroRoot (Carrier : Type) [AddCommGroup Carrier] :
    SourceNativeLivingRootClosure N V where
  source := zeroLivingSource Carrier
  emitted := questionWorld.emitted
  compiler_commutes := questionWorld.compiler_commutes

def zeroVisit (Carrier : Type) [AddCommGroup Carrier] :
    SourceNativeTemporalVisitAt
      (zeroRoot Carrier).toAuthoritativeRoot.toLedgerRoot :=
  .finite (zeroRoot Carrier).toAuthoritativeRoot.toRoot.initialVisit

def zeroRecognition (Carrier : Type) [AddCommGroup Carrier] :
    SourceNativeCofinalFaithfulRecognitionAt Carrier (zeroRoot Carrier) :=
  SourceNativeCofinalFaithfulRecognitionAt.create
    (zeroMaterialLaw Carrier)
    (SourceNativeProjectionLaw.InstallationAt.refl
      (zeroMaterialLaw Carrier).toProjectionLaw)

abbrev zeroStep (Carrier : Type) [AddCommGroup Carrier] :
    RootGeneratedCofinalFaithfulSettlementStepAt
      (zeroRecognition Carrier) (zeroVisit Carrier) :=
  (zeroRecognition Carrier).generateStepAt (zeroVisit Carrier)

theorem history_relationClosure_bot (Carrier : Type)
    [AddCommGroup Carrier] :
    (zeroStep Carrier).history.relationClosure =
      (⊥ : Submodule ℤ (Empty →₀ ℤ)) := by
  apply bot_unique
  refine iSup_le fun stage => ?_
  intro relation _relation_mem
  rw [Submodule.mem_bot]
  ext generator
  exact Empty.elim generator

theorem history_compact_zero (Carrier : Type)
    [AddCommGroup Carrier] :
    (zeroStep Carrier).history.CompactAt 0 := by
  apply ((zeroStep Carrier).history.compactAt_iff_presentedEpi 0).mpr
  apply ((zeroStep Carrier).history.stageGeneratorToCompletion_surjective_iff_presentedEpi
    0).mp
  intro value
  refine ⟨0, ?_⟩
  symm
  refine Submodule.Quotient.induction_on
    (p := (zeroStep Carrier).history.relationInGeneratorClosure) value ?_
  intro representative
  have representative_eq_zero : representative = 0 := by
    apply Subtype.ext
    ext generator
    exact Empty.elim generator
  subst representative
  rfl

theorem history_completion_subsingleton (Carrier : Type)
    [AddCommGroup Carrier] :
    Subsingleton (zeroStep Carrier).history.CompletionCarrier := by
  have source_subsingleton :
      Subsingleton ((zeroStep Carrier).history.generatorStage 0) := by
    constructor
    intro left right
    apply Subtype.ext
    ext generator
    exact Empty.elim generator
  have presented_surjective :
      Function.Surjective
        ((zeroStep Carrier).history.stageGeneratorToCompletion 0) :=
    ((zeroStep Carrier).history.stageGeneratorToCompletion_surjective_iff_presentedEpi
      0).mpr
      (((zeroStep Carrier).history.compactAt_iff_presentedEpi 0).mp
        (history_compact_zero Carrier))
  constructor
  intro left right
  obtain ⟨leftSource, left_eq⟩ := presented_surjective left
  obtain ⟨rightSource, right_eq⟩ := presented_surjective right
  rw [← left_eq, ← right_eq]
  exact congrArg ((zeroStep Carrier).history.stageGeneratorToCompletion 0)
    (source_subsingleton.elim _ _)

theorem zero_relationsSound (Carrier : Type)
    [AddCommGroup Carrier] :
    (zeroStep Carrier).faithful.RelationsSound := by
  intro relation relation_mem
  have relation_zero : relation = 0 := by
    have relation_bot : relation ∈
        (⊥ : Submodule ℤ (Empty →₀ ℤ)) := by
      rw [← history_relationClosure_bot Carrier]
      exact relation_mem
    exact (Submodule.mem_bot ℤ).mp relation_bot
  subst relation
  rw [LinearMap.mem_ker]
  exact map_zero _

/-! The public positive consumer uses the classifier directly. -/
theorem unit_settles_faithfully :
    ∃ soundness : GeneratedRelationSoundnessAt (zeroStep Unit).faithful,
      ∃ coverage : GeneratedCoverageResidualZeroAt
          (zeroStep Unit).faithful soundness,
        ∃ realization : GeneratedFaithfulRealizationAt
            (zeroStep Unit).faithful soundness coverage,
          (zeroStep Unit).settlement =
            .faithful soundness coverage realization := by
  have soundness : GeneratedRelationSoundnessAt (zeroStep Unit).faithful :=
    by
      cases h : (zeroStep Unit).faithful.settleRelations with
      | sound token => exact token
      | unsound obstruction =>
          exact False.elim (obstruction.notSound (zero_relationsSound Unit))
  have completion_subsingleton :
      Subsingleton (zeroStep Unit).history.CompletionCarrier :=
    history_completion_subsingleton Unit
  have coverage_vanishes :
      (zeroStep Unit).faithful.CoverageResidualVanishes soundness := by
    constructor
    · apply le_antisymm
      · intro value value_mem
        rw [Submodule.mem_bot]
        exact completion_subsingleton.elim _ _
      · exact bot_le
    · constructor
      intro left right
      refine Submodule.Quotient.induction_on
        (p := LinearMap.range
          ((zeroStep Unit).faithful.completionEvaluation soundness)) left ?_
      intro leftValue
      refine Submodule.Quotient.induction_on
        (p := LinearMap.range
          ((zeroStep Unit).faithful.completionEvaluation soundness)) right ?_
      intro rightValue
      have left_zero : leftValue = 0 := Subsingleton.elim _ _
      have right_zero : rightValue = 0 := Subsingleton.elim _ _
      subst leftValue
      subst rightValue
      rfl
  generalize outcome_eq : (zeroStep Unit).settlement = outcome
  cases outcome with
  | faithful soundness' coverage' realization' =>
      exact ⟨soundness', coverage', realization', rfl⟩
  | unsound obstruction =>
      exact False.elim (obstruction.notSound (zero_relationsSound Unit))
  | uncovered soundness' obstruction =>
      exact False.elim (obstruction.persists coverage_vanishes)

theorem unit_generates_quotient_equivalence :
    Nonempty ((zeroStep Unit).history.CompletionCarrier ≃ₗ[ℤ] Unit) := by
  obtain ⟨soundness, coverage, realization, _settled⟩ :=
    unit_settles_faithfully
  exact ⟨realization.canonicalQuotientEquiv⟩

theorem unit_bridge_mouth :
    (zeroStep Unit).faithful.root = (zeroStep Unit).history.root ∧
      HEq (zeroStep Unit).wholeLedgerWriteBack
        ((zeroRoot Unit).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (zeroVisit Unit).current) ∧
      (zeroStep Unit).nextCurrent = (zeroRoot Unit).generatedNextCurrentAt
        (zeroVisit Unit) ∧
      HEq
        ((zeroRoot Unit).source.base.projectionLaw.outcomeAt
          ((zeroRecognition Unit).installation.embed PUnit.unit)
          (zeroStep Unit).sourceOccurrence)
        ((zeroRecognition Unit).materialLaw.toProjectionLaw.outcomeAt
          PUnit.unit (zeroStep Unit).sourceOccurrence) :=
  ⟨(zeroStep Unit).faithful_root_eq_history_root,
    (zeroStep Unit).wholeLedgerWriteBack_eq_root,
    (zeroStep Unit).nextCurrent_eq_root,
    (zeroStep Unit).installedFaithful_factorizes⟩

/-! ## Infinite-rank coverage residual -/

theorem infinite_rank_relationsSound :
    (zeroStep (Finsupp Nat Int)).faithful.RelationsSound :=
  zero_relationsSound (Finsupp Nat Int)

theorem infinite_rank_completion_subsingleton :
    Subsingleton
      (zeroStep (Finsupp Nat Int)).history.CompletionCarrier :=
  history_completion_subsingleton (Finsupp Nat Int)

theorem infinite_rank_coverage_not_vanishes
    (soundness : GeneratedRelationSoundnessAt
      (zeroStep (Finsupp Nat Int)).faithful) :
    ¬ (zeroStep (Finsupp Nat Int)).faithful.CoverageResidualVanishes soundness := by
  intro coverage
  letI : Subsingleton
      (zeroStep (Finsupp Nat Int)).history.CompletionCarrier :=
    infinite_rank_completion_subsingleton
  have range_zero :
      LinearMap.range
        ((zeroStep (Finsupp Nat Int)).faithful.completionEvaluation soundness) = ⊥ := by
    apply le_antisymm
    · rintro value ⟨sourceValue, rfl⟩
      rw [Submodule.mem_bot]
      have source_zero : sourceValue = 0 := Subsingleton.elim _ _
      subst sourceValue
      exact map_zero _
    · exact bot_le
  let nonzero : Finsupp Nat Int := Finsupp.single 0 1
  have class_ne :
      (Submodule.Quotient.mk nonzero :
        (zeroStep (Finsupp Nat Int)).faithful.CokernelResidual soundness) ≠ 0 := by
    intro equality
    have mem := (Submodule.Quotient.eq
      (LinearMap.range
        ((zeroStep (Finsupp Nat Int)).faithful.completionEvaluation soundness))).mp
      equality
    rw [range_zero] at mem
    rw [Submodule.mem_bot] at mem
    change nonzero - 0 = 0 at mem
    rw [sub_zero] at mem
    simp [nonzero] at mem
  exact class_ne (coverage.2.elim _ _)

theorem infinite_rank_explicit_class
    (soundness : GeneratedRelationSoundnessAt
      (zeroStep (Finsupp Nat Int)).faithful) :
    (Submodule.Quotient.mk (Finsupp.single 0 1) :
      (zeroStep (Finsupp Nat Int)).faithful.CokernelResidual soundness) ≠ 0 := by
  intro equality
  letI : Subsingleton
      (zeroStep (Finsupp Nat Int)).history.CompletionCarrier :=
    infinite_rank_completion_subsingleton
  have range_zero :
      LinearMap.range
        ((zeroStep (Finsupp Nat Int)).faithful.completionEvaluation soundness) = ⊥ := by
    apply le_antisymm
    · rintro value ⟨sourceValue, rfl⟩
      rw [Submodule.mem_bot]
      have source_zero : sourceValue = 0 := Subsingleton.elim _ _
      subst sourceValue
      exact map_zero _
    · exact bot_le
  have mem := (Submodule.Quotient.eq
    (LinearMap.range
      ((zeroStep (Finsupp Nat Int)).faithful.completionEvaluation soundness))).mp
    equality
  rw [range_zero] at mem
  rw [Submodule.mem_bot] at mem
  change (Finsupp.single 0 1 : Finsupp Nat Int) - 0 = 0 at mem
  rw [sub_zero] at mem
  simp at mem

theorem infinite_rank_settles_uncovered :
    ∃ soundness : GeneratedRelationSoundnessAt
        (zeroStep (Finsupp Nat Int)).faithful,
      ∃ obstruction : GeneratedCoverageResidualObstructionAt
          (zeroStep (Finsupp Nat Int)).faithful soundness,
        (zeroStep (Finsupp Nat Int)).settlement =
          .uncovered soundness obstruction := by
  generalize outcome_eq : (zeroStep (Finsupp Nat Int)).settlement = outcome
  cases outcome with
  | faithful soundness coverage realization =>
      exact False.elim (infinite_rank_coverage_not_vanishes soundness
        coverage.vanishes)
  | unsound obstruction =>
      exact False.elim (obstruction.notSound infinite_rank_relationsSound)
  | uncovered soundness obstruction =>
      exact ⟨soundness, obstruction, rfl⟩

theorem infinite_rank_residual_disposition :
    ∃ soundness : GeneratedRelationSoundnessAt
        (zeroStep (Finsupp Nat Int)).faithful,
      ∃ obstruction : GeneratedCoverageResidualObstructionAt
          (zeroStep (Finsupp Nat Int)).faithful soundness,
        ∃ coordinate : GeneratedCoverageResidualCoordinateAt
            (zeroStep (Finsupp Nat Int)).faithful soundness,
          (zeroStep (Finsupp Nat Int)).residualDisposition =
              .coverageResidual soundness obstruction coordinate ∧
            coordinate.coordinate ≠ 0 ∧
            coordinate.representative ∉
              LinearMap.range
                ((zeroStep (Finsupp Nat Int)).faithful.completionEvaluation
                  soundness) := by
  generalize outcome_eq : (zeroStep (Finsupp Nat Int)).residualDisposition = outcome
  cases outcome with
  | faithful soundness coverage realization =>
      exact False.elim (infinite_rank_coverage_not_vanishes soundness
        coverage.vanishes)
  | unsound obstruction coordinate =>
      exact False.elim (obstruction.notSound infinite_rank_relationsSound)
  | kernelResidual soundness obstruction coordinate =>
      have coordinate_zero :
          (coordinate.coordinate :
            (zeroStep (Finsupp Nat Int)).history.CompletionCarrier) = 0 := by
        letI : Subsingleton
            (zeroStep (Finsupp Nat Int)).history.CompletionCarrier :=
          infinite_rank_completion_subsingleton
        exact Subsingleton.elim _ _
      exact False.elim (coordinate.coordinate_ne_zero coordinate_zero)
  | coverageResidual soundness obstruction coordinate =>
      exact ⟨soundness, obstruction, coordinate, outcome_eq ▸ rfl,
        coordinate.coordinate_ne_zero,
        coordinate.representative_not_mem_range⟩

theorem infinite_rank_negative_branch :
    ¬ Module.Finite Int (Finsupp Nat Int) ∧
      ∃ soundness : GeneratedRelationSoundnessAt
          (zeroStep (Finsupp Nat Int)).faithful,
        (Submodule.Quotient.mk (Finsupp.single 0 1) :
          (zeroStep (Finsupp Nat Int)).faithful.CokernelResidual soundness) ≠ 0 := by
  obtain ⟨soundness, _obstruction, _settled⟩ :=
    infinite_rank_settles_uncovered
  exact ⟨natFinsupp_not_moduleFinite, soundness,
    infinite_rank_explicit_class soundness⟩

example : True := by
  fail_if_success exact (zeroStep Unit).callerSettlement
  fail_if_success exact (zeroStep Unit).callerFaithfulness
  fail_if_success exact (zeroStep Unit).callerWholeLedger
  fail_if_success exact (zeroStep Unit).callerNext
  exact True.intro

#print axioms SourceNativeCofinalFaithfulMaterialLaw.toProjectionLaw
#print axioms RootGeneratedCofinalFaithfulSettlementStepAt.sourceFreeEvaluation_single
#print axioms distinct_evaluator_changes_source_projection
#print axioms RootGeneratedCofinalFaithfulSettlementStepAt.installedFaithful_factorizes
#print axioms unit_settles_faithfully
#print axioms unit_bridge_mouth
#print axioms infinite_rank_settles_uncovered
#print axioms infinite_rank_explicit_class
#print axioms infinite_rank_residual_disposition
#print axioms infinite_rank_negative_branch

end
end CofinalFaithfulSettlementFaceRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
