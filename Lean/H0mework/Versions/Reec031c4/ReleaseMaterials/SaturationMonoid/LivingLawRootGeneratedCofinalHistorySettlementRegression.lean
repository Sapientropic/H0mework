import H0mework.Realization.Completion.HistorySettlement

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistorySettlementRegression

open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt

noncomputable section

def rootOccurrence : RootedAccountedUnfolding Unit :=
  RootedAccountedUnfolding.zero ()

def seedOccurrence :
    RootedAccountedUnfolding (PresentedRelationEventAt Empty) :=
  RootedAccountedUnfolding.zero (.relation 0)

def constantContinuation
    (_event : PresentedRelationEventAt Empty) :
    RootedAccountedUnfolding (PresentedRelationEventAt Empty) :=
  RootedAccountedUnfolding.zero (.relation 0)

def continuationOccurrence :
    RootedAccountedUnfolding
      (PresentedRelationEventAt Empty →
        RootedAccountedUnfolding (PresentedRelationEventAt Empty)) :=
  RootedAccountedUnfolding.zero constantContinuation

def face : RootGeneratedCofinalHistoryAt rootOccurrence
    seedOccurrence continuationOccurrence :=
  RootGeneratedCofinalHistoryAt.generate

theorem face_generatorStage_eq_bot (stage : Nat) :
    face.generatorStage stage = ⊥ := by
  apply le_bot_iff.mp
  intro value _value_mem
  rw [Submodule.mem_bot]
  ext generator
  exact Empty.elim generator

theorem face_generatorClosure_eq_bot :
    face.generatorClosure = ⊥ := by
  apply le_bot_iff.mp
  refine iSup_le fun stage => ?_
  rw [face_generatorStage_eq_bot stage]

theorem face_stageGeneratorToCompletion_zero_surjective :
    Function.Surjective (face.stageGeneratorToCompletion 0) := by
  intro value
  refine ⟨0, ?_⟩
  symm
  refine Submodule.Quotient.induction_on
    (p := face.relationInGeneratorClosure) value ?_
  intro representative
  have representative_eq_zero : representative = 0 := by
    apply Subtype.ext
    change (representative : Empty →₀ ℤ) = 0
    have representative_mem_bot :
        (representative : Empty →₀ ℤ) ∈
          (⊥ : Submodule ℤ (Empty →₀ ℤ)) := by
      rw [← face_generatorClosure_eq_bot]
      exact representative.property
    simpa only [Submodule.mem_bot] using representative_mem_bot
  subst representative
  rfl

theorem face_compactAt_zero : face.CompactAt 0 :=
  (face.compactAt_iff_presentedEpi 0).mpr
    ((face.stageGeneratorToCompletion_surjective_iff_presentedEpi 0).mp
      face_stageGeneratorToCompletion_zero_surjective)

theorem face_generates_perfectDeterminantUnit :
    ∃ (trace : GeneratedHistoricalCompactnessAt face)
      (readout : GeneratedCompactPerfectReadoutAt face trace),
      Nonempty
        (GradedIntegralDeterminantLine.CanonicalIntegralUnitTorsor
          readout.determinantState.integralLine) ∧
      Nonempty
        ((face.generatorStage trace.index ⧸
          LinearMap.ker (face.stageGeneratorToCompletion trace.index)) ≃ₗ[ℤ]
            face.CompletionCarrier) := by
  have generated := face.compactPerfectReadout_exists
    ⟨0, face_compactAt_zero⟩
  rcases generated with ⟨⟨trace, readout⟩⟩
  exact ⟨trace, readout, readout.determinantState_has_unitTorsor,
    readout.resolves_same_completion⟩

/-! ## Quotient compactness does not imply support stabilization -/

def quotientStableSeed :
    RootedAccountedUnfolding (PresentedRelationEventAt Bool) :=
  RootedAccountedUnfolding.zero (.generator false)

def quotientStableContinuation : PresentedRelationEventAt Bool →
    RootedAccountedUnfolding (PresentedRelationEventAt Bool)
  | .generator false =>
      .occur (.relation (Finsupp.single true 1))
        (.singleton (RootedAccountedUnfolding.zero (.generator true)))
  | _ => RootedAccountedUnfolding.zero (.generator true)

def quotientStableContinuationOccurrence :
    RootedAccountedUnfolding
      (PresentedRelationEventAt Bool →
        RootedAccountedUnfolding (PresentedRelationEventAt Bool)) :=
  RootedAccountedUnfolding.zero quotientStableContinuation

def quotientStableFace : RootGeneratedCofinalHistoryAt rootOccurrence
    quotientStableSeed quotientStableContinuationOccurrence :=
  RootGeneratedCofinalHistoryAt.generate

theorem quotientStable_observation_zero :
    quotientStableFace.observation 0 = quotientStableSeed :=
  rfl

theorem quotientStable_observation_one :
    quotientStableFace.observation 1 =
      .occur (.generator false)
        (.singleton <| .occur (.relation (Finsupp.single true 1))
          (.singleton (RootedAccountedUnfolding.zero (.generator true)))) :=
  rfl

theorem quotientStable_observedEvents_zero :
    quotientStableFace.observedEvents 0 = [.generator false] := by
  rw [RootGeneratedCofinalHistoryAt.observedEvents]
  change (quotientStableFace.observation 0).trace = [.generator false]
  rw [quotientStable_observation_zero]
  rfl

theorem quotientStable_observedEvents_one :
    quotientStableFace.observedEvents 1 =
      [.generator false, .generator false,
        .relation (Finsupp.single true 1), .generator true] := by
  rw [RootGeneratedCofinalHistoryAt.observedEvents]
  change (quotientStableFace.observation 0).trace ++
    (quotientStableFace.observation 1).trace = _
  rw [quotientStable_observation_zero, quotientStable_observation_one]
  rfl

theorem quotientStable_support_zero :
    quotientStableFace.generatorSupport 0 = {false} := by
  classical
  rw [RootGeneratedCofinalHistoryAt.generatorSupport,
    quotientStable_observedEvents_zero]
  simp [PresentedRelationEventAt.support]

theorem quotientStable_support_one :
    quotientStableFace.generatorSupport 1 = {false, true} := by
  classical
  rw [RootGeneratedCofinalHistoryAt.generatorSupport,
    quotientStable_observedEvents_one]
  apply Finset.ext
  intro value
  simp [PresentedRelationEventAt.support]

theorem quotientStable_support_does_not_stabilize_at_zero :
    quotientStableFace.generatorSupport 0 ≠
      quotientStableFace.generatorSupport 1 := by
  rw [quotientStable_support_zero, quotientStable_support_one]
  decide

theorem quotientStable_relation_true_mem_closure :
    Finsupp.single true 1 ∈ quotientStableFace.relationClosure := by
  apply quotientStableFace.relationStage_le_closure 1
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation (Finsupp.single true 1) ∈
    quotientStableFace.observedEvents 1
  rw [quotientStable_observedEvents_one]
  simp

theorem quotientStable_stageGeneratorToCompletion_zero_surjective :
    Function.Surjective
      (quotientStableFace.stageGeneratorToCompletion 0) := by
  intro value
  obtain ⟨closureValue, rfl⟩ := Submodule.Quotient.mk_surjective
    quotientStableFace.relationInGeneratorClosure value
  let preimage : quotientStableFace.generatorStage 0 :=
    ⟨Finsupp.single false (closureValue.1 false), by
      change Finsupp.single false (closureValue.1 false) ∈
        Finsupp.supported ℤ ℤ
          (quotientStableFace.generatorSupport 0 : Set Bool)
      apply Finsupp.single_mem_supported
      rw [quotientStable_support_zero]
      simp⟩
  refine ⟨preimage, ?_⟩
  change Submodule.Quotient.mk
      (quotientStableFace.stageGeneratorToClosure 0 preimage) =
    Submodule.Quotient.mk closureValue
  apply (Submodule.Quotient.eq
    quotientStableFace.relationInGeneratorClosure).2
  change ((preimage : Bool →₀ ℤ) - closureValue.1) ∈
    quotientStableFace.relationClosure
  have relation_multiple := quotientStableFace.relationClosure.smul_mem
    (-closureValue.1 true) quotientStable_relation_true_mem_closure
  convert relation_multiple using 1
  ext generator
  cases generator <;> simp [preimage]

theorem quotientStable_compactAt_zero :
    quotientStableFace.CompactAt 0 :=
  (quotientStableFace.compactAt_iff_presentedEpi 0).mpr
    ((quotientStableFace.stageGeneratorToCompletion_surjective_iff_presentedEpi
      0).mp quotientStable_stageGeneratorToCompletion_zero_surjective)

/-- Regression for the exact calibration: support grows at the next stage,
yet the already-presented quotient residual vanishes at stage zero. -/
theorem quotient_compact_while_support_grows :
    quotientStableFace.CompactAt 0 ∧
      quotientStableFace.generatorSupport 0 ≠
        quotientStableFace.generatorSupport 1 :=
  ⟨quotientStable_compactAt_zero,
    quotientStable_support_does_not_stabilize_at_zero⟩

theorem settlement_is_total_for_arbitrary_generator_carrier
    {Generator : Type*}
    {seed : RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
    {next : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator →
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    (history : RootGeneratedCofinalHistoryAt rootOccurrence seed next) :
    (∃ stage, history.CompactAt stage) ∨
      (∀ stage, ¬ history.CompactAt stage) :=
  history.settlement_exhaustive

/-- The public mouth takes actual occurrences only.  In particular the old
caller-owned history receipts and generated-after-the-fact perfect data are
not fields. -/
example : True := by
  fail_if_success exact face.generatorSupportReceipt
  fail_if_success exact face.relationStages
  fail_if_success exact face.relationSupported
  fail_if_success exact face.finiteGenerator
  fail_if_success exact face.finiteEnvelope
  fail_if_success exact face.degreewiseEpi
  fail_if_success exact face.perfectModel
  fail_if_success exact face.determinant
  exact True.intro

#print axioms RootGeneratedCofinalHistoryAt.generate
#print axioms RootGeneratedCofinalHistoryAt.settle
#print axioms RootGeneratedCofinalHistoryAt.settlement_exhaustive
#print axioms RootGeneratedCofinalHistoryAt.compactAt_iff_presentedEpi
#print axioms face_generates_perfectDeterminantUnit
#print axioms quotient_compact_while_support_grows

end

end CofinalHistorySettlementRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
