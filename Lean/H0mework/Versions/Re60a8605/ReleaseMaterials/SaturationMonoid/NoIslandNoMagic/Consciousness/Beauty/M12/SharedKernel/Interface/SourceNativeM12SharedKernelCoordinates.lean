import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.SharedKernel.ObserverRestrictionFamily
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.Interface.SourceGeneratedM12AestheticObserverContext
import H0mework.Cognition.Selfhood.Narrative

/-!
# Source-native M12 shared-kernel coordinates

The coarse and refined M12 observers are restrictions of the same exact
crossing occurrence and share one authority coordinate.  Their joint visible
kernel supports public evaluation, proposal, publication, and narrative
readouts.  The first/recurrent pair remains hidden and is retained as an
explicit exact-event and authority residual.

This interface creates no communication edge, carrier, quotient, root, or
successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Beauty
namespace M12
namespace SharedKernel

open ProcessGame Society
open ResponsibilityLifecycle
open ProcessGame.Society.Space
open ProcessGame.Society.Observer
open ProcessGame.Society.History
open ProcessGame.Society.Probability
open ProcessGame.Society.Probability.Measure
open ProcessGame.Society.Probability.Kernel
open ProcessGame.Society.Probability.Consumer
open ProcessGame.Society.M11GeneratedSocialSpaceCrossingFixture
open ProcessGame.Society.M12GeneratedFlowObserverFixture
open ProcessGame.Society.M12GeneratedFlowMeasureFixture
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.SharedKernel

noncomputable section

abbrev M12ObserverMember :=
  SourceGeneratedM12AestheticContextOccurrence

/-- Both member observers are restrictions of one exact crossing and use the
literal same source authority coordinate. -/
def m12ObserverFamily :
    CommonAuthorityObserverFamily ExactCrossing Nat where
  Member := M12ObserverMember
  Visible := fun _member => Visible
  forget := fun member => (observerAt member).forget
  authorityK := crossingAuthorityK
  positive := ⟨.coarse⟩

abbrev M12JointVisible := m12ObserverFamily.JointVisible

def m12JointObserver : AuthorityObserver ExactCrossing M12JointVisible Nat :=
  m12ObserverFamily.jointAuthorityObserver

/-- Runtime-sized concrete image of the dependent two-member visible family.
It is used by the finite fold so equality remains computational. -/
structure M12SharedVisible where
  coarse : Visible
  refined : Visible
  deriving DecidableEq, Repr

def m12SharedVisibleRead (crossing : ExactCrossing) : M12SharedVisible where
  coarse := coarseObserver.forget crossing
  refined := fineObserver.forget crossing

def m12JointVisibleToShared (visible : M12JointVisible) : M12SharedVisible where
  coarse := visible .coarse
  refined := visible .refined

@[simp] theorem m12JointVisibleToShared_jointForget
    (crossing : ExactCrossing) :
    m12JointVisibleToShared (m12ObserverFamily.jointForget crossing) =
      m12SharedVisibleRead crossing :=
  rfl

theorem m12SharedVisibleRead_eq_iff
    {left right : ExactCrossing} :
    m12SharedVisibleRead left = m12SharedVisibleRead right ↔
      ∀ member, (observerAt member).forget left =
        (observerAt member).forget right := by
  constructor
  · intro equality member
    cases member with
    | coarse => exact congrArg M12SharedVisible.coarse equality
    | refined => exact congrArg M12SharedVisible.refined equality
  · intro memberwise
    exact congrArg₂ M12SharedVisible.mk
      (memberwise .coarse) (memberwise .refined)

def m12SharedObserver :
    AuthorityObserver ExactCrossing M12SharedVisible Nat where
  forget := m12SharedVisibleRead
  authorityK := crossingAuthorityK

/-- Concrete shared fold of the same monthly measure and exact event. -/
def m12SharedFold : SourceGeneratedObserverKernelFoldAt
    monthlyMeasure m12SharedObserver firstOccurrenceEvent :=
  SourceGeneratedObserverKernelFoldAt.generate
    monthlyMeasure m12SharedObserver firstOccurrenceEvent

def m12SharedConditionedVisible : M12SharedVisible :=
  ⟨.conditioned, .conditioned⟩

@[simp] theorem m12Shared_first_visible :
    m12SharedObserver.forget firstCrossing =
      m12SharedConditionedVisible :=
  rfl

@[simp] theorem m12Shared_middle_visible :
    m12SharedObserver.forget middleCrossing =
      ⟨.conditioned, .outside⟩ :=
  rfl

@[simp] theorem m12Shared_recurrent_visible :
    m12SharedObserver.forget recurrentCrossing =
      m12SharedConditionedVisible :=
  rfl

theorem m12Shared_middle_not_conditioned :
    m12SharedObserver.forget middleCrossing ≠
      m12SharedConditionedVisible := by
  rw [m12Shared_middle_visible]
  decide

@[simp] theorem m12Shared_conditioned_fibre :
    m12SharedFold.fibre m12SharedConditionedVisible =
      [firstCrossing, recurrentCrossing] := by
  rfl

@[simp] theorem m12Shared_conditioned_eventFibre :
    m12SharedFold.eventFibre m12SharedConditionedVisible =
      [firstCrossing] := by
  rfl

@[simp] theorem m12Shared_conditioned_fibreMass :
    m12SharedFold.fibreMass m12SharedConditionedVisible = 11511 := by
  unfold SourceGeneratedObserverKernelFoldAt.fibreMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change monthlyMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if m12SharedObserver.forget weighted.1 =
          m12SharedConditionedVisible then
        weighted.2 + accumulated else accumulated) 0 = 11511
  rw [monthlyMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    ProcessGame.Society.M11GeneratedSocialSpaceRegression.crossingTrace_exact]
  simp [m12SharedConditionedVisible]
  norm_num

@[simp] theorem m12Shared_conditioned_eventMass :
    m12SharedFold.eventMass m12SharedConditionedVisible = 8754 := by
  unfold SourceGeneratedObserverKernelFoldAt.eventMass
    SourceGeneratedFiniteMeasureAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.eventMass
    SourceOwnedFiniteMeasureCompilerAt.generatedMeasure
    FiniteObserverMeasure.eventMass
  change monthlyMeasureCompiler.weightedCrossings.foldr
    (fun weighted accumulated =>
      if m12SharedObserver.forget weighted.1 =
          m12SharedConditionedVisible ∧ firstOccurrenceEvent weighted.1 then
        weighted.2 + accumulated else accumulated) 0 = 8754
  rw [monthlyMeasureCompiler.weightedCrossings_eq_crossingTrace_map,
    ProcessGame.Society.M11GeneratedSocialSpaceRegression.crossingTrace_exact]
  simp [m12SharedConditionedVisible]

theorem m12Shared_conditioned_readVisible_exact :
    m12SharedFold.readVisible m12SharedConditionedVisible =
      some ((8754 : ℚ≥0) / 11511) := by
  rw [m12SharedFold.readVisible_eq_some_ratio]
  · rw [m12Shared_conditioned_eventMass,
      m12Shared_conditioned_fibreMass]
  · rw [m12Shared_conditioned_fibreMass]
    norm_num

theorem m12Shared_conditioned_aboveHalf :
    ObserverConditionedPredictionClass.ofReadout
        (m12SharedFold.readVisible m12SharedConditionedVisible) =
      some ObserverConditionedPredictionClass.aboveHalf := by
  apply (ObserverConditionedPredictionClass.ofReadout_eq_some_aboveHalf_iff
    (m12SharedFold.readVisible m12SharedConditionedVisible)).2
  exact ⟨(8754 : ℚ≥0) / 11511,
    m12Shared_conditioned_readVisible_exact,
    by simpa [ObserverConditionedPredictionClass.half] using
      ProcessGame.Society.M12ObserverGeometryRegression.fine_probability_above_half⟩

/-! ## Public readouts generated from the shared visible image -/

inductive M12PublicAestheticProposal where
  | withhold
  | suspend
  | endorse
  deriving DecidableEq, Repr

def publicProposalOfEvaluation :
    Option ObserverConditionedPredictionClass → M12PublicAestheticProposal
  | some .aboveHalf => .endorse
  | some .equalHalf => .suspend
  | _ => .withhold

def sharedProbabilityFromVisible (visible : M12SharedVisible) : Option ℚ≥0 :=
  m12SharedFold.readVisible visible

def sharedEvaluationFromVisible
    (visible : M12SharedVisible) :
    Option ObserverConditionedPredictionClass :=
  ObserverConditionedPredictionClass.ofReadout
    (sharedProbabilityFromVisible visible)

def sharedProposalFromVisible
    (visible : M12SharedVisible) : M12PublicAestheticProposal :=
  publicProposalOfEvaluation (sharedEvaluationFromVisible visible)

def publicationFromSharedVisible (visible : M12SharedVisible) : Bool :=
  match visible.refined with
  | .conditioned => false
  | .outside => true

def sourceMemberReport
    (member : M12ObserverMember) (crossing : ExactCrossing) : Visible :=
  (observerAt member).forget crossing

def sourceWitnessPublicationRead (crossing : ExactCrossing) : Bool :=
  publicationFromSharedVisible (m12SharedVisibleRead crossing)

def sourceSharedEvaluationRead
    (crossing : ExactCrossing) : Option ObserverConditionedPredictionClass :=
  sharedEvaluationFromVisible (m12SharedVisibleRead crossing)

def sourceSharedProposalRead
    (crossing : ExactCrossing) : M12PublicAestheticProposal :=
  sharedProposalFromVisible (m12SharedVisibleRead crossing)

def sourceSharedNarrativeRead (crossing : ExactCrossing) : M12SharedVisible :=
  m12SharedVisibleRead crossing

@[simp] theorem sourceWitnessPublicationRead_exact
    (crossing : ExactCrossing) :
    sourceWitnessPublicationRead crossing =
      aestheticStatePublication.publicationTag crossing := by
  cases state_eq : crossing.state <;>
    simp [sourceWitnessPublicationRead, publicationFromSharedVisible,
      m12SharedVisibleRead, fineObserver, aestheticStatePublication, state_eq]

def m12SharedNarrativeReadout :
    TraceConstrainedNarrativeReadout
      ExactCrossing M12SharedVisible M12SharedVisible where
  trace := fun crossing => [m12SharedVisibleRead crossing]
  narrative := sourceSharedNarrativeRead
  claims := fun story => [story]
  emitted_claim_supported := by
    intro crossing atom claimed
    simpa [sourceSharedNarrativeRead, sourceSharedNarrativeRead] using claimed

/-! ## Consumer safety and explicit gluing residuals -/

theorem sourceWitnessPublication_consumerSafe :
    ConsumerSafe m12SharedVisibleRead sourceWitnessPublicationRead :=
  ConsumerSafe.of_factorization publicationFromSharedVisible (fun _ => rfl)

theorem sourceSharedEvaluation_consumerSafe :
    ConsumerSafe m12SharedVisibleRead sourceSharedEvaluationRead :=
  ConsumerSafe.of_factorization sharedEvaluationFromVisible (fun _ => rfl)

theorem sourceSharedProposal_consumerSafe :
    ConsumerSafe m12SharedVisibleRead sourceSharedProposalRead :=
  ConsumerSafe.of_factorization sharedProposalFromVisible (fun _ => rfl)

theorem sourceSharedNarrative_consumerSafe :
    ConsumerSafe m12SharedVisibleRead sourceSharedNarrativeRead :=
  ConsumerSafe.of_factorization id (fun _ => rfl)

def m12SharedKernelPair : AuthorityKernelPair m12SharedObserver where
  left := firstCrossing
  right := recurrentCrossing
  occurrence_ne :=
    SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
      ProcessGame.Society.M10OccurrenceCapacityProcessFixture.recurrent_positions_are_distinct
  visible_eq := rfl
  authority_ne := by decide

def exactFirstOccurrenceRead (crossing : ExactCrossing) : Bool :=
  decide (firstOccurrenceEvent crossing)

def m12SharedExactEventResidual :
    HiddenNullWitness m12SharedVisibleRead exactFirstOccurrenceRead where
  left := firstCrossing
  right := recurrentCrossing
  sameObservation := rfl
  differentDisposition := by decide

def m12SharedAuthorityResidual :
    HiddenNullWitness m12SharedVisibleRead crossingAuthorityK :=
  ⟨firstCrossing, recurrentCrossing, rfl, by decide⟩

def m12SharedEvaluationStatus :
    ConsumerKernelStatus m12SharedVisibleRead sourceSharedEvaluationRead :=
  .certifiedSafe sourceSharedEvaluation_consumerSafe

def m12SharedProposalStatus :
    ConsumerKernelStatus m12SharedVisibleRead sourceSharedProposalRead :=
  .certifiedSafe sourceSharedProposal_consumerSafe

def m12SharedAuthorityStatus :
    ConsumerKernelStatus m12SharedVisibleRead crossingAuthorityK :=
  .hidden m12SharedAuthorityResidual

theorem m12SharedExactEvent_not_consumerSafe :
    ¬ ConsumerSafe m12SharedVisibleRead exactFirstOccurrenceRead :=
  m12SharedExactEventResidual.not_consumerSafe

theorem m12SharedAuthority_not_consumerSafe :
    ¬ ConsumerSafe m12SharedVisibleRead crossingAuthorityK :=
  m12SharedAuthorityResidual.not_consumerSafe

end
end SharedKernel
end M12
end Beauty
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.m12SharedVisibleRead_eq_iff
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.m12Shared_conditioned_readVisible_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.sourceWitnessPublicationRead_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.m12SharedExactEventResidual
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.m12SharedAuthority_not_consumerSafe
