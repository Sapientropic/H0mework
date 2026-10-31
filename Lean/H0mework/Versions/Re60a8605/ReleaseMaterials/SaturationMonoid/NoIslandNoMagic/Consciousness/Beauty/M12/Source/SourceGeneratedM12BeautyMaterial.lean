import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.Interface.SourceGeneratedM12AestheticObserverContext

/-!
# Source-generated beauty material for the fixed M12 instance

The five-coordinate face is generated from one monthly crossing source and
one honest source-state observer refinement.  The producer accepts only the
fixed context occurrence; probability, classification, factorization,
consumer coverage, quotient, and successor are all absent from its mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Beauty
namespace M12

open ProcessGame Society
open ProcessGame.Society.Observer
open ProcessGame.Society.Probability
open ProcessGame.Society.Probability.Kernel
open ProcessGame.Society.M11GeneratedSocialSpaceCrossingFixture
open ProcessGame.Society.M12GeneratedFlowObserverFixture
open ProcessGame.Society.M12ObserverGeometryRegression

noncomputable section

/-- Concrete five-face carrier.  Its fields retain separate source
responsibilities and are not asserted to be algebraically independent. -/
structure SourceGeneratedM12BeautyFace where
  object : M12AestheticObjectReadout
  observerKernel : M12AestheticObserverKernelReadout
  context : M12AestheticContextReadout
  alignment : M12AestheticAlignmentReadout
  kernelLineage : M12AestheticKernelLineageReadout

def m12BeautyFaceRead
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) :
    SourceGeneratedM12BeautyFace where
  object := sourceObjectRead occurrence
  observerKernel := sourceObserverKernelRead occurrence
  context := sourceContextRead occurrence
  alignment := sourceAlignmentRead occurrence
  kernelLineage := sourceKernelLineageRead occurrence

/-- Private source seal indexed by the fixed observer-context occurrence. -/
inductive SourceGeneratedM12BeautyFaceAt
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) : Type
  | private generated

def generateM12BeautyFaceAt
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) :
    SourceGeneratedM12BeautyFaceAt occurrence :=
  .generated

namespace SourceGeneratedM12BeautyFaceAt

def read
    {occurrence : SourceGeneratedM12AestheticContextOccurrence}
    (_face : SourceGeneratedM12BeautyFaceAt occurrence) :
    SourceGeneratedM12BeautyFace :=
  m12BeautyFaceRead occurrence

end SourceGeneratedM12BeautyFaceAt

/-- Object-only collapse is false inside this one carrier: the complete
object event is preserved while the source-generated alignment phase flips. -/
theorem m12Beauty_object_preserved :
    (m12BeautyFaceRead .coarse).object =
      (m12BeautyFaceRead .refined).object := by
  rcases sourceObjectRead_event_preserved with
    ⟨eventFibreEquality, eventMassEquality, _eventMassExact⟩
  change sourceObjectRead .coarse = sourceObjectRead .refined
  cases eventFibreEquality
  cases eventMassEquality
  rfl

theorem m12Beauty_alignment_differs :
    (m12BeautyFaceRead .coarse).alignment ≠
      (m12BeautyFaceRead .refined).alignment := by
  intro equality
  have phaseEquality := congrArg M12AestheticAlignmentReadout.phase equality
  change (sourceAlignmentRead .coarse).phase =
    (sourceAlignmentRead .refined).phase at phaseEquality
  rw [sourceAlignmentRead_coarse_phase,
    sourceAlignmentRead_refined_phase] at phaseEquality
  cases phaseEquality

theorem m12BeautyFace_coarse_ne_refined :
    m12BeautyFaceRead .coarse ≠ m12BeautyFaceRead .refined := by
  intro equality
  exact m12Beauty_alignment_differs
    (congrArg SourceGeneratedM12BeautyFace.alignment equality)

theorem m12Beauty_objectOnly_noGo :
    (m12BeautyFaceRead .coarse).object =
        (m12BeautyFaceRead .refined).object ∧
      m12BeautyFaceRead .coarse ≠ m12BeautyFaceRead .refined :=
  ⟨m12Beauty_object_preserved, m12BeautyFace_coarse_ne_refined⟩

/-- Fixed-fibre arbitrary-subject voting is impossible.  The first and
recurrent actual crossings have one probability readout but distinct source
authority in either context, so no authority-complete decoder exists. -/
theorem m12Beauty_arbitrarySubject_noGo
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) :
    (foldAt occurrence).probabilityReadout.read
        (persistentHiddenKernelPairAt occurrence).left =
      (foldAt occurrence).probabilityReadout.read
        (persistentHiddenKernelPairAt occurrence).right ∧
      (observerAt occurrence).authorityK
          (persistentHiddenKernelPairAt occurrence).left ≠
        (observerAt occurrence).authorityK
          (persistentHiddenKernelPairAt occurrence).right ∧
      ¬ Nonempty (AuthorityCompleteReadoutAt (observerAt occurrence)
        (foldAt occurrence).probabilityReadout) :=
  ⟨persistentHiddenKernelPair_probability_equal occurrence,
    (persistentHiddenKernelPairAt occurrence).authority_ne,
    (foldAt occurrence).noAuthorityCompleteProbability
      (persistentHiddenKernelPairAt occurrence)⟩

/-- Complete source mouth for one fixed context.  All evidence is generated
internally from the same exact crossing trace and honest state publication. -/
structure SourceGeneratedM12BeautyMaterialAt
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) : Type 1 where
  private mk ::
  face : SourceGeneratedM12BeautyFaceAt occurrence
  faceExact : face = generateM12BeautyFaceAt occurrence
  stateRefinement : SourceWitnessKernelRefinementAt
    aestheticStatePublication coarseMiddleKernelPair
  stateRefinementExact : stateRefinement = coarseMiddleKernelRefinement
  refinedObserverExact : ∀ crossing,
    refinedVisibleProjection (sourceRefinedObserver.forget crossing) =
      fineObserver.forget crossing
  hiddenKernelPair : AuthorityKernelPair (observerAt occurrence)
  hiddenKernelPairExact : hiddenKernelPair =
    persistentHiddenKernelPairAt occurrence
  arbitrarySubjectNoGo : type_of% (m12Beauty_arbitrarySubject_noGo occurrence)

def sourceGeneratedM12BeautyMaterialAt
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) :
    SourceGeneratedM12BeautyMaterialAt occurrence where
  face := generateM12BeautyFaceAt occurrence
  faceExact := rfl
  stateRefinement := coarseMiddleKernelRefinement
  stateRefinementExact := rfl
  refinedObserverExact := refinedPublicationProjection_forget_exact
  hiddenKernelPair := persistentHiddenKernelPairAt occurrence
  hiddenKernelPairExact := rfl
  arbitrarySubjectNoGo := m12Beauty_arbitrarySubject_noGo occurrence

theorem sourceGeneratedM12BeautyMaterial_directConsumer
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) :
    let material := sourceGeneratedM12BeautyMaterialAt occurrence
    Nonempty (SourceGeneratedM12BeautyMaterialAt occurrence) ∧
      material.face.read = m12BeautyFaceRead occurrence ∧
      material.stateRefinement = coarseMiddleKernelRefinement ∧
      (∀ crossing, type_of% (material.refinedObserverExact crossing)) ∧
      material.hiddenKernelPair = persistentHiddenKernelPairAt occurrence ∧
      type_of% material.arbitrarySubjectNoGo ∧
      type_of% sourceObjectRead_event_preserved ∧
      type_of% refinement_removes_middle_mass_exact ∧
      type_of% sourceAlignment_phaseFlip ∧
      type_of% measure_compiler_cannot_be_deleted ∧
      type_of% recurrent_state_same_but_origin_lineage_changes ∧
      type_of% same_target_does_not_collapse_crossing := by
  let material := sourceGeneratedM12BeautyMaterialAt occurrence
  exact
    ⟨⟨material⟩, rfl, material.stateRefinementExact,
      material.refinedObserverExact, material.hiddenKernelPairExact,
      material.arbitrarySubjectNoGo, sourceObjectRead_event_preserved,
      refinement_removes_middle_mass_exact, sourceAlignment_phaseFlip,
      measure_compiler_cannot_be_deleted,
      recurrent_state_same_but_origin_lineage_changes,
      same_target_does_not_collapse_crossing⟩

end
end M12
end Beauty
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.m12Beauty_objectOnly_noGo
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.m12Beauty_arbitrarySubject_noGo
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.sourceGeneratedM12BeautyMaterial_directConsumer
