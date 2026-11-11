import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCarrierKernel
import H0mework.Realization.Coherent.PerfectRealization

/-!
# Source-generated dependent joint-state occurrence

For every payload of one existing dependent-carrier occurrence, raw
evaluation-compatible source action and owner-free Hilbert evolution generate
the complete equivariant perfect-realization disposition.  The resulting
joint-state and disposition trees are relabellings of the original
`RootedAccountedUnfolding`, so they retain every branch and project strictly
back to the same occurrence.

This is the source-polymorphic mathematical face, not a controller admission.
It adds no runtime, ledger, next, second root, branch choice, covariance law,
radial-zero premise, determinant, or domain endpoint.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedDependentJointState

open DependentCarrier
open SourceGeneratedIntegralEquivariantPerfectRealization

noncomputable section

universe s a c t l r h v d f

variable {Source : Type s}
variable {Algebra : Source → Type a} {Combinatorial : Source → Type c}
variable {Topological : Source → Type t} {Logical : Source → Type l}
variable {Relation : Source → Type r} {Cochain : Source → Type h}
variable {Carrier : Source → Type v} {DualTarget : Source → Type d}
variable {ActualTarget : Source → Type f}
variable [∀ source, AddCommGroup (Carrier source)]
variable [∀ source, AddCommGroup (DualTarget source)]
variable [∀ source, NormedAddCommGroup (ActualTarget source)]
variable [∀ source, InnerProductSpace ℂ (ActualTarget source)]
variable [∀ source, CompleteSpace (ActualTarget source)]

local notation "InputT" =>
  Input Source Algebra Combinatorial Topological Logical Relation Cochain
    Carrier DualTarget ActualTarget

/-- Raw root-law action coordinates indexed by the same payload as the
dependent carrier.  There is no measurement covariance or residual verdict
in this input. -/
structure ActionProfile (input : InputT) where
  sourceActionAt : ∀ source,
    SourceGeneratedScalarEquivariantPerfectAction.ActionData
      (input.dualEvaluationAt source)
  coherentEvolutionAt : ∀ source,
    ActualTarget source →ₗᵢ[ℂ] ActualTarget source

def jointActionAt (input : InputT) (profile : ActionProfile input)
    (source : Source) :
    JointActionData (H := ActualTarget source)
      (input.dualEvaluationAt source) where
  sourceAction := profile.sourceActionAt source
  coherentEvolution := profile.coherentEvolutionAt source

abbrev JointStateAt (input : InputT) (profile : ActionProfile input)
    (source : Source) :=
  GeneratedJointState (input.dualEvaluationAt source)
    (input.faithfulAt source) (jointActionAt input profile source)

abbrev JointDispositionAt (input : InputT)
    (profile : ActionProfile input) (source : Source) :=
  RealizationDisposition (input.dualEvaluationAt source)
    (input.faithfulAt source) (jointActionAt input profile source)

abbrev JointStatePayload (input : InputT)
    (profile : ActionProfile input) :=
  Σ source, JointStateAt input profile source

abbrev JointDispositionPayload (input : InputT)
    (profile : ActionProfile input) :=
  Σ source, JointDispositionAt input profile source

def jointStatePayloadAt (input : InputT) (profile : ActionProfile input)
    (source : Source) : JointStatePayload input profile :=
  ⟨source, SourceGeneratedIntegralEquivariantPerfectRealization.generate
    (input.dualEvaluationAt source) (input.faithfulAt source)
    (jointActionAt input profile source)⟩

/-- Every node of the existing occurrence generates its own joint state. -/
def jointStateOccurrence (input : InputT)
    (profile : ActionProfile input) :
    RootedAccountedUnfolding (JointStatePayload input profile) :=
  input.occurrence.map (jointStatePayloadAt input profile)

/-- Outer factorization residual and the three realized covariance branches
remain one dependent projection of the same state tree. -/
def jointDispositionOccurrence (input : InputT)
    (profile : ActionProfile input) :
    RootedAccountedUnfolding (JointDispositionPayload input profile) :=
  (jointStateOccurrence input profile).map (fun payload =>
    ⟨payload.1, payload.2.realization⟩)

theorem jointStateOccurrence_rooted (input : InputT)
    (profile : ActionProfile input) :
    (jointStateOccurrence input profile).map (fun payload => payload.1) =
      input.occurrence := by
  rw [jointStateOccurrence, RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id input.occurrence

theorem jointDispositionOccurrence_rooted (input : InputT)
    (profile : ActionProfile input) :
    (jointDispositionOccurrence input profile).map
        (fun payload => payload.1) = input.occurrence := by
  rw [jointDispositionOccurrence, RootedAccountedUnfolding.map_map]
  exact jointStateOccurrence_rooted input profile

/-- Existing dependent evaluation/measurement faces and their generated
joint state are packaged without changing the occurrence. -/
structure GeneratedInstallation (input : InputT)
    (profile : ActionProfile input) where
  dependent : DependentCarrier.Generated input
  jointStateFace : RootedAccountedUnfolding (JointStatePayload input profile)
  dispositionFace :
    RootedAccountedUnfolding (JointDispositionPayload input profile)
  jointState_rooted :
    jointStateFace.map (fun payload => payload.1) = input.occurrence
  disposition_rooted :
    dispositionFace.map (fun payload => payload.1) = input.occurrence

def generateInstallation (input : InputT)
    (profile : ActionProfile input) : GeneratedInstallation input profile where
  dependent := DependentCarrier.generate input
  jointStateFace := jointStateOccurrence input profile
  dispositionFace := jointDispositionOccurrence input profile
  jointState_rooted := jointStateOccurrence_rooted input profile
  disposition_rooted := jointDispositionOccurrence_rooted input profile

theorem installed_evaluation_is_existing_face (input : InputT)
    (profile : ActionProfile input) :
    (generateInstallation input profile).dependent.evaluationFace =
      input.EvaluationOccurrence :=
  rfl

theorem installed_faithful_is_existing_face (input : InputT)
    (profile : ActionProfile input) :
    (generateInstallation input profile).dependent.faithfulFace =
      input.FaithfulOccurrence :=
  rfl

theorem joint_root_source (input : InputT)
    (profile : ActionProfile input) :
    (jointStateOccurrence input profile).root.1 = input.occurrence.root :=
  congrArg Sigma.fst
    (RootedAccountedUnfolding.root_map
      (jointStatePayloadAt input profile) input.occurrence)

theorem joint_root_is_generated_from_existing_faces (input : InputT)
    (profile : ActionProfile input) :
    (jointStateOccurrence input profile).root =
      ⟨input.occurrence.root,
        SourceGeneratedIntegralEquivariantPerfectRealization.generate
          (RootEvaluation input) (RootFaithful input)
          (jointActionAt input profile input.occurrence.root)⟩ := by
  exact RootedAccountedUnfolding.root_map
    (jointStatePayloadAt input profile) input.occurrence

/-- Every lawful readout of the disposition tree is the existing unique
rooted fold. -/
theorem disposition_readout_unique
    (input : InputT) (profile : ActionProfile input)
    {Readout : Type*}
    (atOccurrence : JointDispositionPayload input profile →
      List Readout → Readout)
    (candidate : RootedAccountedUnfolding
      (JointDispositionPayload input profile) → Readout)
    (commutes : ∀ origin branches,
      candidate (RootedAccountedUnfolding.occur origin branches) =
        atOccurrence origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate (jointDispositionOccurrence input profile) =
      (jointDispositionOccurrence input profile).fold atOccurrence :=
  RootedAccountedUnfolding.fold_unique atOccurrence candidate commutes _

end

end SourceGeneratedDependentJointState
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
