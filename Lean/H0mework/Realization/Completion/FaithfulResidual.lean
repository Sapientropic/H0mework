import H0mework.Realization.Completion.FaithfulRealization

/-!
# Root-generated residual coordinates for faithful realization

`RootGeneratedCofinalFaithfulRealizationAt` already classifies an actual
evaluator as faithful, relation-unsound, or relation-sound but uncovered.  A
predicate-level obstruction is not yet a usable downstream object.  This
kernel replays the generated settlement and exposes the first exact residual
coordinate:

* an unsound relation is paired with its nonzero actual image;
* a sound but uncovered map is split into a nonzero kernel coordinate or a
  nonzero cokernel class with an actual representative outside the source
  range.

The coordinate is generated from the settled face.  No branch, zero receipt,
surjectivity/injectivity witness, quotient equivalence, or caller-selected
representative enters the public mouth.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalFaithfulRealization

open CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

universe u v w

namespace RootGeneratedCofinalFaithfulRealizationAt

variable {Root : Type w} {Generator : Type u} {Carrier : Type v}
variable [AddCommGroup Carrier]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
variable {history : RootGeneratedCofinalHistoryAt rootOccurrence
  seedOccurrence continuationOccurrence}
variable {evaluatorOccurrence : RootedAccountedUnfolding
  (Generator → Carrier)}

/-! ## Coordinates of the three generated dispositions -/

/-- A relation outside the actual free-evaluation kernel, together with its
nonzero image.  This is the exact residual when relation soundness fails. -/
structure GeneratedRelationResidualCoordinateAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : Type (max u v w) where
  private mk ::
  relation : Generator →₀ ℤ
  relation_mem : relation ∈ history.relationClosure
  coordinate : Carrier
  coordinate_eq : coordinate = face.freeEvaluation relation
  coordinate_ne_zero : coordinate ≠ 0

namespace GeneratedRelationResidualCoordinateAt

variable {face : RootGeneratedCofinalFaithfulRealizationAt
  history evaluatorOccurrence}

theorem relation_image_eq
    (coordinate : GeneratedRelationResidualCoordinateAt face) :
    coordinate.coordinate = face.freeEvaluation coordinate.relation :=
  coordinate.coordinate_eq

theorem coordinate_nonzero
    (coordinate : GeneratedRelationResidualCoordinateAt face) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne_zero

end GeneratedRelationResidualCoordinateAt

/-- Extract the nonzero relation image directly from a generated unsound
obstruction. -/
noncomputable def relationResidualCoordinate
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (obstruction : GeneratedUnsoundRelationObstructionAt face) :
    GeneratedRelationResidualCoordinateAt face := by
  classical
  let witness := face.unsoundRelationWitness obstruction
  let relation := Classical.choose witness
  have relation_mem : relation ∈ history.relationClosure :=
    (Classical.choose_spec witness).1
  have image_ne_zero : face.freeEvaluation relation ≠ 0 :=
    (Classical.choose_spec witness).2
  exact ⟨relation, relation_mem, face.freeEvaluation relation,
    rfl, image_ne_zero⟩

theorem relationResidualCoordinate_nonzero
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (obstruction : GeneratedUnsoundRelationObstructionAt face) :
    (face.relationResidualCoordinate obstruction).coordinate ≠ 0 :=
  (face.relationResidualCoordinate obstruction).coordinate_ne_zero

/-- A nonzero element of the kernel of the generated completion-to-actual
map.  It is the exact faithful-compression residual when injectivity fails. -/
structure GeneratedKernelResidualCoordinateAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) : Type (max u v w) where
  private mk ::
  coordinate : face.KernelResidual soundness
  coordinate_ne_zero : (coordinate : history.CompletionCarrier) ≠ 0

namespace GeneratedKernelResidualCoordinateAt

variable {face : RootGeneratedCofinalFaithfulRealizationAt
  history evaluatorOccurrence}
variable {soundness : GeneratedRelationSoundnessAt face}

theorem maps_to_zero
    (coordinate : GeneratedKernelResidualCoordinateAt face soundness) :
    face.completionEvaluation soundness coordinate.coordinate = 0 := by
  exact (LinearMap.mem_ker.mp coordinate.coordinate.property)

theorem coordinate_nonzero
    (coordinate : GeneratedKernelResidualCoordinateAt face soundness) :
    (coordinate.coordinate : history.CompletionCarrier) ≠ 0 :=
  coordinate.coordinate_ne_zero

end GeneratedKernelResidualCoordinateAt

/-- Extract a nonzero kernel element from the generated kernel submodule. -/
noncomputable def kernelResidualCoordinate
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face)
    (kernel_nonzero : face.KernelResidual soundness ≠ ⊥) :
    GeneratedKernelResidualCoordinateAt face soundness := by
  classical
  let witness := Submodule.exists_mem_ne_zero_of_ne_bot kernel_nonzero
  let value := Classical.choose witness
  have value_mem : value ∈ face.KernelResidual soundness :=
    (Classical.choose_spec witness).1
  have value_ne_zero : value ≠ 0 :=
    (Classical.choose_spec witness).2
  exact ⟨⟨value, value_mem⟩, value_ne_zero⟩

theorem kernelResidualCoordinate_nonzero
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face)
    (kernel_nonzero : face.KernelResidual soundness ≠ ⊥) :
    ((face.kernelResidualCoordinate soundness kernel_nonzero).coordinate :
      history.CompletionCarrier) ≠ 0 :=
  (face.kernelResidualCoordinate soundness kernel_nonzero).coordinate_ne_zero

/-- A nonzero class in the actual cokernel, with a representative which is
provably outside the generated completion image. -/
structure GeneratedCoverageResidualCoordinateAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) : Type (max u v w) where
  private mk ::
  coordinate : face.CokernelResidual soundness
  coordinate_ne_zero : coordinate ≠ 0
  representative : Carrier
  representative_class :
    (Submodule.Quotient.mk representative : face.CokernelResidual soundness) =
      coordinate
  representative_not_mem_range :
    representative ∉ LinearMap.range (face.completionEvaluation soundness)

namespace GeneratedCoverageResidualCoordinateAt

variable {face : RootGeneratedCofinalFaithfulRealizationAt
  history evaluatorOccurrence}
variable {soundness : GeneratedRelationSoundnessAt face}

theorem class_nonzero
    (coordinate : GeneratedCoverageResidualCoordinateAt face soundness) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne_zero

theorem representative_outside_source_range
    (coordinate : GeneratedCoverageResidualCoordinateAt face soundness) :
    coordinate.representative ∉
      LinearMap.range (face.completionEvaluation soundness) :=
  coordinate.representative_not_mem_range

end GeneratedCoverageResidualCoordinateAt

/-- Extract a nonzero cokernel class and an actual representative from a
non-subsingleton coverage residual. -/
noncomputable def coverageResidualCoordinate
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face)
    (cokernel_nontrivial :
      ¬ Subsingleton (face.CokernelResidual soundness)) :
    GeneratedCoverageResidualCoordinateAt face soundness := by
  classical
  letI : Nontrivial (face.CokernelResidual soundness) :=
    not_subsingleton_iff_nontrivial.mp cokernel_nontrivial
  let pairWitness := exists_pair_ne (face.CokernelResidual soundness)
  let left := Classical.choose pairWitness
  let right := Classical.choose (Classical.choose_spec pairWitness)
  have distinct : left ≠ right :=
    Classical.choose_spec (Classical.choose_spec pairWitness)
  let coordinate : face.CokernelResidual soundness := left - right
  have coordinate_ne_zero : coordinate ≠ 0 := sub_ne_zero.mpr distinct
  let rangeSubmodule : Submodule ℤ Carrier :=
    LinearMap.range (face.completionEvaluation soundness)
  let representative : Carrier :=
    Classical.choose (Submodule.Quotient.mk_surjective
      rangeSubmodule coordinate)
  have representative_class :
      (Submodule.Quotient.mk representative :
        face.CokernelResidual soundness) = coordinate :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective
      rangeSubmodule coordinate)
  have representative_not_mem_range :
      representative ∉ LinearMap.range (face.completionEvaluation soundness) := by
    intro rangeMembership
    have representative_zero :
        (Submodule.Quotient.mk representative :
          face.CokernelResidual soundness) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 rangeMembership
    exact coordinate_ne_zero (representative_class.symm.trans representative_zero)
  exact ⟨coordinate, coordinate_ne_zero, representative,
    representative_class, representative_not_mem_range⟩

theorem coverageResidualCoordinate_nonzero
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face)
    (cokernel_nontrivial :
      ¬ Subsingleton (face.CokernelResidual soundness)) :
    (face.coverageResidualCoordinate soundness cokernel_nontrivial).coordinate ≠ 0 :=
  (face.coverageResidualCoordinate soundness cokernel_nontrivial).coordinate_ne_zero

/-! ## Total generated residual disposition -/

inductive ResidualDispositionOutcome
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : Type (max u v w) where
  | faithful
      (soundness : GeneratedRelationSoundnessAt face)
      (coverage : GeneratedCoverageResidualZeroAt face soundness)
      (realization : GeneratedFaithfulRealizationAt face soundness coverage)
  | unsound
      (obstruction : GeneratedUnsoundRelationObstructionAt face)
      (coordinate : GeneratedRelationResidualCoordinateAt face)
  | kernelResidual
      (soundness : GeneratedRelationSoundnessAt face)
      (obstruction : GeneratedCoverageResidualObstructionAt face soundness)
      (coordinate : GeneratedKernelResidualCoordinateAt face soundness)
  | coverageResidual
      (soundness : GeneratedRelationSoundnessAt face)
      (obstruction : GeneratedCoverageResidualObstructionAt face soundness)
      (coordinate : GeneratedCoverageResidualCoordinateAt face soundness)

/-- A sound but uncovered settlement always produces one of the two exact
mapping residual coordinates.  The kernel/cokernel split is internal to this
producer; callers provide only the generated obstruction. -/
noncomputable def settleCoverageResidual
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face)
    (obstruction : GeneratedCoverageResidualObstructionAt face soundness) :
    Sum (GeneratedKernelResidualCoordinateAt face soundness)
      (GeneratedCoverageResidualCoordinateAt face soundness) := by
  classical
  by_cases kernel_zero : face.KernelResidual soundness = ⊥
  · have cokernel_nontrivial :
        ¬ Subsingleton (face.CokernelResidual soundness) := by
      intro cokernel_subsingleton
      exact obstruction.persists ⟨kernel_zero, cokernel_subsingleton⟩
    exact Sum.inr
      (face.coverageResidualCoordinate soundness cokernel_nontrivial)
  · exact Sum.inl (face.kernelResidualCoordinate soundness kernel_zero)

/-- Total caller-free residual disposition.  It is definitionally driven by
the existing faithful-realization settlement and preserves its positive
branch unchanged. -/
noncomputable def settleWithResidual
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :
    ResidualDispositionOutcome face := by
  classical
  cases face.settle with
  | faithful soundness coverage realization =>
      exact .faithful soundness coverage realization
  | unsound obstruction =>
      exact .unsound obstruction
        (face.relationResidualCoordinate obstruction)
  | uncovered soundness obstruction =>
      cases face.settleCoverageResidual soundness obstruction with
      | inl coordinate =>
          exact .kernelResidual soundness obstruction coordinate
      | inr coordinate =>
          exact .coverageResidual soundness obstruction coordinate

theorem residualDispositionMouth
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :
    Nonempty (ResidualDispositionOutcome face) :=
  ⟨face.settleWithResidual⟩

theorem settleWithResidual_preserves_root
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :
    face.root = history.root :=
  rfl

end RootGeneratedCofinalFaithfulRealizationAt

end
end CofinalFaithfulRealization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
