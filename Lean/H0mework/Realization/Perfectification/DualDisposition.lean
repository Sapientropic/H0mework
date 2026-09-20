import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import H0mework.Foundation.Relations.DualEvaluation

/-!
# Source-generated dual evaluation disposition

This is the generic duality/perfection evidence face.  An actual integral
pairing produces the two evaluation maps into the corresponding algebraic
duals.  The compiler classifies each map without assuming finite generation,
perfectness, nondegeneracy, or a determinant frame:

* a bijective evaluation map yields a generated dual equivalence;
* a non-injective map yields a nonzero kernel coordinate;
* an injective but non-surjective map yields a nonzero cokernel coordinate
  with an actual representative outside the generated range.

The paired face chooses no branch supplied by a caller.  It returns a
dualizable two-sided evidence branch exactly when both generated evaluations
are equivalences; otherwise it preserves the first exact residual.  This is
an evidence/disposition layer, not a claim that every complete carrier is
finite or determinant-eligible.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedDualEvaluation

noncomputable section

universe u v w

/-! ## Total disposition of one actual integral evaluation map -/

structure GeneratedEvaluationKernelCoordinate
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    (map : M →ₗ[ℤ] N) : Type (max u v + 1) where
  private mk ::
  coordinate : M
  coordinate_ne_zero : coordinate ≠ 0
  maps_to_zero : map coordinate = 0

namespace GeneratedEvaluationKernelCoordinate

variable {M : Type u} {N : Type v}
variable [AddCommGroup M] [AddCommGroup N]
variable {map : M →ₗ[ℤ] N}

theorem nonzero (coordinate : GeneratedEvaluationKernelCoordinate map) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne_zero

theorem vanishes (coordinate : GeneratedEvaluationKernelCoordinate map) :
    map coordinate.coordinate = 0 :=
  coordinate.maps_to_zero

end GeneratedEvaluationKernelCoordinate

structure GeneratedEvaluationCokernelCoordinate
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    (map : M →ₗ[ℤ] N) : Type (max u v + 1) where
  private mk ::
  coordinate : N ⧸ LinearMap.range map
  coordinate_ne_zero : coordinate ≠ 0
  representative : N
  representative_class :
    (Submodule.Quotient.mk representative : N ⧸ LinearMap.range map) =
      coordinate
  representative_not_mem_range : representative ∉ LinearMap.range map

namespace GeneratedEvaluationCokernelCoordinate

variable {M : Type u} {N : Type v}
variable [AddCommGroup M] [AddCommGroup N]
variable {map : M →ₗ[ℤ] N}

theorem nonzero (coordinate : GeneratedEvaluationCokernelCoordinate map) :
    coordinate.coordinate ≠ 0 :=
  coordinate.coordinate_ne_zero

theorem representative_outside_range
    (coordinate : GeneratedEvaluationCokernelCoordinate map) :
    coordinate.representative ∉ LinearMap.range map :=
  coordinate.representative_not_mem_range

end GeneratedEvaluationCokernelCoordinate

inductive EvaluationDispositionOutcome
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    (map : M →ₗ[ℤ] N) : Type (max u v + 1) where
  | equivalence (equiv : M ≃ₗ[ℤ] N)
  | kernelResidual (coordinate : GeneratedEvaluationKernelCoordinate map)
  | coverageResidual (coordinate : GeneratedEvaluationCokernelCoordinate map)

theorem not_injective_exists
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    {map : M →ₗ[ℤ] N} (not_injective : ¬ Function.Injective map) :
    ∃ left right, left ≠ right ∧ map left = map right := by
  classical
  by_contra impossible
  apply not_injective
  intro left right equality
  by_contra different
  exact impossible ⟨left, right, different, equality⟩

/-! The map is the only input to this classifier.  In particular, no
surjectivity, inverse, or quotient representative is accepted as a premise. -/
noncomputable def settleEvaluation
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    (map : M →ₗ[ℤ] N) : EvaluationDispositionOutcome map := by
  classical
  by_cases injective : Function.Injective map
  · by_cases surjective : Function.Surjective map
    · exact .equivalence (LinearEquiv.ofBijective map ⟨injective, surjective⟩)
    · have exists_not : ∃ value : N, value ∉ LinearMap.range map := by
        by_contra h
        apply surjective
        intro value
        by_contra not_mem
        apply h
        exact ⟨value, not_mem⟩
      let witness : N := Classical.choose exists_not
      have witness_not_mem : witness ∉ LinearMap.range map :=
        Classical.choose_spec exists_not
      let coordinate : N ⧸ LinearMap.range map :=
        Submodule.Quotient.mk witness
      have coordinate_ne_zero : coordinate ≠ 0 := by
        intro equality
        apply witness_not_mem
        exact (Submodule.Quotient.mk_eq_zero _).mp equality
      exact .coverageResidual
        ⟨coordinate, coordinate_ne_zero, witness, rfl,
          by
            intro rangeMembership
            exact witness_not_mem (by exact rangeMembership)⟩
  · let witness := not_injective_exists injective
    let left : M := Classical.choose witness
    let right : M := Classical.choose (Classical.choose_spec witness)
    have left_ne_right : left ≠ right :=
      (Classical.choose_spec (Classical.choose_spec witness)).1
    have equality : map left = map right :=
      (Classical.choose_spec (Classical.choose_spec witness)).2
    let coordinate : M := left - right
    have coordinate_ne_zero : coordinate ≠ 0 :=
      sub_ne_zero.mpr left_ne_right
    have maps_to_zero : map coordinate = 0 := by
      rw [map_sub, equality, sub_self]
    exact .kernelResidual ⟨coordinate, coordinate_ne_zero, maps_to_zero⟩

theorem evaluationDisposition_is_total
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    (map : M →ₗ[ℤ] N) :
  Nonempty (EvaluationDispositionOutcome map) :=
  ⟨settleEvaluation map⟩

theorem settleEvaluation_eq_equivalence_of_bijective
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    (map : M →ₗ[ℤ] N)
    (injective : Function.Injective map)
    (surjective : Function.Surjective map) :
    settleEvaluation map =
      .equivalence (LinearEquiv.ofBijective map ⟨injective, surjective⟩) := by
  classical
  simp [settleEvaluation, injective, surjective]

theorem settleEvaluation_eq_kernelResidual_of_not_injective
    {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    (map : M →ₗ[ℤ] N)
    (not_injective : ¬ Function.Injective map) :
    ∃ coordinate : GeneratedEvaluationKernelCoordinate map,
      settleEvaluation map = .kernelResidual coordinate := by
  classical
  simp only [settleEvaluation]
  split
  · rename_i actualInjective
    exact False.elim (not_injective actualInjective)
  · rename_i actualInjective
    let witness := not_injective_exists actualInjective
    let left : M := Classical.choose witness
    let right : M := Classical.choose (Classical.choose_spec witness)
    have left_ne_right : left ≠ right :=
      (Classical.choose_spec (Classical.choose_spec witness)).1
    have equality : map left = map right :=
      (Classical.choose_spec (Classical.choose_spec witness)).2
    let generated : GeneratedEvaluationKernelCoordinate map := by
      let coordinate : M := left - right
      have coordinate_ne_zero : coordinate ≠ 0 :=
        sub_ne_zero.mpr left_ne_right
      have maps_to_zero : map coordinate = 0 := by
        rw [map_sub, equality, sub_self]
      exact ⟨coordinate, coordinate_ne_zero, maps_to_zero⟩
    exact ⟨generated, rfl⟩

/-! ## Root-owned two-sided pairing evaluations -/

namespace RootGeneratedDualEvaluationPairingAt

variable {Root : Type w} {Left : Type u} {Right : Type v}
variable [AddCommGroup Left] [AddCommGroup Right]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {leftOccurrences : Left → RootedAccountedUnfolding Left}
variable {rightOccurrences : Right → RootedAccountedUnfolding Right}
variable {pairingOccurrence : RootedAccountedUnfolding
  (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}

def leftEvaluation
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    Left →ₗ[ℤ] Module.Dual ℤ Right :=
  face.actualPairing.root

def rightEvaluation
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    Right →ₗ[ℤ] Module.Dual ℤ Left :=
  face.actualPairing.root.flip

end RootGeneratedDualEvaluationPairingAt

inductive DualityDispositionOutcome
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    Type (max u v w + 1) where
  | dualizable
      (leftEquiv : Left ≃ₗ[ℤ] Module.Dual ℤ Right)
      (rightEquiv : Right ≃ₗ[ℤ] Module.Dual ℤ Left)
  | leftResidual
      (coordinate : EvaluationDispositionOutcome face.leftEvaluation)
  | rightResidual
      (coordinate : EvaluationDispositionOutcome face.rightEvaluation)

def combineDualityOutcomes
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence)
    (leftOutcome : EvaluationDispositionOutcome face.leftEvaluation)
    (rightOutcome : EvaluationDispositionOutcome face.rightEvaluation) :
    DualityDispositionOutcome face :=
  match leftOutcome, rightOutcome with
  | .equivalence leftEquiv, .equivalence rightEquiv =>
      .dualizable leftEquiv rightEquiv
  | .equivalence _, .kernelResidual coordinate =>
      .rightResidual (.kernelResidual coordinate)
  | .equivalence _, .coverageResidual coordinate =>
      .rightResidual (.coverageResidual coordinate)
  | .kernelResidual coordinate, _ =>
      .leftResidual (.kernelResidual coordinate)
  | .coverageResidual coordinate, _ =>
      .leftResidual (.coverageResidual coordinate)

noncomputable def settleDuality
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    DualityDispositionOutcome face := by
  exact combineDualityOutcomes face
    (settleEvaluation face.leftEvaluation)
    (settleEvaluation face.rightEvaluation)

theorem dualityDisposition_is_total
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
  Nonempty (DualityDispositionOutcome face) :=
  ⟨settleDuality face⟩

theorem settleDuality_of_both_equivalences
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence)
    (leftEquiv : Left ≃ₗ[ℤ] Module.Dual ℤ Right)
    (rightEquiv : Right ≃ₗ[ℤ] Module.Dual ℤ Left)
    (left_settled : settleEvaluation face.leftEvaluation =
      .equivalence leftEquiv)
    (right_settled : settleEvaluation face.rightEvaluation =
      .equivalence rightEquiv) :
    settleDuality face = .dualizable leftEquiv rightEquiv := by
  unfold settleDuality
  rw [left_settled, right_settled]
  rfl

theorem settleDuality_of_left_kernelResidual
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence)
    (coordinate : GeneratedEvaluationKernelCoordinate face.leftEvaluation)
    (left_settled : settleEvaluation face.leftEvaluation =
      .kernelResidual coordinate) :
    settleDuality face = .leftResidual (.kernelResidual coordinate) := by
  unfold settleDuality
  rw [left_settled]
  rfl

theorem settleDuality_of_left_coverageResidual
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence)
    (coordinate : GeneratedEvaluationCokernelCoordinate face.leftEvaluation)
    (left_settled : settleEvaluation face.leftEvaluation =
      .coverageResidual coordinate) :
    settleDuality face = .leftResidual (.coverageResidual coordinate) := by
  unfold settleDuality
  rw [left_settled]
  rfl

end
end SourceGeneratedDualEvaluation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
