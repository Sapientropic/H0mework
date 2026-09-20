import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.Polynomial.Basic
import H0mework.Realization.Completion.ProcessDiagram

/-!
# Root-generated cofinal polynomial section

A source-local process supplies one polynomial section, one successor, and
the generated relative factor witnessing that the current section divides
the successor section.  The generic cofinal-process engine then generates
the entire rooted history and the pro-section diagram.  This diagram is the
global section authority consumed by a later zero-fibre functor.

No zero fibre, point, completed `Nat` table, limit, same-component witness,
or external coordinate enters this kernel.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPolynomialSection

open CategoryTheory
open CofinalProcessDiagram
open CofinalProcessDiagram.RootGeneratedCofinalProcessDiagramAt

noncomputable section

universe u w

/-- Polynomial sections ordered contravariantly by divisibility: an arrow
`D' ⟶ D` records that `D` divides `D'`. -/
structure PolynomialSectionObjectAt (R : Type u) [CommRing R] where
  polynomial : Polynomial R

namespace PolynomialSectionObjectAt

variable {R : Type u} [CommRing R]

instance : LE (PolynomialSectionObjectAt R) :=
  ⟨fun source target => target.polynomial ∣ source.polynomial⟩

instance : Preorder (PolynomialSectionObjectAt R) where
  le_refl object := dvd_refl object.polynomial
  le_trans left middle right leftMiddle middleRight :=
    dvd_trans middleRight leftMiddle

end PolynomialSectionObjectAt

/-- One source-local determinant-section successor.  The relative factor is
an output of the preceding action-determinant calculation, not a submitted
global section. -/
structure PolynomialSectionSuccessorProcessAt
    (R : Type u) [CommRing R] where
  State : Type w
  seed : State
  next : State → State
  polynomialAt : State → Polynomial R
  relativeFactor : State → Polynomial R
  factorization : ∀ state,
    polynomialAt (next state) = relativeFactor state * polynomialAt state

namespace PolynomialSectionSuccessorProcessAt

variable {R : Type u} [CommRing R]
variable (process : PolynomialSectionSuccessorProcessAt R)

def object (state : process.State) : PolynomialSectionObjectAt R :=
  ⟨process.polynomialAt state⟩

theorem successor_le (state : process.State) :
    process.object (process.next state) ≤ process.object state := by
  change process.polynomialAt state ∣
    process.polynomialAt (process.next state)
  refine ⟨process.relativeFactor state, ?_⟩
  rw [process.factorization]
  exact mul_comm _ _

def toCofinalProcess :
    CofinalDiagramSuccessorProcessAt (PolynomialSectionObjectAt R) where
  State := process.State
  seed := process.seed
  next := process.next
  object := process.object
  transition state := homOfLE (process.successor_le state)

@[simp] theorem toCofinalProcess_stateAt (stage : Nat) :
    process.toCofinalProcess.stateAt stage =
      Nat.rec process.seed (fun _ current => process.next current) stage :=
  rfl

end PolynomialSectionSuccessorProcessAt

/-- The generated global pro-section on one exact root occurrence. -/
structure RootGeneratedCofinalPolynomialSectionAt
    {R : Type u} [CommRing R]
    {Root : Type w}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (dependentProcessOccurrence : RootedAccountedUnfolding
      (Root × PolynomialSectionSuccessorProcessAt R))
    (projects : dependentProcessOccurrence.map Prod.fst = rootOccurrence) :
    Type (max u w) where
  private mk ::

namespace RootGeneratedCofinalPolynomialSectionAt

variable {R : Type u} [CommRing R]
variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {dependentProcessOccurrence : RootedAccountedUnfolding
  (Root × PolynomialSectionSuccessorProcessAt R)}
variable {projects : dependentProcessOccurrence.map Prod.fst = rootOccurrence}

def generate : RootGeneratedCofinalPolynomialSectionAt
    rootOccurrence dependentProcessOccurrence projects :=
  ⟨⟩

def actualProcess
    (_face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :=
  dependentProcessOccurrence.root.2

def dependentCofinalProcessOccurrence
    (_face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :
    RootedAccountedUnfolding
      (Root × CofinalDiagramSuccessorProcessAt
        (PolynomialSectionObjectAt R)) :=
  dependentProcessOccurrence.map fun payload =>
    (payload.1, payload.2.toCofinalProcess)

theorem dependentCofinalProcessOccurrence_projects
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :
    face.dependentCofinalProcessOccurrence.map Prod.fst = rootOccurrence := by
  unfold dependentCofinalProcessOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change dependentProcessOccurrence.map Prod.fst = rootOccurrence
  exact projects

def cofinalFace
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :
    RootGeneratedCofinalProcessDiagramAt rootOccurrence
      face.dependentCofinalProcessOccurrence
      face.dependentCofinalProcessOccurrence_projects :=
  RootGeneratedCofinalProcessDiagramAt.generate

theorem cofinalFace_actualProcess
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :
    face.cofinalFace.actualProcess =
      face.actualProcess.toCofinalProcess := by
  unfold cofinalFace
    RootGeneratedCofinalProcessDiagramAt.actualProcess
    dependentCofinalProcessOccurrence actualProcess
  rw [RootedAccountedUnfolding.root_map]

/-- The global determinant section `D` is the generated pro-section diagram;
zero-fibre formation is deliberately downstream. -/
def globalSectionDiagram
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :
    CategoryTheory.Functor ℕᵒᵖ (PolynomialSectionObjectAt R) :=
  face.cofinalFace.actualDiagram

def stateAt
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :=
  face.cofinalFace.stateAt

theorem stateAt_mem_observation_trace
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects)
    (stage : Nat) :
    face.stateAt stage ∈ (face.cofinalFace.observation stage).trace :=
  face.cofinalFace.stateAt_mem_observation_trace stage

theorem localSection_at
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects)
    (stage : Nat) :
    (face.globalSectionDiagram.obj (Opposite.op stage)).polynomial =
      (face.cofinalFace.actualProcess.object
        (face.stateAt stage)).polynomial :=
  rfl

theorem preserves_root_local_successor_and_global_section
    (face : RootGeneratedCofinalPolynomialSectionAt
      rootOccurrence dependentProcessOccurrence projects) :
    face.cofinalFace.root = rootOccurrence ∧
      face.cofinalFace.actualProcess = face.actualProcess.toCofinalProcess ∧
      face.globalSectionDiagram =
        face.actualProcess.toCofinalProcess.diagram := by
  refine ⟨face.cofinalFace.preserves_root_process_and_generated_diagram.1,
    face.cofinalFace_actualProcess, ?_⟩
  calc
    face.globalSectionDiagram =
        face.cofinalFace.actualProcess.diagram :=
      face.cofinalFace.preserves_root_process_and_generated_diagram.2.2
    _ = face.actualProcess.toCofinalProcess.diagram :=
      congrArg CofinalDiagramSuccessorProcessAt.diagram
        face.cofinalFace_actualProcess

end RootGeneratedCofinalPolynomialSectionAt

end
end CofinalPolynomialSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
