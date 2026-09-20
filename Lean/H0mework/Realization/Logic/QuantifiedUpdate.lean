import H0mework.Realization.Logic.SourceScope
import H0mework.Realization.Operations.IntegralRelations

/-!
Logical consumers of one actual update retain the joint old/effect coimage.
Both endpoint maps are generated from that common inventory. Predicates are
transported along those maps; neither a predicate truth nor an old-to-new
choice function constructs the update.
-/

set_option autoImplicit false

universe r c d k j o n u v w

namespace SaturationMonoid.SourceOperationDynamics

open SourceOperationLogic SourceOperationEffects SourceOperationRelations
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedScalarDifferentialResidual

noncomputable section

section LogicalConsumers

variable {Joint : Type j} {Old : Type o} {New : Type n}

def postAlong (left : Joint → Old) (right : Joint → New) (predicate : Set Old) : Set New :=
  right '' (left ⁻¹' predicate)

def preAlong (left : Joint → Old) (right : Joint → New) (predicate : Set New) : Set Old :=
  Set.kernImage left (right ⁻¹' predicate)

theorem post_preAlong (left : Joint → Old) (right : Joint → New) :
    GaloisConnection (postAlong left right) (preAlong left right) :=
  (Set.preimage_kernImage (f := left)).compose (Set.image_preimage (f := right))

end LogicalConsumers

section ExistingInventory

variable {R : Type r} [CommRing R]
variable {C : Type c} [AddCommGroup C] [Module R C]
variable {D : Type d} [AddCommGroup D] [Module R D]
variable {K : Type k} [AddCommGroup K] [Module R K]

/-- Project an already generated finite inventory. The endpoint evaluator is
the actual composite, so this interface requests no future table or square. -/
def projectionMorphism (inventory : C →ₗ[R] D) (read : D →ₗ[R] K) :
    Morphism inventory (read.comp inventory) where
  sourceMap := LinearMap.id
  targetMap := read
  commutes := rfl

def projectScope (inventory : C →ₗ[R] D) (read : D →ₗ[R] K) :
    Scope inventory →ₗ[R] Scope (read.comp inventory) :=
  inducedResidualMap (projectionMorphism inventory read)

@[simp] theorem projectScope_source (inventory : C →ₗ[R] D) (read : D →ₗ[R] K)
    (source : C) :
    projectScope inventory read (q inventory source) = q (read.comp inventory) source := rfl

end ExistingInventory

section OperationUpdate

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
variable [∀ sort, AddCommGroup (Value sort)] {s : Sorts}

abbrev OldScope (old : Env Value Var) := Scope (evaluation (s := s) old)
abbrev NewScope (old increment : Env Value Var) := Scope (evaluation (s := s) (old + increment))
abbrev JointScope (old increment : Env Value Var) := Scope (updateInventory (s := s) old increment)

def oldMorphism (old increment : Env Value Var) :
    Morphism (updateInventory (s := s) old increment) (evaluation (s := s) old) where
  sourceMap := LinearMap.id
  targetMap := LinearMap.fst ℤ _ _
  commutes := rfl

def oldRead (old increment : Env Value Var) :
    JointScope (s := s) old increment →ₗ[ℤ] OldScope (s := s) old :=
  inducedResidualMap (oldMorphism old increment)

def newRead (old increment : Env Value Var) :
    JointScope (s := s) old increment →ₗ[ℤ] NewScope (s := s) old increment :=
  inducedResidualMap (updateMorphism old increment)

def jointWitness (old increment : Env Value Var) (word : Formal Value Var s) :
    JointScope (s := s) old increment :=
  q (updateInventory old increment) word

theorem jointWitness_reads (old increment : Env Value Var) (word : Formal Value Var s) :
    oldRead old increment (jointWitness old increment word) = q (evaluation old) word ∧
      newRead old increment (jointWitness old increment word) = q (evaluation (old + increment)) word :=
  ⟨rfl, rfl⟩

abbrev post (old increment : Env Value Var) : Set (OldScope (s := s) old) →
    Set (NewScope (s := s) old increment) :=
  postAlong (oldRead old increment) (newRead old increment)

abbrev pre (old increment : Env Value Var) : Set (NewScope (s := s) old increment) →
    Set (OldScope (s := s) old) :=
  preAlong (oldRead old increment) (newRead old increment)

theorem post_pre (old increment : Env Value Var) :
    GaloisConnection (post (s := s) old increment) (pre old increment) :=
  post_preAlong _ _

/-- An actual source word supplies the joint witness for existential transport. -/
theorem source_post (old increment : Env Value Var) (word : Formal Value Var s)
    (predicate : Set (OldScope (s := s) old)) (holds : q (evaluation old) word ∈ predicate) :
    q (evaluation (old + increment)) word ∈ post old increment predicate :=
  ⟨jointWitness old increment word, holds, rfl⟩

/-- Universal transport is eliminated at this same actual joint witness. -/
theorem source_pre (old increment : Env Value Var) (word : Formal Value Var s)
    (predicate : Set (NewScope (s := s) old increment))
    (holds : q (evaluation old) word ∈ pre old increment predicate) :
    q (evaluation (old + increment)) word ∈ predicate :=
  holds (x := jointWitness old increment word) rfl

end OperationUpdate

end

end SaturationMonoid.SourceOperationDynamics
