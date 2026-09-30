import H0mework.Realization.ScalarCofinal.Tail

/-! Actual action iterates generate the complete observation history and its autonomous action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory

open SourceGeneratedScalarCofinalKernelCompletion SourceGeneratedScalarCofinalNaturality
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]

abbrev PrefixCarrier (B : Type u) (bound : Nat) := Fin (bound + 1) → B

def prefixRestriction (bound : Nat) : PrefixCarrier B (bound + 1) →ₗ[R] PrefixCarrier B bound :=
  LinearMap.pi fun index => LinearMap.proj index.castSucc

def dropFirst (bound : Nat) : PrefixCarrier B (bound + 1) →ₗ[R] PrefixCarrier B bound :=
  LinearMap.pi fun index => LinearMap.proj index.succ

theorem dropFirst_transition (bound : Nat) :
    (dropFirst (R := R) (B := B) bound).comp (prefixRestriction (bound + 1)) =
      (prefixRestriction bound).comp (dropFirst (bound + 1)) := rfl

variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B)

def stageEvaluator (stage : Nat) : C →ₗ[R] B := observation.comp (action ^ stage)

def prefixEvaluator (bound : Nat) : C →ₗ[R] PrefixCarrier B bound :=
  LinearMap.pi fun index => stageEvaluator action observation index.val

def data : Data (R := R) (Generator := C) (Carrier := PrefixCarrier B) where
  evaluator := prefixEvaluator action observation
  transition := prefixRestriction

theorem compatible : (data action observation).Compatible := by
  intro bound
  rfl

def completion := (data action observation).Completion (compatible action observation)

def sourceMap : C →ₗ[R] completion action observation :=
  ((data action observation).completionMap (compatible action observation)).hom

def stageRead (bound : Nat) : completion action observation →ₗ[R] PrefixCarrier B bound :=
  ((data action observation).stageRealization bound).comp
    ((data action observation).restriction (compatible action observation) bound).hom

@[simp] theorem source_reads_prefix (bound : Nat) (value : C) :
    stageRead action observation bound (sourceMap action observation value) =
      prefixEvaluator action observation bound value :=
  ConcreteCategory.congr_hom ((data action observation).source_to_evaluator
    (compatible action observation) bound) value

@[simp] theorem source_reads_stage (bound : Nat) (value : C) (index : Fin (bound + 1)) :
    stageRead action observation bound (sourceMap action observation value) index =
      observation ((action ^ index.val) value) :=
  congrFun (source_reads_prefix action observation bound value) index

theorem source_fibre_iff (left right : C) :
    sourceMap action observation left = sourceMap action observation right ↔
      ∀ stage : Nat, observation ((action ^ stage) left) = observation ((action ^ stage) right) := by
  constructor
  · intro same stage
    have observed := congrArg (fun value => stageRead action observation stage value (Fin.last stage)) same
    exact (source_reads_stage action observation stage left (Fin.last stage)).symm.trans
      (observed.trans (source_reads_stage action observation stage right (Fin.last stage)))
  · intro observed
    apply Limits.Concrete.limit_ext ((data action observation).quotientTower (compatible action observation))
    intro bound
    have leftRead := ConcreteCategory.congr_hom
      ((data action observation).completionMap_restriction (compatible action observation) bound.unop) left
    have rightRead := ConcreteCategory.congr_hom
      ((data action observation).completionMap_restriction (compatible action observation) bound.unop) right
    have quotientEq : (data action observation).quotientMap bound.unop left =
        (data action observation).quotientMap bound.unop right := by
      apply (data action observation).stageRealization_injective bound.unop
      change prefixEvaluator action observation bound.unop left = prefixEvaluator action observation bound.unop right
      exact funext fun index => observed index.val
    exact leftRead.trans (quotientEq.trans rightRead.symm)

theorem dropFirst_evaluator (bound : Nat) :
    (dropFirst (R := R) bound).comp (prefixEvaluator action observation (bound + 1)) =
      (prefixEvaluator action observation bound).comp action := by
  apply LinearMap.ext
  intro value
  funext index
  change observation ((action ^ (index.val + 1)) value) =
    observation ((action ^ index.val) (action value))
  rw [pow_succ]
  rfl

def historyMorphism : Morphism (SourceGeneratedScalarCofinalTail.tail (data action observation))
    (data action observation) where
  generatorMap := action
  stageMap := dropFirst
  transition_naturality := dropFirst_transition
  evaluator_naturality := dropFirst_evaluator action observation

def endomorphism : completion action observation →ₗ[R] completion action observation :=
  ((historyMorphism action observation).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (data action observation) (compatible action observation))
    (compatible action observation)).hom.comp
      (SourceGeneratedScalarCofinalTail.completionMap (data action observation) (compatible action observation)).hom

theorem endomorphism_source (value : C) :
    endomorphism action observation (sourceMap action observation value) =
      sourceMap action observation (action value) := by
  have tail := ConcreteCategory.congr_hom
    (SourceGeneratedScalarCofinalTail.completionMap_source (data action observation)
      (compatible action observation)) value
  have source := ConcreteCategory.congr_hom
    ((historyMorphism action observation).completionMorphism_source_naturality
      (SourceGeneratedScalarCofinalTail.compatible (data action observation) (compatible action observation))
      (compatible action observation)) value
  exact (congrArg ((historyMorphism action observation).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (data action observation) (compatible action observation))
    (compatible action observation)).hom tail).trans source

private theorem stageQuotient_reads_dropFirst (bound : Nat)
    (value : (SourceGeneratedScalarCofinalTail.tail (data action observation)).StageQuotient bound) :
    (data action observation).stageRealization bound
        ((historyMorphism action observation).stageQuotientMap bound value) =
      dropFirst (R := R) bound ((data action observation).stageRealization (bound + 1) value) := by
  obtain ⟨source, rfl⟩ := Submodule.mkQ_surjective
    ((SourceGeneratedScalarCofinalTail.tail (data action observation)).stageKernel bound) value
  exact (LinearMap.congr_fun (dropFirst_evaluator action observation bound) source).symm

theorem endomorphism_reads_dropFirst (bound : Nat) (value : completion action observation) :
    stageRead action observation bound (endomorphism action observation value) =
      dropFirst (R := R) bound (stageRead action observation (bound + 1) value) := by
  have afterMorphism := ConcreteCategory.congr_hom
    ((historyMorphism action observation).completionMorphism_restriction
      (SourceGeneratedScalarCofinalTail.compatible (data action observation) (compatible action observation))
      (compatible action observation) bound)
    ((SourceGeneratedScalarCofinalTail.completionMap (data action observation) (compatible action observation)).hom value)
  have afterTail := ConcreteCategory.congr_hom
    (SourceGeneratedScalarCofinalTail.completionMap_restriction (data action observation)
      (compatible action observation) bound) value
  exact (congrArg ((data action observation).stageRealization bound) afterMorphism).trans
    ((congrArg (fun quotient => (data action observation).stageRealization bound
      ((historyMorphism action observation).stageQuotientMap bound quotient)) afterTail).trans
      (stageQuotient_reads_dropFirst action observation bound
        (((data action observation).restriction (compatible action observation) (bound + 1)).hom value)))

end
end SourceGeneratedActionObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
