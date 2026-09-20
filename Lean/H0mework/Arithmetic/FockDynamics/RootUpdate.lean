import H0mework.Arithmetic.FockState.JointMeasurement
import H0mework.Realization.Operations.MixedTrace

/-!
# Root-generated second-quantized Fock update

At one exact global-germ owner, the finite prime field is the sum of all
actual prime basis states in the current even-sector factorization.  Its
raw wave colors and ordered two-particle tensor form one Fock state.  Moving
between two indices generates the full second-quantized effect, including
both cross terms; no state, effect or conservation equation is supplied by
a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

noncomputable section

open SourceOperationEffects

/-- Finite source field generated from every actual prime in one exact-owner
even-sector factorization. -/
def ownerPrimeField (owner : GlobalParentOwner) (index : Nat) :
    IntegralOneParticle :=
  ∑ primeIndex : OwnerPrimeIndexAt owner index,
    ownerPrimeOneParticle primeIndex

/-- Raw two-color wave state together with its ordered two-particle sector. -/
def secondQuantizedState (field : IntegralOneParticle) : ParentCarrier :=
  diagonalInclusion field + pairInclusion (field ⊗ₜ[ℤ] field)

/-- Exact degree-at-most-two effect of adding one field increment.  The two
ordered cross terms are retained separately. -/
def secondQuantizedEffect
    (old increment : IntegralOneParticle) : ParentCarrier :=
  diagonalInclusion increment +
    pairInclusion
      (old ⊗ₜ[ℤ] increment + increment ⊗ₜ[ℤ] old +
        increment ⊗ₜ[ℤ] increment)

/-! The source fixes its operation syntax before the runtime occurrence. Intermediate
tensor and parent sorts have no free inputs; their values are generated from the field. -/

inductive OperationSort
  | field | pair | parent

abbrev OperationValue : OperationSort → Type
  | .field => IntegralOneParticle
  | .pair => OrderedParticleTwo
  | .parent => ParentCarrier

instance : (sort : OperationSort) → AddCommGroup (OperationValue sort)
  | .field => inferInstanceAs (AddCommGroup IntegralOneParticle)
  | .pair => inferInstanceAs (AddCommGroup OrderedParticleTwo)
  | .parent => inferInstanceAs (AddCommGroup ParentCarrier)

abbrev OperationVar : OperationSort → Type
  | .field => PUnit
  | .pair | .parent => PEmpty

def fieldEnvironment (field : IntegralOneParticle) : Env OperationValue OperationVar
  | .field, _ => field
  | .pair, arg => nomatch arg
  | .parent, arg => nomatch arg

def operationTensor : IntegralOneParticle →+ IntegralOneParticle →+ OrderedParticleTwo :=
  LinearMap.toAddMonoidHom'.comp (TensorProduct.mk ℤ _ _).toAddMonoidHom

/-- The original Fock operation, expressed in the source-polymorphic compiler. -/
def fockOperation : Expr OperationValue OperationVar .parent :=
  .add (.linear (s := .field) diagonalInclusion.toAddMonoidHom (.var PUnit.unit))
    (.linear (s := .pair) pairInclusion.toAddMonoidHom
      (.bilinear (s := .field) (t := .field) operationTensor
        (.var PUnit.unit) (.var PUnit.unit)))

theorem fockOperation_eval (field : IntegralOneParticle) :
    fockOperation.eval (fieldEnvironment field) = secondQuantizedState field := rfl

theorem fockOperation_effect (old increment : IntegralOneParticle) :
    fockOperation.effect (fieldEnvironment old) (fieldEnvironment increment) =
      secondQuantizedEffect old increment := rfl

theorem fieldEnvironment_add (old increment : IntegralOneParticle) :
    fieldEnvironment old + fieldEnvironment increment = fieldEnvironment (old + increment) := by
  funext sort arg
  cases sort with
  | field => rfl
  | pair => exact PEmpty.elim arg
  | parent => exact PEmpty.elim arg

abbrev OperationEffectTerm :=
  Expr OperationValue (ChangedVar OperationVar) .parent

/-- Complete symbolic effect inventory; source order and repeated terms are retained. -/
def operationEffectTrace : List OperationEffectTerm := fockOperation.mixedTerms

def evaluateEffectTerms (terms : List OperationEffectTerm)
    (old increment : IntegralOneParticle) : List ParentCarrier :=
  terms.map fun term =>
    term.eval (mixedEnvironment (fieldEnvironment old) (fieldEnvironment increment))

def evaluateOperationTrace (old increment : IntegralOneParticle) : List ParentCarrier :=
  evaluateEffectTerms operationEffectTrace old increment

theorem evaluateOperationTrace_exact (old increment : IntegralOneParticle) :
    evaluateOperationTrace old increment =
      [diagonalInclusion increment,
       pairInclusion (old ⊗ₜ[ℤ] increment),
       pairInclusion (increment ⊗ₜ[ℤ] old),
       pairInclusion (increment ⊗ₜ[ℤ] increment)] := rfl

theorem evaluateOperationTrace_sum (old increment : IntegralOneParticle) :
    (evaluateOperationTrace old increment).sum = secondQuantizedEffect old increment :=
  (fockOperation.mixedTerms_sum (fieldEnvironment old) (fieldEnvironment increment)).trans
    (fockOperation_effect old increment)

/-- The update is produced by the complete symbolic operation trace. -/
theorem secondQuantizedState_trace_update (old target : IntegralOneParticle) :
    secondQuantizedState target = secondQuantizedState old +
      (evaluateOperationTrace old (target - old)).sum := by
  have generated := fockOperation.eval_update_mixedTerms
    (fieldEnvironment old) (fieldEnvironment (target - old))
  rw [fieldEnvironment_add, fockOperation_eval, fockOperation_eval] at generated
  have sourceWrite : old + (target - old) = target := by abel
  rwa [sourceWrite] at generated

def fieldIncrement (owner : GlobalParentOwner)
    (sourceIndex targetIndex : Nat) : IntegralOneParticle :=
  ownerPrimeField owner targetIndex - ownerPrimeField owner sourceIndex

/-- The original Fock update consumes the generic complete operation trace. -/
theorem secondQuantizedState_update
    (old target : IntegralOneParticle) :
    secondQuantizedState target =
      secondQuantizedState old +
        secondQuantizedEffect old (target - old) := by
  rw [← evaluateOperationTrace_sum]
  exact secondQuantizedState_trace_update old target

theorem jointMeasurement_secondQuantizedState_update
    (old target : IntegralOneParticle) :
    jointMeasurement (secondQuantizedState target) =
      jointMeasurement (secondQuantizedState old) +
        jointMeasurement (secondQuantizedEffect old (target - old)) := by
  rw [secondQuantizedState_update, map_add]

theorem jointCoimage_secondQuantizedState_update
    (old target : IntegralOneParticle) :
    jointMeasurementCoimage (secondQuantizedState target) =
      jointMeasurementCoimage (secondQuantizedState old) +
        jointMeasurementCoimage
          (secondQuantizedEffect old (target - old)) := by
  rw [secondQuantizedState_update, map_add]

end


end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
