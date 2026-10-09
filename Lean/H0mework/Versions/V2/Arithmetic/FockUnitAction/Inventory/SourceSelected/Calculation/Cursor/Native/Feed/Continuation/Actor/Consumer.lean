import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Consumer
open SourceOperationEffects SourceOperationExecution
open ParticleWaveFockPrimePairActuality ParticleWaveFockPrimePairActualityDirect
open Actor.Source
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
  (rawSource environment_actual raw_actual)
end O
namespace R
export Registered (old origin reader actor runtime Point source calculatedValue calculated_value consumes_original_disposition)
end R
namespace K
export Cursor (mathState readCursor emitted)
export Cursor.Source (readMaterial someLift)
end K

/-- This is the already installed original raw restriction after birth registration.
The new born active environment is the separate decoder output. -/
def rawCoimage (depth count ordinal : Nat) : F.Values depth count false :=
  (SourceOperationInquiry.Context.readEnv
    (A.runtime (F.dynamicFeed depth count) (C.continuous depth count))
    (O.rawSource (F.dynamicFeed depth count) (C.continuous depth count))
    ((A.runtime (F.dynamicFeed depth count) (C.continuous depth count)).stateAt
      (birth depth count ordinal + 1))) false Unit.unit

def rawMaterial (depth count ordinal : Nat) :=
  N.cursorRestriction depth (N.recover depth count (rawCoimage depth count ordinal))

theorem raw_full (depth count ordinal : Nat) :
    N.recover depth count (rawCoimage depth count ordinal) =
      SourceOperationNative.point (N.C.mathRuntime depth (actorClock depth count (birth depth count ordinal))) := by
  rw [rawCoimage, O.environment_actual, birth_raw]
  exact N.complete_inverse depth count _

theorem raw_material (depth count ordinal : Nat) :
    rawMaterial depth count ordinal =
      K.readMaterial depth (N.C.mathRuntime depth (actorClock depth count (birth depth count ordinal))).state := by
  change N.cursorRestriction depth (N.recover depth count (rawCoimage depth count ordinal)) = _
  rw [raw_full]
  exact N.cursor_restriction depth _

theorem raw_prefix (depth count ordinal pulse : Nat)
    (atClock : actorClock depth count (birth depth count ordinal) = pulse + 1)
    (within : pulse ≤ sourceFuel (R.source depth (K.emitted depth))) :
    rawMaterial depth count ordinal = Finsupp.single
      (some (⟨K.emitted depth, run pulse (initial (R.source depth (K.emitted depth)))⟩ : R.Point depth)) 1 := by
  rw [raw_material, atClock]
  exact Cursor.Source.material_keeps_prefix depth pulse within

abbrev nativeBudget (depth : Nat) := SourceOperationExecution.remaining
  (RootGeneratedDebtActivationJointSource.OwnerFree.raw (R.old depth) (R.origin depth) (R.reader depth)).expression

private theorem native_material_completed (depth clock : Nat) (after : nativeBudget depth ≤ clock) :
    K.readMaterial depth (N.C.mathRuntime depth clock).state = K.someLift depth (R.calculatedValue depth) := by
  have zero : SourceOperationExecution.remaining (K.mathState depth clock).1 = 0 := by
    rw [RootGeneratedDebtActivationJointSource.OwnerFree.Completion.budget]
    exact Nat.sub_eq_zero_of_le after
  let settled := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.localSettlement
    (R.old depth) (R.origin depth) (R.reader depth) (K.mathState depth clock) zero
  have answer : settled.1 = R.calculatedValue depth :=
    (SourceOperationExecutionDebt.completed_value _ settled).trans
      (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source
        (R.old depth) (R.origin depth) (R.reader depth)).symm
  have shape : (K.mathState depth clock).1 = .const (R.calculatedValue depth) :=
    settled.2.down.trans (congrArg Expr.const answer)
  change Finsupp.single (K.readCursor depth (K.mathState depth clock).1) 1 = _
  rw [shape, R.calculated_value]
  simp [K.readCursor, K.someLift]

theorem raw_completed (depth count : Nat) :
    rawMaterial depth count (nativeBudget depth) = K.someLift depth (R.calculatedValue depth) := by
  rw [raw_material]
  exact native_material_completed depth _ (birthClock_lower depth count (nativeBudget depth))

/-- The original independent recognizer consumes the installed raw face's full actor result. -/
theorem raw_original_disposition (depth count : Nat) :
    (∃ reached : ReachedAt (R.actor depth).rooted.rootSource.source,
      rawMaterial depth count (nativeBudget depth) = K.someLift depth (Finsupp.single
        (⟨(R.runtime depth).emittedOccurrence, .completed (.inl reached)⟩ : R.Point depth) 1) ∧
      ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .settlement generated) ∨
    (∃ exhausted : ExhaustedAt (R.actor depth).rooted.rootSource.source,
      rawMaterial depth count (nativeBudget depth) = K.someLift depth (Finsupp.single
        (⟨(R.runtime depth).emittedOccurrence, .completed (.inr exhausted)⟩ : R.Point depth) 1) ∧
      ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .obstruction generated) := by
  have observed := raw_completed depth count
  rcases R.consumes_original_disposition depth with
    ⟨reached, same, generated, actual⟩ | ⟨exhausted, same, generated, actual⟩
  · exact .inl ⟨reached, observed.trans (congrArg (K.someLift depth) same), generated, actual⟩
  · exact .inr ⟨exhausted, observed.trans (congrArg (K.someLift depth) same), generated, actual⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
