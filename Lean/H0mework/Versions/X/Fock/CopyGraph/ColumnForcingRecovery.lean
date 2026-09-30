import H0mework.Versions.X.Fock.CopyGraph.NormalInverseField
import H0mework.Versions.X.Fock.CopyGraph.ColumnForcingSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceColumnForcing

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedJointClockGraph
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def decode (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) : Space (observed (historyPMF bound) query) :=
  SourceNormalInverse.solve depth bound index query (forcing depth bound index query target)

def field (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) : FieldSpace depth bound :=
  SourceConditionalGraphDecoder.realizeObserved depth bound query (decode depth bound index query target)

def remaining (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  target - SourceCopyGraph.action depth index (fieldRead depth bound (field depth bound index query target))

theorem reconstruction (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.action depth index (fieldRead depth bound (field depth bound index query target)) +
      remaining depth bound index query target = target := add_sub_cancel _ _

variable [MeasurableSingletonClass Observed]

theorem decode_equation (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    (SourceConditionalGraphDecoder.action depth bound index query).adjoint
      (SourceConditionalGraphDecoder.action depth bound index query (decode depth bound index query target)) =
        forcing depth bound index query target :=
  SourceNormalInverse.solve_equation depth bound index query _

omit [MeasurableSingletonClass Observed] in
theorem decode_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    decode depth bound index query target = SourceNormalInverse.decode depth bound index query target := by
  rw [decode, forcing_source]
  exact (SourceNormalInverse.solve_map_apply depth bound index query _).symm

omit [MeasurableSingletonClass Observed] in
theorem field_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    field depth bound index query target = SourceNormalInverse.fieldDecode depth bound index query target := by
  change SourceConditionalGraphDecoder.realizeObserved depth bound query (decode depth bound index query target) = _
  rw [decode_source]
  rfl

omit [MeasurableSingletonClass Observed] in
theorem remaining_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    remaining depth bound index query target = SourceNormalInverse.residual depth bound index query target := by
  rw [remaining, field, SourceConditionalGraphDecoder.realized_action, decode_source]
  rfl

theorem forcing_equal_iff (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (left right : SourceJointClockGraph.Carrier) :
    forcing depth bound index query left = forcing depth bound index query right ↔
      field depth bound index query left = field depth bound index query right := by
  constructor
  · intro same
    simp only [field, decode, same]
  · intro same
    have actionSame := congrArg (fun value => SourceCopyGraph.action depth index (fieldRead depth bound value)) same
    change SourceCopyGraph.action depth index (fieldRead depth bound
      (SourceConditionalGraphDecoder.realizeObserved depth bound query (decode depth bound index query left))) =
      SourceCopyGraph.action depth index (fieldRead depth bound
        (SourceConditionalGraphDecoder.realizeObserved depth bound query (decode depth bound index query right))) at actionSame
    rw [SourceConditionalGraphDecoder.realized_action, SourceConditionalGraphDecoder.realized_action] at actionSame
    have equation := congrArg (SourceConditionalGraphDecoder.action depth bound index query).adjoint actionSame
    rw [decode_equation, decode_equation] at equation
    exact equation

theorem complete_fibre (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (left right : SourceJointClockGraph.Carrier) :
    left = right ↔ forcing depth bound index query left = forcing depth bound index query right ∧
      remaining depth bound index query left = remaining depth bound index query right := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨sameForcing, sameRemaining⟩
    have sameField := (forcing_equal_iff depth bound index query left right).mp sameForcing
    rw [← reconstruction depth bound index query left, sameField, sameRemaining,
      reconstruction depth bound index query right]

theorem remaining_forcing_zero (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    forcing depth bound index query (remaining depth bound index query target) = 0 := by
  rw [forcing_source, remaining_source]
  change (SourceConditionalGraphDecoder.action depth bound index query).adjoint
    (target - SourceConditionalGraphDecoder.action depth bound index query
      (SourceNormalInverse.decode depth bound index query target)) = 0
  rw [SourceNormalInverse.decode_source]
  exact SourceConditionalCorrection.normal depth bound index query target

end
end SourceColumnForcing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
