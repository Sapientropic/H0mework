import H0mework.Versions.X.Fock.CopyGraph.NormalInverseDecoder

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNormalInverse

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedJointClockGraph SourceGeneratedAcquisitionJoint
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def fieldDecode (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth bound :=
  (SourceConditionalGraphDecoder.realizeObserved depth bound query).comp (decode depth bound index query)

def residual (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  target - SourceConditionalGraphDecoder.action depth bound index query (decode depth bound index query target)

variable [MeasurableSingletonClass Observed]

theorem field_decode_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    fieldDecode depth bound index query = SourceConditionalGraphDecoder.fieldDecode depth bound index query := by
  rw [fieldDecode, decode_linear]
  rfl

theorem residual_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    residual depth bound index query target = SourceConditionalGraphDecoder.residual depth bound index query target := by
  rw [residual, decode_source]
  have original := SourceConditionalGraphDecoder.reconstruction depth bound index query target
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

omit [MeasurableSingletonClass Observed] in
theorem source_reconstruction (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.action depth index (fieldRead depth bound (fieldDecode depth bound index query target)) +
      residual depth bound index query target = target := by
  change SourceCopyGraph.action depth index
    (fieldRead depth bound (SourceConditionalGraphDecoder.realizeObserved depth bound query
      (decode depth bound index query target))) + _ = _
  rw [SourceConditionalGraphDecoder.realized_action, residual]
  exact add_sub_cancel _ _

theorem source_minimum (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    fieldDecode depth bound index query target ∈ Set.range (SourceConditionalGraphDecoder.realizeObserved depth bound query) ∧
      IsMinOn (fun value : FieldSpace depth bound => ‖target - SourceCopyGraph.action depth index (fieldRead depth bound value)‖ ^ 2)
        (Set.range (SourceConditionalGraphDecoder.realizeObserved depth bound query)) (fieldDecode depth bound index query target) := by
  rw [field_decode_source]
  exact SourceConditionalGraphDecoder.original_minimum depth bound index query target

omit [MeasurableSingletonClass Observed] in
theorem source_realization (round depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    let copied := SourceCopyGraph.complexAction depth index (word depth bound (fieldDecode depth bound index query target))
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) +
        residual depth bound index query target = target := by
  dsimp only
  rw [SourceCopyGraph.original_copy_realization]
  exact source_reconstruction depth bound index query target

end
end SourceNormalInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
