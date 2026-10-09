import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Effect
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Calculation.Callee
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Lower.SourceFamily.Foresight.Contextual.Forecast
namespace Terminal
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualVisit actualOccurrence)
end Q
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (runtimeCurrent)
namespace Math
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
 (endpointCount endpoint_source_state answerFace compiled actual_next original_material)
end Math
namespace Payment
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (wellFounded no_refill endpoint_no_paid)
end Payment
end O
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev sourceRoot := (Q.base data.1).root
abbrev sourceVisit : SourceNativeTemporalVisitAt (sourceRoot n data).toAuthoritativeRoot.toLedgerRoot := Q.actualVisit data.1
def raw := Paid.raw binding n data s (requestWord binding n data)
def reader (_supplied : (sourceRoot n data).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
 (sourceVisit n data).current) := raw binding n data
abbrev context := RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.targetRuntime
 (sourceRoot n data).toAuthoritativeRoot (sourceVisit n data).current (reader binding n data)
abbrev sourceU7 := (Q.base data.1).U7
abbrev sourceCalculus := (Q.base data.1).calculus
abbrev endpointCount := O.Math.endpointCount (sourceRoot n data) (sourceVisit n data) (reader binding n data)
abbrev endpointFace := O.Math.answerFace (sourceRoot n data) (sourceVisit n data) (sourceU7 n data) (sourceCalculus n data)
 (reader binding n data) (endpointCount binding n data)

theorem same_state : (Paid.result binding n data s (requestWord binding n data)).2.1=
 O.runtimeCurrent (sourceRoot n data).toAuthoritativeRoot (sourceVisit n data).current
  (reader binding n data) (context binding n data) := by
 exact eq_of_heq (Evaluated.Callee.full_state_of_raw (sourceRoot n data).toAuthoritativeRoot
  (fun {_current} _=> raw binding n data) (Q.actualOccurrence data.1) (raw binding n data) rfl)

theorem endpoint_result : (endpointFace binding n data).rootRead=
 (Paid.result binding n data s (requestWord binding n data)).2.1 :=
 (O.Math.endpoint_source_state (sourceRoot n data) (sourceVisit n data) (sourceU7 n data) (sourceCalculus n data)
  (reader binding n data)).trans (same_state binding n data).symm

theorem noetherian : type_of% (O.Payment.wellFounded (sourceRoot n data).toAuthoritativeRoot
 (sourceVisit n data).current (reader binding n data)) := O.Payment.wellFounded _ _ _
theorem no_refill (count : Nat) : type_of% (O.Payment.no_refill (sourceRoot n data).toAuthoritativeRoot
 (sourceVisit n data).current (reader binding n data) count) := O.Payment.no_refill _ _ _ _
theorem endpoint_no_paid : type_of% (O.Payment.endpoint_no_paid (sourceRoot n data).toAuthoritativeRoot
 (sourceVisit n data).current (reader binding n data)) := O.Payment.endpoint_no_paid _ _ _
theorem actual_compilation : type_of% (O.Math.compiled (sourceRoot n data) (sourceVisit n data) (sourceU7 n data)
 (sourceCalculus n data) (reader binding n data) (endpointCount binding n data)) := O.Math.compiled _ _ _ _ _ _
theorem actual_next : type_of% (O.Math.actual_next (sourceRoot n data) (sourceVisit n data) (sourceU7 n data)
 (sourceCalculus n data) (reader binding n data) (endpointCount binding n data)) := O.Math.actual_next _ _ _ _ _ _
theorem original_material : type_of% (O.Math.original_material (sourceRoot n data) (sourceVisit n data) (sourceU7 n data)
 (sourceCalculus n data) (reader binding n data) (endpointCount binding n data)) := O.Math.original_material _ _ _ _ _ _
end Terminal
end Lower.SourceFamily.Foresight.Contextual.Forecast
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
