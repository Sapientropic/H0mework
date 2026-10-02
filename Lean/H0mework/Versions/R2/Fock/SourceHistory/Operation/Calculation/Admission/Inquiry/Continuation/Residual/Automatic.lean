import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.Next
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Continuation.Runtime

/-! The original physical occurrence supplies the one environment reader.
All later residual births inherit it through the actual old-source pullback;
the original macro engine consumes each birth and emits its next activation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.Automatic

open SourceOperationEffects SourceOperationNative RootInquiryCompletion
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

namespace C
export RootGeneratedDebtActivationJointSource.Native.Request.Continuation
  (Frame frames runtime actual_node actual_current macro_next macro_next_preserves)
end C

noncomputable section
variable (sourceRuntime : LivingRuntimeState process)

def sourceEnvironment
    {current : Joint.Current (SourcePhysicalCalculationAdmission.registered sourceRuntime)}
    (_source : (lower sourceRuntime).source.source.toRootSource.actual.OccurrenceAt current) :
    Env SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar :=
  Context.environment (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
    (statePoint process (scanIndex current.1 - 1))

def initial : C.Frame (Value := SourcePhysicalCalculation.CalculationValue)
    (Var := SourcePhysicalCalculation.CalculationVar) (sort := Sum.inl OperationSort.parent) where
  N := NewN sourceRuntime
  V := Joint.JointV (SourcePhysicalCalculationAdmission.registered sourceRuntime)
  old := ResidualAdmission.oldState sourceRuntime 9
  program := program sourceRuntime
  registered := ResidualAdmission.request sourceRuntime 9
  scope := identityScope sourceRuntime
  environment := sourceEnvironment sourceRuntime
  depth := 0

theorem initial_source_action
    (source : RootGeneratedDebtActivationJointSource.Native.Request.Residual.Occurrence
      (initial sourceRuntime).old (initial sourceRuntime).program (initial sourceRuntime).registered
      (initial sourceRuntime).scope 0) :
    (fun sort name => (Context.binding sort name).eval
      (SourcePhysicalCalculation.rawEnvironment (sourceRuntime.advance (9 + (0 + 1))))) =
        (initial sourceRuntime).environmentAt source :=
  Next.source_action_environment sourceRuntime 9 0 source

def inquiry := C.runtime (initial sourceRuntime)

theorem actual_node (count : Nat) : ((inquiry sourceRuntime).stateAt count).engine.node =
    .active (C.frames (initial sourceRuntime) count).presentation :=
  C.actual_node (initial sourceRuntime) count

theorem actual_current (count : Nat) : ((inquiry sourceRuntime).stateAt count).engine.node.erase =
    (C.frames (initial sourceRuntime) count).currentPresentation.erase :=
  C.actual_current (initial sourceRuntime) count

theorem actual_next (count : Nat) : ((inquiry sourceRuntime).tickAt count).next.node =
    .active (C.frames (initial sourceRuntime) (count + 1)).presentation :=
  C.macro_next (initial sourceRuntime) count

def canonical := inquiry (runtimeAt 0)

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.Automatic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
