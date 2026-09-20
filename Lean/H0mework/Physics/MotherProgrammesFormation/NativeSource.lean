import H0mework.Physics.MotherSource.GroundedRealization
import H0mework.Physics.GaugeSource.CenteredReducedEntropyIteration

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualSourceCoverage

open StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineP286SourceNativeCenteredReducedEntropyIteration Stage9C.Revision
open StageNineCClassicalWorldAcceptance StageNineFormNativeGaugeAuxiliaryVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

/-- Source-relative field equations supply the exact operand type of the
original writer; no source-membership or history witness is accepted here. -/
def acceptedState (current : StageNineHolonomicConfiguration)
    (accepted : ClassicalWorldAcceptance positiveSmoothUnifiedSource current) : MaterialState where
  current := current
  smooth := accepted.smooth
  nondegenerate := accepted.nondegenerate
  auxiliaryEquation := by
    intro point
    apply (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff _ _).1
    exact congrArg DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeAuxiliary
      (accepted.pointwiseJointZeroFiber point)

/-- A weaker geometric input is also genuinely prepared by the source's
constitutive writer, which computes its own auxiliary field. -/
def preparedState (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) (nondegenerate : current.Nondegenerate) : MaterialState :=
  p286CenteredReducedEntropyInitialState positiveSmoothUnifiedSource current smooth nondegenerate

def occurrence (state : MaterialState) :
    SpinPair.source.toRootSource.actual.OccurrenceAt (.running state) :=
  SpinPair.emitted (.running state)

def evolution (state : MaterialState) :
    SourceNativeLedgerEvolutionAt SpinPair.source (occurrence state) :=
  SpinPair.generatedEvolution (occurrence state)

def successor (state : MaterialState) :
    SourceNativeLedgerGeneratedSuccessorAt (occurrence state) (evolution state) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (evolution state)).get (by rfl)

theorem successor_native (state : MaterialState) :
    (successor state).targetCurrent = SpinPair.next (.running state) := rfl

theorem actual_whole_write (state : MaterialState) :
    Recognition.wholeField (successor state).targetCurrent =
      Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource state.current
        state.smooth state.nondegenerate 0 :=
  Recognition.native_running_fold state

theorem accepted_current_retained (current : StageNineHolonomicConfiguration)
    (accepted : ClassicalWorldAcceptance positiveSmoothUnifiedSource current) :
    Recognition.wholeField (.running (acceptedState current accepted)) = current := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualSourceCoverage
