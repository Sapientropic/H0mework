import H0mework.Versions.R2.Physics.RootRuntime.Authority
import H0mework.Versions.R2.Physics.QuantumFoundation.RuntimeConsumer

/-! The first Stage-10 consumer uses the next original macro occurrence after
the Stage-9 acceptance history. Physical time and runtime depth stay distinct. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision StageNineHolonomicField StageNineEnrichedProofFreeSource
open ProofFreeRicherAnholonomicSource

noncomputable section

def visit := SpinPair.visit 10
def event := Recognition.generated visit
def entry := materialEntry (SpinPair.support visit.current)
def standing := SpinPair.authorityAt 10
def answerAndNext := SpinPair.livingRoot.generatedCausalEntryAnswerAndNextAt visit entry standing

def sourceFace : SourceNativeRootSemanticFaceAt SpinPair.livingRoot visit where
  projection := .inherited .source
  active := PUnit.unit
  classifier_eq := rfl

def classicalFace := SpinPair.configurationFace 10
def quantumFace := Stage9DEF.Runtime.quantumFace 10
def source := sourceFace.rootRead
def configuration : StageNineHolonomicConfiguration := classicalFace.rootRead

def tick := physicalInquiryRuntime.tickAt 16
def nextTick := physicalInquiryRuntime.tickAt 17

theorem ingress : (physicalInquiryRuntime.stateAt 16).engine.node.erase =
    (Stage9DEF.Runtime.quantumPresentation 9).erase := Stage9CU.History.runtime_suffix 9

theorem source_eq : source = positiveSmoothUnifiedSource := rfl

theorem configuration_eq : configuration = Stage9C.Material.SpinPair.actual :=
  Stage9DEF.Runtime.configurationAt_eq_actual 9

theorem recovers_stageNine : configuration = Stage9G.Runtime.configuration :=
  configuration_eq.trans Stage9G.Runtime.configuration_eq.symm

theorem tick_resolution : tick.resolution =
    .directlyAnswered quantumFace (Stage9DEF.Runtime.quantumConsumer 10) := rfl

theorem tick_answer : tick.answer = Stage9DEF.Source.restrict configuration := rfl

theorem tick_vector : tick.answer = Stage9DEF.Source.vector :=
  Stage9DEF.Runtime.fieldAt_eq_vector 9

theorem tick_next : tick.next.node.erase =
    (Stage9DEF.Runtime.quantumPresentation 10).erase := rfl

theorem nextTick_resolution : nextTick.resolution =
    .directlyAnswered (Stage9DEF.Runtime.quantumFace 11)
      (Stage9DEF.Runtime.quantumConsumer 11) := rfl

theorem nextTick_vector : nextTick.answer = Stage9DEF.Source.vector :=
  Stage9DEF.Runtime.fieldAt_eq_vector 10

theorem nextTick_next : nextTick.next.node.erase =
    (Stage9DEF.Runtime.quantumPresentation 11).erase := rfl

theorem next_quantum_from_current (point displacement : BasePoint) :
    nextTick.answer (point + displacement) =
      Matrix.mulVec (Stage9DEF.Dynamics.unitary displacement).val (tick.answer point) :=
  Stage9DEF.Runtime.next_field_from_current 9 point displacement

end
end SaturationMonoid.PhysicsCore.Stage10.Runtime
