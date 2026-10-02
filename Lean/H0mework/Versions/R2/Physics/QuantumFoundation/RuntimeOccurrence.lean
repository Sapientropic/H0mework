import H0mework.Versions.R2.Physics.QuantumRuntime.Consumer

/-! The first post-DEF occurrence already emits the source, complete classical
configuration and quantum field. Their joint consumer follows the original
macro runtime; no new process, source law or result selector is introduced. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource

noncomputable section

def visit := SpinPair.visit 7
def event := SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit
def entry := materialEntry (SpinPair.support visit.current)

def sourceFace : SourceNativeRootSemanticFaceAt SpinPair.livingRoot visit where
  projection := .inherited .source
  active := PUnit.unit
  classifier_eq := rfl

def classicalFace := SpinPair.configurationFace 7
def quantumFace := Stage9DEF.Runtime.quantumFace 7

def source : SmoothUnifiedSource := sourceFace.rootRead
def configuration : StageNineHolonomicConfiguration := classicalFace.rootRead
def quantum : Stage9DEF.Source.OccupiedField := quantumFace.rootRead

theorem source_eq : source = positiveSmoothUnifiedSource := rfl

theorem configuration_eq : configuration = Stage9C.Material.SpinPair.actual :=
  Stage9DEF.Runtime.configurationAt_eq_actual 6

theorem quantum_restriction : quantum = Stage9DEF.Source.restrict configuration := rfl

theorem quantum_eq : quantum = Stage9DEF.Source.vector :=
  Stage9DEF.Runtime.fieldAt_eq_vector 6

def tick := physicalInquiryRuntime.tickAt 13
def nextTick := physicalInquiryRuntime.tickAt 14

theorem tick_resolution : tick.resolution =
    .directlyAnswered quantumFace (Stage9DEF.Runtime.quantumConsumer 7) := rfl

theorem tick_answer : tick.answer = quantum := rfl

theorem nextTick_resolution : nextTick.resolution =
    .directlyAnswered (Stage9DEF.Runtime.quantumFace 8)
      (Stage9DEF.Runtime.quantumConsumer 8) := rfl

theorem nextTick_answer : nextTick.answer = Stage9DEF.Runtime.fieldAt 7 := rfl

theorem tick_next : tick.next.node.erase =
    (Stage9DEF.Runtime.quantumPresentation 7).erase := rfl

theorem nextTick_next : nextTick.next.node.erase =
    (Stage9DEF.Runtime.quantumPresentation 8).erase := rfl

theorem next_quantum_from_current (point displacement : BasePoint) :
    nextTick.answer (point + displacement) =
      Matrix.mulVec (Stage9DEF.Dynamics.unitary displacement).val (tick.answer point) :=
  Stage9DEF.Runtime.next_field_from_current 6 point displacement

end
end SaturationMonoid.PhysicsCore.Stage9G.Runtime
