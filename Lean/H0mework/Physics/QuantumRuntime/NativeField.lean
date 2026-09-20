import H0mework.Physics.Actual.HistoryRuntime
import H0mework.Physics.QuantumRuntime.Inquiry

/-! The installed occupied field is read from the exact generated material
configuration. Every later native write retains its full physical source. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision StageNineHolonomicField

noncomputable section

def configurationAt (index : ℕ) :=
  materialConfiguration (SpinPair.support (SpinPair.visit (index + 1)).current)

theorem configurationAt_eq_actual (index : ℕ) :
    configurationAt index = Stage9C.Material.SpinPair.actual := by
  exact (Stage9CU.History.configuration_add_seven_eq_runtime index).symm.trans
    (Stage9CU.History.configuration_add_seven_eq_firstWrite index)

def fieldAt (index : ℕ) : Source.OccupiedField := Source.restrict (configurationAt index)

theorem fieldAt_eq_vector (index : ℕ) : fieldAt index = Source.vector := by
  rw [fieldAt, configurationAt_eq_actual, Source.restrict_actual]

def firstQuantumTick := physicalInquiryRuntime.tickAt 10

theorem firstQuantumTick_resolution : firstQuantumTick.resolution =
    .directlyAnswered (quantumFace 4) (quantumConsumer 4) := rfl

theorem firstQuantumTick_answer : firstQuantumTick.answer = fieldAt 3 := rfl

theorem firstQuantumTick_next : firstQuantumTick.next.node.erase =
    (quantumPresentation 4).erase := rfl

def secondQuantumTick := physicalInquiryRuntime.tickAt 11

theorem secondQuantumTick_resolution : secondQuantumTick.resolution =
    .directlyAnswered (quantumFace 5) (quantumConsumer 5) := rfl

theorem secondQuantumTick_answer : secondQuantumTick.answer = fieldAt 4 := rfl

theorem secondQuantumTick_next : secondQuantumTick.next.node.erase =
    (quantumPresentation 5).erase := rfl

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Runtime
