import H0mework.Arithmetic.GoldbachDynamics.OperationalDecay
import H0mework.Arithmetic.FockState.JointMeasurement

/-!
# Goldbach factor-channel transition in the Fock measurement kernel

Every positive ordered split is encoded as a pure two-particle basis state.
The unconditional particle measurement reads its exact even target.  Hence
an existing source-generated factor repair/emission channel becomes a
same-sector transition whose full state difference lies in the joint
measurement kernel.  Its lifecycle receipt, target and conservative trace
are retained; no strict budget or terminal claim is added here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

def splitLeftUnit {index : Nat} (state : EffectiveSplitAt index) :
    Units NNReal :=
  positiveRealUnit (splitLeft state : ℝ) (by
    exact_mod_cast
      (lt_of_lt_of_le (by omega : 0 < 2) (splitLeft_atLeastTwo state)))

def splitRightUnit {index : Nat} (state : EffectiveSplitAt index) :
    Units NNReal :=
  positiveRealUnit (splitRight state : ℝ) (by
    exact_mod_cast
      (lt_of_lt_of_le (by omega : 0 < 2) (splitRight_atLeastTwo state)))

@[simp] theorem splitLeftUnit_value {index : Nat}
    (state : EffectiveSplitAt index) :
    (((splitLeftUnit state : Units NNReal) : NNReal) : ℝ) = splitLeft state :=
  positiveRealUnit_val _ _

@[simp] theorem splitRightUnit_value {index : Nat}
    (state : EffectiveSplitAt index) :
    (((splitRightUnit state : Units NNReal) : NNReal) : ℝ) = splitRight state :=
  positiveRealUnit_val _ _

/-- Ordered split as one pure degree-two state. -/
def splitParticleState {index : Nat}
    (state : EffectiveSplitAt index) : ParentCarrier :=
  pairInclusion
    (delta (splitLeftUnit state) ⊗ₜ[ℤ] delta (splitRightUnit state))

theorem particleMeasurement_splitParticleState {index : Nat}
    (state : EffectiveSplitAt index) :
    particleMeasurement (splitParticleState state) = targetCharge index := by
  change pairCharge
      (delta (splitLeftUnit state) ⊗ₜ[ℤ] delta (splitRightUnit state)) = _
  rw [pairCharge_delta_tmul_delta]
  apply (Finsupp.single_left_inj (by norm_num : (1 : ℤ) ≠ 0)).2
  apply NNReal.eq
  simp only [NNReal.coe_add, splitLeftUnit_value, splitRightUnit_value]
  have landing : splitLeft state + splitRight state = 2 * (index + 1) := by
    rw [split_landing]
    unfold repairTargetValue
    rw [evenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]
  exact_mod_cast landing

theorem jointMeasurement_splitParticleState {index : Nat}
    (state : EffectiveSplitAt index) :
    jointMeasurement (splitParticleState state) = (0, targetCharge index) := by
  rw [← particleMeasurement_splitParticleState state]
  change jointMeasurement
      (pairInclusion
        (delta (splitLeftUnit state) ⊗ₜ[ℤ] delta (splitRightUnit state))) =
    (0, pairCharge
      (delta (splitLeftUnit state) ⊗ₜ[ℤ] delta (splitRightUnit state)))
  exact jointMeasurement_particleSector _

theorem factorDecay_split_measurement_eq {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    jointMeasurement (splitParticleState source) =
      jointMeasurement (splitParticleState channel.target) := by
  rw [jointMeasurement_splitParticleState,
    jointMeasurement_splitParticleState]

def factorDecayKernelTrace {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : JointMeasurementKernel :=
  ⟨splitParticleState source - splitParticleState channel.target,
    (jointMeasurement_eq_iff_sub_mem_kernel _ _).mp
      (factorDecay_split_measurement_eq channel)⟩

theorem factorDecayFock_recollects {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    splitParticleState channel.target + factorDecayKernelTrace channel =
      splitParticleState source := by
  change splitParticleState channel.target +
      (splitParticleState source - splitParticleState channel.target) = _
  abel

/-- The existing channel receipt and its Fock-kernel realization are one
dependent package. -/
structure GeneratedFactorDecayFockTraceAt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt channel) : Type where
  private mk ::
  sourceState : ParentCarrier
  sourceState_eq : sourceState = splitParticleState source
  targetState : ParentCarrier
  targetState_eq : targetState = splitParticleState channel.target
  trace : JointMeasurementKernel
  trace_eq : trace = factorDecayKernelTrace channel
  sameMeasurement : jointMeasurement sourceState = jointMeasurement targetState
  recollects : targetState + trace = sourceState
  lifecycleTarget : receipt.step.target = channel.target
  lifecycleTraceTotalZero : receipt.step.trace.1 + receipt.step.trace.2 = 0
  lifecycleProgress : receipt.lifecycleEdge.lifecycleEvent.kind.IsProgress

def generateFactorDecayFockTrace {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt channel) :
    GeneratedFactorDecayFockTraceAt channel receipt :=
  { sourceState := splitParticleState source
    sourceState_eq := rfl
    targetState := splitParticleState channel.target
    targetState_eq := rfl
    trace := factorDecayKernelTrace channel
    trace_eq := rfl
    sameMeasurement := factorDecay_split_measurement_eq channel
    recollects := factorDecayFock_recollects channel
    lifecycleTarget := receipt.target_eq
    lifecycleTraceTotalZero := receipt.trace_total_zero
    lifecycleProgress := receipt.lifecycleProgress }

end


end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
