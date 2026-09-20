import H0mework.Physics.MotherProgrammesFormationClockBF.Consumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFFeedback

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous Stage9C.Revision
open ClockBF ClockBFPreparation ClockBFCoordinates ClockBFSplit ClockBFConsumer

noncomputable section

def nextField (u : ℝ) (positive : 0 < 1 + u) : StageNineHolonomicConfiguration :=
  (NativeFamily.stateAt (prepared u positive) 1).current

/-- The original complete writer retains the live coframe and computes its
gravity auxiliary. Neither field is supplied as a target of this step. -/
theorem first_write (u : ℝ) (positive : 0 < 1 + u) :
    (nextField u positive).coframe = (prepared u positive).current.coframe ∧
    (nextField u positive).gravityAuxiliary =
      fun point => physicalIIPlusBivector ((prepared u positive).current.coframe point) :=
  ⟨rfl, rfl⟩

private theorem time_auxiliary_component (clock : ℝ) :
    physicalIIPlusBivector (homogeneousCoframe clock) 3 0 = -clock := by
  simp [physicalIIPlusBivector, homogeneousCoframe, internalBivectorDual,
    coframeWedge, lorentzianCoframeHodge, pairFirst, pairSecond]

theorem original_gravity_component : Runtime.configuration.gravityAuxiliary 0 3 0 = -lapse := by
  rw [Runtime.configuration_eq]
  change physicalIIPlusBivector (homogeneousCoframe lapse) 3 0 = -lapse
  exact time_auxiliary_component lapse

theorem next_gravity_component (u : ℝ) (positive : 0 < 1 + u) :
    (nextField u positive).gravityAuxiliary 0 3 0 = -(1 + u) * lapse := by
  rw [(first_write u positive).2, prepared_current, configuration_coframe]
  change physicalIIPlusBivector (homogeneousCoframe ((1 + u) * lapse)) 3 0 = _
  rw [time_auxiliary_component]
  ring

/-- The changed gravity component lives in the source-computed remainder:
the two displayed coordinates cannot absorb or overwrite it. -/
theorem remainder_change (u : ℝ) (positive : 0 < 1 + u) :
    (encodedAt u positive 1).2.val.gravityAuxiliary 0 3 0 -
      (encodedAt u positive 0).2.val.gravityAuxiliary 0 3 0 = -u * lapse := by
  rw [initial_encoded]
  change (nextField u positive).gravityAuxiliary 0 3 0 -
    Runtime.configuration.gravityAuxiliary 0 3 0 = _
  rw [next_gravity_component, original_gravity_component]
  ring

theorem remainder_changes (u : ℝ) (positive : 0 < 1 + u) (nonzero : u ≠ 0) :
    (encodedAt u positive 1).2.val ≠ (encodedAt u positive 0).2.val := by
  intro equal
  have component := congrArg (fun field : StageNineHolonomicConfiguration =>
    field.gravityAuxiliary 0 3 0) equal
  have delta := remainder_change u positive
  rw [component, sub_self] at delta
  exact (mul_ne_zero (neg_ne_zero.mpr nonzero) (ne_of_gt lapse_pos)) delta.symm

/-- This two-parameter initial family is not closed under the actual mother
write. The full field and its generated remainder carry the successor. -/
theorem next_not_two_parameter (u : ℝ) (positive : 0 < 1 + u) (nonzero : u ≠ 0)
    (otherClock otherB : ℝ) :
    nextField u positive ≠ clockBFConfiguration otherClock otherB := by
  intro equal
  apply remainder_changes u positive nonzero
  rw [initial_encoded]
  change remainder (nextField u positive) = Runtime.configuration
  rw [equal, configuration_eq_displace, source_displacement_remainder]

/-- A nonzero amplitude read from the fixed original source, not a caller
clock or a replacement physical-time normalization. -/
def sourceClockSeed : ℝ := motherSource.legacy.sigma

theorem sourceClockSeed_value : sourceClockSeed = 1 / 2 := by
  change positiveSmoothUnifiedSource.legacy.sigma = 1 / 2
  exact positiveSource_sigma

theorem sourceClockSeed_domain : 0 < 1 + sourceClockSeed := by
  rw [sourceClockSeed_value]
  norm_num

theorem sourceClockSeed_nonzero : sourceClockSeed ≠ 0 := by
  rw [sourceClockSeed_value]
  norm_num

def sourcePrepared : MaterialState := prepared sourceClockSeed sourceClockSeed_domain

theorem source_remainder_change :
    (encodedAt sourceClockSeed sourceClockSeed_domain 1).2.val.gravityAuxiliary 0 3 0 -
      (encodedAt sourceClockSeed sourceClockSeed_domain 0).2.val.gravityAuxiliary 0 3 0 = -lapse / 2 := by
  rw [remainder_change, sourceClockSeed_value]
  ring

set_option maxHeartbeats 2000000 in
/-- The source-only instance consumes the original emitter, native action,
complete patch and successor. The visit, not its field encoding, owns history. -/
theorem source_feedback_consumed :
    let event := NativeFamily.occurrenceAt sourcePrepared 0
    let successor := NativeFamily.successorAt sourcePrepared 0
    event = SpinPair.emitted (.running sourcePrepared) ∧
    SpinPair.source.toRootSource.actual.compile event =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running sourcePrepared))) ∧
    successor.targetCurrent = (NativeFamily.visitAt sourcePrepared 1).current ∧
    successor.ledgerEvolution = (SpinPair.generatedPatch event).toLedgerWriteEvolution ∧
    wholeSplit.symm (encodedAt sourceClockSeed sourceClockSeed_domain 1) =
      Recognition.wholeField successor.targetCurrent ∧
    (encodedAt sourceClockSeed sourceClockSeed_domain 1).2.val ≠
      (encodedAt sourceClockSeed sourceClockSeed_domain 0).2.val ∧
    ∀ u b : ℝ, Recognition.wholeField successor.targetCurrent ≠ clockBFConfiguration u b := by
  obtain ⟨compiled, next, recovery, _, patch⟩ :=
    native_encoded_next sourceClockSeed sourceClockSeed_domain 0
  exact ⟨rfl, compiled, next, patch, recovery,
    remainder_changes sourceClockSeed sourceClockSeed_domain sourceClockSeed_nonzero,
    fun u b => next_not_two_parameter sourceClockSeed sourceClockSeed_domain sourceClockSeed_nonzero u b⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFFeedback
