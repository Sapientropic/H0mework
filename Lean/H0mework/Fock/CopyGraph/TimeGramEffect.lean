import H0mework.Fock.CopyGraph.TimeGramFinite

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index)
open SourceCopyTimeModel (Packet)
open scoped Classical
noncomputable section

theorem part_axes (depth : Nat) (index : Index depth) (phase : Fin (index.val + 1)) (mass clock : ℂ) :
    SourceCopyTimeEnergy.part depth index phase (SourceCopyGraph.axes mass clock) = 0 := by
  apply norm_eq_zero.mp
  exact (SourceCopyTimeEnergy.part_norm depth index phase (SourceCopyGraph.axes mass clock)).trans (norm_zero)

theorem axes_next (mass clock : ℂ) :
    SourceJointClockGraph.action (SourceCopyGraph.axes mass clock) = SourceCopyGraph.axes mass (clock + mass) := by
  rw [SourceJointClockGraph.action_apply]
  change WithLp.toLp 2 (WithLp.toLp 2 (SourceOwnedObservationHistory.SourceShift.shift 0, mass), clock + mass) = _
  rw [map_zero]
  rfl

abbrev twoIndex : Index 2 := ⟨1, by decide⟩

theorem two_index_source : twoIndex = (1 : Index 2) := by decide

private theorem sum_phases_two {M : Type*} [AddCommMonoid M] (f : Fin (twoIndex.val + 1) → M) :
    (∑ phase, f phase) = f 0 + f 1 := by
  change (∑ phase : Fin 2, f phase) = f 0 + f 1
  exact Fin.sum_univ_two f

theorem two_mean : meanPhase 2 twoIndex = 1 / 2 := by
  unfold meanPhase
  rw [sum_phases_two, SourceCopyProgram.scale_source]
  norm_num

theorem two_normalizer : normalizer 2 twoIndex = 17 / 8 := by
  unfold normalizer spread
  rw [sum_phases_two, two_mean, SourceCopyProgram.scale_source]
  norm_num

theorem decode_two (firstMass firstClock lastMass lastClock : ℂ) :
    decode 2 twoIndex ![SourceCopyGraph.axes firstMass firstClock, SourceCopyGraph.axes lastMass lastClock] =
      SourceCopyGraph.axes ((8 / 17 : ℂ) * (firstMass + lastMass + (lastClock - firstClock) / 4))
        (firstClock + lastClock - (4 / 17 : ℂ) * (firstMass + lastMass + (lastClock - firstClock) / 4)) := by
  unfold decode solve synthesis
  simp only [sum_phases_two, Matrix.cons_val_zero, Matrix.cons_val_one, part_axes, zero_add,
    two_mean, two_normalizer, SourceCopyProgram.scale_source]
  apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
  apply Prod.ext
  · apply (WithLp.linearEquiv 2 ℂ (SourceOwnedObservationHistory.SourceShift.H × ℂ)).injective
    apply Prod.ext
    · rfl
    · norm_num [SourceCopyGraph.axes, SourceCopyTimeModel.mass, SourceCopyTimeModel.hilbert,
        SourceJointClockGraph.joint, SourceJointClockGraph.clock, SourceMassCompletion.massRead, SourceMassCompletion.firstRead]
      ring
  · norm_num [SourceCopyGraph.axes, SourceCopyTimeModel.mass, SourceCopyTimeModel.hilbert,
      SourceJointClockGraph.joint, SourceJointClockGraph.clock, SourceMassCompletion.massRead, SourceMassCompletion.firstRead]
    ring

def stale : Packet 2 twoIndex := fun _ =>
  SourceJointClockGraph.recover (SourceJointClockGraph.read
    (SourceClockComplex.ofNative (SourceOwnedObservationHistory.sourcePoint 0)))

theorem stale_source : stale = ![SourceCopyGraph.axes 1 0, SourceCopyGraph.axes 1 0] := by
  funext phase
  fin_cases phase <;> exact SourceJointClockGraph.root_unit_recovery

theorem stale_next : SourceCopyTimeModel.next 2 twoIndex stale =
    ![SourceCopyGraph.axes 1 0, SourceCopyGraph.axes 1 1] := by
  rw [stale_source]
  funext phase
  fin_cases phase
  · rfl
  · change SourceJointClockGraph.action (SourceCopyGraph.axes 1 0) = SourceCopyGraph.axes 1 1
    rw [axes_next, zero_add]

theorem stale_correction : decode 2 twoIndex (SourceCopyTimeModel.next 2 twoIndex stale) -
    SourceJointClockGraph.action (decode 2 twoIndex stale) = SourceCopyGraph.axes (2 / 17) 0 := by
  rw [stale_next, stale_source, decode_two, decode_two, axes_next]
  norm_num [SourceCopyGraph.axes, ← WithLp.toLp_sub, Prod.mk_sub_mk]

theorem stale_feedback_nonzero : decode 2 twoIndex (SourceCopyTimeModel.next 2 twoIndex
    (WithLp.ofLp (residual 2 twoIndex stale))) ≠ 0 := by
  rw [← next_correction, stale_correction]
  intro zero
  have mass := congrArg SourceCopyTimeModel.mass zero
  change (2 / 17 : ℂ) = 0 at mass
  norm_num at mass

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
