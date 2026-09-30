import H0mework.Fock.CopyGraph.Native

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead realize retained hilbertLift)
open SourceCopySharedNext (NextPacket gain)
open SourceCopyTimeModel (phaseAt finitePhases hilbert mass)
open SourceOwnedObservationHistory.SourceShift (basis)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def slice (runtime : LivingRuntimeState process) (value : Coordinates runtime (maximumIndex runtime) 0)
    (phase : Fin ((maximumIndex runtime).val + 1)) : SourceJointClockGraph.Carrier :=
  realize runtime (maximumIndex runtime) 0
    ((fun coordinate => if phaseAt (inventoryBound runtime) (maximumIndex runtime) coordinate.val = phase
      then value.1 coordinate else 0), 0, 0)

theorem slice_coordinate (runtime : LivingRuntimeState process) (value : Coordinates runtime (maximumIndex runtime) 0)
    (phase : Fin ((maximumIndex runtime).val + 1))
    (coordinate : Fin (SourceCopyRecordedRecurrence.cutoff runtime (maximumIndex runtime) 0 + 1)) :
    hilbert (slice runtime value phase) coordinate.val =
      if phaseAt (inventoryBound runtime) (maximumIndex runtime) coordinate.val = phase then value.1 coordinate else 0 :=
  congrArg (fun result : Coordinates runtime (maximumIndex runtime) 0 => result.1 coordinate)
    (SourceCopyCurrentCoordinates.realize_source runtime (maximumIndex runtime) 0
      ((fun address => if phaseAt (inventoryBound runtime) (maximumIndex runtime) address.val = phase then value.1 address else 0), 0, 0))

theorem slice_sum (runtime : LivingRuntimeState process) (value : Coordinates runtime (maximumIndex runtime) 0)
    (massZero : value.2.1 = 0) (clockZero : value.2.2 = 0) :
    ∑ phase, slice runtime value phase = realize runtime (maximumIndex runtime) 0 value := by
  simp only [slice, ← map_sum]
  congr 1
  change (∑ phase, ((fun coordinate => if phaseAt (inventoryBound runtime) (maximumIndex runtime) coordinate.val = phase then value.1 coordinate else 0), (0 : ℂ), (0 : ℂ))) = value
  apply Prod.ext
  · funext coordinate
    simp only [Prod.fst_sum, Finset.sum_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · apply Prod.ext
    · simpa only [Prod.snd_sum, Prod.fst_sum, Finset.sum_const_zero] using massZero.symm
    · simpa only [Prod.snd_sum, Finset.sum_const_zero] using clockZero.symm

theorem slice_orthogonal (runtime : LivingRuntimeState process)
    (left right : Coordinates runtime (maximumIndex runtime) 0)
    (first second : Fin ((maximumIndex runtime).val + 1)) (different : first ≠ second) :
    ⟪slice runtime left first, slice runtime right second⟫_ℂ = 0 := by
  dsimp only [slice, realize, LinearMap.coe_mk, AddHom.coe_mk]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  with_reducible change (⟪hilbertLift runtime (maximumIndex runtime) 0 (fun coordinate =>
      if phaseAt (inventoryBound runtime) (maximumIndex runtime) coordinate.val = first then left.1 coordinate else 0),
    hilbertLift runtime (maximumIndex runtime) 0 (fun coordinate =>
      if phaseAt (inventoryBound runtime) (maximumIndex runtime) coordinate.val = second then right.1 coordinate else 0)⟫_ℂ +
    ⟪(0 : ℂ), 0⟫_ℂ) + ⟪(0 : ℂ), 0⟫_ℂ = 0
  rw [inner_zero_left, add_zero, add_zero]
  rw [hilbertLift, LinearMap.sum_apply, sum_inner]
  apply Finset.sum_eq_zero
  intro coordinate _
  change ⟪(if phaseAt (inventoryBound runtime) (maximumIndex runtime) coordinate.val = first then left.1 coordinate else 0) •
    basis coordinate.val, hilbertLift runtime (maximumIndex runtime) 0 _⟫_ℂ = 0
  rw [inner_smul_left]
  simp only [basis, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one,
    SourceCopyCurrentCoordinates.hilbert_lift_at]
  by_cases selected : phaseAt (inventoryBound runtime) (maximumIndex runtime) coordinate.val = first
  · rw [if_pos selected, if_neg (fun other => different (selected.symm.trans other)), mul_zero]
  · rw [if_neg selected, map_zero, zero_mul]

theorem slice_energy (runtime : LivingRuntimeState process) (value : Coordinates runtime (maximumIndex runtime) 0)
    (massZero : value.2.1 = 0) (clockZero : value.2.2 = 0) :
    ∑ phase, ‖slice runtime value phase‖ ^ 2 = ‖realize runtime (maximumIndex runtime) 0 value‖ ^ 2 := by
  have diagonal : ⟪∑ phase, slice runtime value phase, ∑ phase, slice runtime value phase⟫_ℂ =
      ∑ phase, ⟪slice runtime value phase, slice runtime value phase⟫_ℂ := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro phase _
    rw [inner_sum, Finset.sum_eq_single phase]
    · intro other _ different
      exact slice_orthogonal runtime value value phase other different.symm
    · intro absent
      exact (absent (Finset.mem_univ phase)).elim
  rw [slice_sum runtime value massZero clockZero] at diagonal
  have normRe (target : SourceJointClockGraph.Carrier) : (⟪target, target⟫_ℂ).re = ‖target‖ ^ 2 := by
    exact inner_self_eq_norm_sq (𝕜 := ℂ) target
  simpa only [Complex.re_sum, normRe] using (congrArg Complex.re diagonal).symm

theorem slice_tail_energy (runtime : LivingRuntimeState process) (value : Coordinates runtime (maximumIndex runtime) 0)
    (phase : Fin ((maximumIndex runtime).val + 1)) (target : SourceJointClockGraph.Carrier) :
    ‖SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target + slice runtime value phase‖ ^ 2 =
      ‖SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target‖ ^ 2 + ‖slice runtime value phase‖ ^ 2 := by
  have kept : retained runtime (maximumIndex runtime) 0 (slice runtime value phase) = slice runtime value phase := by
    simp only [slice, retained, LinearMap.comp_apply, SourceCopyCurrentCoordinates.realize_source]
  have orthogonal := SourceCopyCurrentCoordinates.retained_orthogonal runtime (maximumIndex runtime) 0 (slice runtime value phase) target
  rw [kept] at orthogonal
  have budget := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (slice runtime value phase)
    (SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target) orthogonal
  have normalized : ‖slice runtime value phase + SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target‖ ^ 2 =
      ‖slice runtime value phase‖ ^ 2 + ‖SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target‖ ^ 2 := by
    simpa only [pow_two] using budget
  rw [add_comm (SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target)]
  exact normalized.trans (add_comm _ _)

theorem gain_mass (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime) :
    mass (gain runtime previous packet) = 0 := by
  change previous.2.1 - previous.2.1 = 0
  exact sub_self _

theorem gain_clock (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime) :
    SourceJointClockGraph.clock (gain runtime previous packet) = 0 := by
  change (previous.2.2 + previous.2.1) - (previous.2.2 + previous.2.1) = 0
  exact sub_self _

theorem gain_retained (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime) :
    retained runtime.tick.next (maximumIndex runtime.tick.next) 0 (gain runtime previous packet) = gain runtime previous packet := by
  have old : retained runtime (maximumIndex runtime) 0 (realize runtime (maximumIndex runtime) 0 previous) =
      realize runtime (maximumIndex runtime) 0 previous := by
    simp only [retained, LinearMap.comp_apply, SourceCopyCurrentCoordinates.realize_source]
  have tail := SourceCopySharedNext.old_time_retained_tail_zero runtime (realize runtime (maximumIndex runtime) 0 previous)
  rw [old] at tail
  have kept := SourceCopyCurrentCoordinates.reconstruction runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous))
  rw [tail, add_zero] at kept
  rw [gain, map_sub, kept]
  have new : retained runtime.tick.next (maximumIndex runtime.tick.next) 0
      (realize runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceCopySharedNext.update runtime previous packet)) =
      realize runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceCopySharedNext.update runtime previous packet) := by
    simp only [retained, LinearMap.comp_apply, SourceCopyCurrentCoordinates.realize_source]
  rw [new]

def phaseGain (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) : SourceJointClockGraph.Carrier :=
  slice runtime.tick.next (sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (gain runtime previous packet)) phase

theorem phase_sum (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime) :
    ∑ phase, phaseGain runtime previous packet phase = gain runtime previous packet := by
  simp only [phaseGain]
  rw [slice_sum runtime.tick.next _ (gain_mass runtime previous packet) (gain_clock runtime previous packet)]
  exact gain_retained runtime previous packet

theorem phase_energy (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime) :
    ∑ phase, ‖phaseGain runtime previous packet phase‖ ^ 2 = ‖gain runtime previous packet‖ ^ 2 := by
  simp only [phaseGain]
  rw [slice_energy runtime.tick.next _ (gain_mass runtime previous packet) (gain_clock runtime previous packet)]
  rw [show realize runtime.tick.next (maximumIndex runtime.tick.next) 0
      (sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (gain runtime previous packet)) = gain runtime previous packet from
    gain_retained runtime previous packet]

theorem phase_budget (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    (∑ phase, ‖phaseGain runtime (sourceRead runtime (maximumIndex runtime) 0 target)
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) phase‖ ^ 2) +
      ‖SourceCopyCurrentCoordinates.residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)‖ ^ 2 =
        ‖SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target‖ ^ 2 := by
  rw [phase_energy]
  exact SourceCopySharedNext.gain_budget runtime target

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
