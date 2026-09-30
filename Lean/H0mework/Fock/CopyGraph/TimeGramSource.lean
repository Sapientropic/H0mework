import H0mework.Fock.CopyGraph.TimeEnergyObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (Packet phases hilbert mass time timeRecovery)
open SourceOwnedObservationHistory.SourceShift (H shift)
open scoped Classical InnerProductSpace
noncomputable section

abbrev Frame (depth : Nat) (index : Index depth) := PiLp 2 (fun _ : Fin (index.val + 1) => SourceJointClockGraph.Carrier)

def analysis (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier →L[ℂ] Frame depth index :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (index.val + 1) => SourceJointClockGraph.Carrier)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun phase => (SourceCopyGraph.recover depth index).comp (time phase.val))

theorem analysis_phase (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) : analysis depth index value phase = phases depth index value phase :=
  (SourceCopyTimeModel.phase_source depth index value phase).symm

theorem analysis_energy (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖analysis depth index value‖ ^ 2 = ∑ phase : Fin (index.val + 1), ‖phases depth index value phase‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [analysis_phase]

theorem recover_hilbert (value : SourceJointClockGraph.Carrier) :
    hilbert (SourceJointClockGraph.recover value) = IsometricRetainedTransfer.transfer shift (hilbert value) := by
  rw [SourceJointClockGraph.recover_apply]
  change SourceMassCompletion.firstRead (SourceJointTransfer.wholeTransfer (SourceJointClockGraph.joint value)) = _
  rw [SourceJointTransfer.whole_transfer]
  rfl

theorem time_pair (steps : Nat) (left right : SourceJointClockGraph.Carrier) :
    ⟪hilbert (time steps left), hilbert right⟫_ℂ =
      ⟪hilbert left, hilbert (timeRecovery steps right)⟫_ℂ := by
  induction steps generalizing right with
  | zero => rfl
  | succ steps previous =>
    rw [SourceCopyTimeModel.time_succ, SourceCopyTimeModel.hilbert_next]
    have step : ⟪shift (hilbert (time steps left)), hilbert right⟫_ℂ =
        ⟪hilbert (time steps left), hilbert (SourceJointClockGraph.recover right)⟫_ℂ := by
      rw [recover_hilbert]
      exact (shift.toContinuousLinearMap.adjoint_inner_right _ _).symm
    rw [step, previous, ← SourceCopyTimeModel.time_recovery_succ]

theorem phase_pair (depth : Nat) (index : Index depth) (phase : Fin (index.val + 1))
    (left right : SourceJointClockGraph.Carrier) :
    ⟪hilbert (phases depth index left phase), hilbert right⟫_ℂ =
      ⟪hilbert left, SourceCopyTimeEnergy.part depth index phase right⟫_ℂ := by
  rw [SourceCopyTimeModel.phase_source]
  change ⟪(SourceCopyGraph.hilbertAction depth index).toContinuousLinearMap.adjoint (hilbert (time phase.val left)), hilbert right⟫_ℂ = _
  rw [(SourceCopyGraph.hilbertAction depth index).toContinuousLinearMap.adjoint_inner_left]
  exact time_pair phase.val left (SourceCopyGraph.action depth index right)

def synthesis (depth : Nat) (index : Index depth) (packet : Packet depth index) : SourceJointClockGraph.Carrier :=
  WithLp.toLp 2 (WithLp.toLp 2
    ((∑ phase : Fin (index.val + 1), SourceCopyTimeEnergy.part depth index phase (packet phase)),
      ∑ phase : Fin (index.val + 1), (mass (packet phase) +
        ((phase.val : ℂ) / (scale depth index : ℂ)) * SourceJointClockGraph.clock (packet phase))),
    ∑ phase : Fin (index.val + 1), (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock (packet phase))

theorem phase_mass (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) : mass (phases depth index value phase) = mass value := by
  rw [SourceCopyTimeModel.phase_source]
  change mass (time phase.val value) = _
  exact SourceCopyTimeModel.time_mass phase.val value

theorem phase_clock (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) :
    SourceJointClockGraph.clock (phases depth index value phase) =
      (scale depth index : ℂ)⁻¹ * (SourceJointClockGraph.clock value + (phase.val : ℂ) * mass value) := by
  rw [SourceCopyTimeModel.phase_source]
  change (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock (time phase.val value) = _
  rw [SourceCopyTimeModel.time_clock]

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
