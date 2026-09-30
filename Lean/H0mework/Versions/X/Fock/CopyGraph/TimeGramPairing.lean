import H0mework.Versions.X.Fock.CopyGraph.TimeGramSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (Packet phases hilbert mass)
open scoped Classical InnerProductSpace
noncomputable section

theorem axes_pair (size phase : Nat) (sourceMass sourceClock readMass readClock : ℂ) :
    ⟪sourceMass, readMass⟫_ℂ + ⟪(size : ℂ)⁻¹ * (sourceClock + (phase : ℂ) * sourceMass), readClock⟫_ℂ =
      ⟪sourceMass, readMass + ((phase : ℂ) / (size : ℂ)) * readClock⟫_ℂ +
        ⟪sourceClock, (size : ℂ)⁻¹ * readClock⟫_ℂ := by
  simp only [RCLike.inner_apply, map_mul, map_add, map_inv₀, map_natCast, div_eq_mul_inv]
  ring

theorem source_pairing (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (packet : Packet depth index) :
    ⟪analysis depth index value, WithLp.toLp 2 packet⟫_ℂ = ⟪value, synthesis depth index packet⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [analysis_phase, WithLp.prod_inner_apply]
  change (∑ phase : Fin (index.val + 1),
    ((⟪hilbert (phases depth index value phase), hilbert (packet phase)⟫_ℂ +
      ⟪mass (phases depth index value phase), mass (packet phase)⟫_ℂ) +
      ⟪SourceJointClockGraph.clock (phases depth index value phase), SourceJointClockGraph.clock (packet phase)⟫_ℂ)) =
    (⟪hilbert value, ∑ phase : Fin (index.val + 1), SourceCopyTimeEnergy.part depth index phase (packet phase)⟫_ℂ +
      ⟪mass value, ∑ phase : Fin (index.val + 1), (mass (packet phase) +
        ((phase.val : ℂ) / (scale depth index : ℂ)) * SourceJointClockGraph.clock (packet phase))⟫_ℂ) +
    ⟪SourceJointClockGraph.clock value, ∑ phase : Fin (index.val + 1),
      (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock (packet phase)⟫_ℂ
  simp only [inner_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro phase _
  rw [phase_pair, phase_mass, phase_clock]
  simpa only [add_assoc] using congrArg
    (fun paired => ⟪hilbert value, SourceCopyTimeEnergy.part depth index phase (packet phase)⟫_ℂ + paired)
    (axes_pair (scale depth index) phase.val (mass value) (SourceJointClockGraph.clock value)
      (mass (packet phase)) (SourceJointClockGraph.clock (packet phase)))

theorem adjoint_source (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    (analysis depth index).adjoint (WithLp.toLp 2 packet) = synthesis depth index packet := by
  apply ext_inner_left ℂ
  intro value
  rw [(analysis depth index).adjoint_inner_right]
  exact source_pairing depth index value packet

def gram (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  WithLp.toLp 2 (WithLp.toLp 2 (hilbert value,
    ∑ phase : Fin (index.val + 1), (mass value + ((phase.val : ℂ) / (scale depth index : ℂ)) *
      ((scale depth index : ℂ)⁻¹ * (SourceJointClockGraph.clock value + (phase.val : ℂ) * mass value)))),
    ∑ phase : Fin (index.val + 1), (scale depth index : ℂ)⁻¹ *
      ((scale depth index : ℂ)⁻¹ * (SourceJointClockGraph.clock value + (phase.val : ℂ) * mass value)))

theorem gram_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    (analysis depth index).adjoint (analysis depth index value) = gram depth index value := by
  have packet : analysis depth index value = WithLp.toLp 2 (phases depth index value) := by
    apply PiLp.ext
    exact analysis_phase depth index value
  rw [packet, adjoint_source]
  have h := SourceCopyTimeEnergy.restore_hilbert depth index (phases depth index value)
  rw [SourceCopyTimeModel.restore_source] at h
  unfold synthesis gram
  simp only [phase_mass, phase_clock, ← h]

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
