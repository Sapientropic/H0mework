import H0mework.Versions.X.Fock.CopyGraph.TimeGramNormal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index)
open SourceCopyTimeModel (Packet phases)
open scoped Classical InnerProductSpace
noncomputable section

def decode (depth : Nat) (index : Index depth) (packet : Packet depth index) : SourceJointClockGraph.Carrier :=
  solve depth index (synthesis depth index packet)

def residual (depth : Nat) (index : Index depth) (packet : Packet depth index) : Frame depth index :=
  WithLp.toLp 2 packet - analysis depth index (decode depth index packet)

theorem analysis_packet (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    analysis depth index value = WithLp.toLp 2 (phases depth index value) := by
  apply PiLp.ext
  exact analysis_phase depth index value

theorem analysis_injective (depth : Nat) (index : Index depth) : Function.Injective (analysis depth index) := by
  intro left right same
  apply SourceCopyTimeModel.phases_injective depth index
  rw [analysis_packet, analysis_packet] at same
  exact WithLp.toLp_injective 2 same

theorem normal_injective (depth : Nat) (index : Index depth) :
    Function.Injective ((analysis depth index).adjoint ∘ analysis depth index) :=
  (analysis depth index).adjoint_comp_self_injective_iff.mpr (analysis_injective depth index)

theorem normal_equation (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    (analysis depth index).adjoint (analysis depth index (decode depth index packet)) =
      (analysis depth index).adjoint (WithLp.toLp 2 packet) := by
  rw [decode, solve_equation, adjoint_source]

theorem decode_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    decode depth index (phases depth index value) = value := by
  apply normal_injective depth index
  change (analysis depth index).adjoint (analysis depth index (decode depth index (phases depth index value))) = _
  rw [normal_equation, ← analysis_packet]
  rfl

theorem residual_normal (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    (analysis depth index).adjoint (residual depth index packet) = 0 := by
  rw [residual, map_sub, normal_equation, sub_self]

theorem reconstruction (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    analysis depth index (decode depth index packet) + residual depth index packet = WithLp.toLp 2 packet := by
  rw [residual]
  abel

theorem residual_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    residual depth index (phases depth index value) = 0 := by
  rw [residual, decode_source, analysis_packet, sub_self]

theorem residual_orthogonal (depth : Nat) (index : Index depth) (packet : Packet depth index)
    (value : SourceJointClockGraph.Carrier) : ⟪analysis depth index value, residual depth index packet⟫_ℂ = 0 := by
  have paired := (analysis depth index).adjoint_inner_right value (residual depth index packet)
  rw [residual_normal, inner_zero_right] at paired
  exact paired.symm

theorem error_energy (depth : Nat) (index : Index depth) (packet : Packet depth index)
    (proposal : SourceJointClockGraph.Carrier) :
    ‖WithLp.toLp 2 packet - analysis depth index proposal‖ ^ 2 =
      ‖residual depth index packet‖ ^ 2 + ‖analysis depth index (decode depth index packet - proposal)‖ ^ 2 := by
  have split : WithLp.toLp 2 packet - analysis depth index proposal =
      residual depth index packet + analysis depth index (decode depth index packet - proposal) := by
    rw [residual, map_sub]
    abel
  rw [split, norm_add_sq (𝕜 := ℂ), inner_eq_zero_symm.mp (residual_orthogonal depth index packet _)]
  simp only [map_zero, mul_zero, add_zero]

theorem minimum (depth : Nat) (index : Index depth) (packet : Packet depth index)
    (proposal : SourceJointClockGraph.Carrier) :
    ‖residual depth index packet‖ ^ 2 ≤ ‖WithLp.toLp 2 packet - analysis depth index proposal‖ ^ 2 := by
  rw [error_energy]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem minimum_fibre (depth : Nat) (index : Index depth) (packet : Packet depth index)
    (proposal : SourceJointClockGraph.Carrier) :
    ‖WithLp.toLp 2 packet - analysis depth index proposal‖ ^ 2 = ‖residual depth index packet‖ ^ 2 ↔
      proposal = decode depth index packet := by
  rw [error_energy, add_eq_left, sq_eq_zero_iff, norm_eq_zero]
  have zero : analysis depth index (decode depth index packet - proposal) = 0 ↔ decode depth index packet - proposal = 0 := by
    constructor
    · intro h
      exact analysis_injective depth index (h.trans (map_zero _).symm)
    · rintro h
      rw [h, map_zero]
  rw [zero, sub_eq_zero, eq_comm]

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
