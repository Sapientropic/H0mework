import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.PointerNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.BodyMeasurement
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerActuation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def approximatedBodyEffect (B : Load.Source.LoadedJoint) : Current.FullJoint :=
  Incidence.bodyObservable (boundedEffect B)

theorem approximated_body_lawful (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) :
    (approximatedBodyEffect B).PosSemidef ∧ (1-approximatedBodyEffect B).PosSemidef :=
  bodyObservable_lawful _ (boundedEffect_positive B hermitian) (boundedEffect_complement_positive B hermitian)

def approximatedPointerUnitary (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) :
    Matrix.unitaryGroup PointerIndex ℂ := dilation (approximatedBodyEffect B)
      (approximated_body_lawful B hermitian).1 (approximated_body_lawful B hermitian).2

theorem original_pointer_action_error (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) :
    ‖(sourceUnitary : PointerJoint)-(approximatedPointerUnitary B hermitian : PointerJoint)‖ ≤
      2*rootErrorBudget (sourceOutputObservable Load.Source.loadTotalHamiltonian) B := by
  have ha := sourceOutputObservable_hermitian Load.Source.loadTotalHamiltonian Load.Source.loadTotalHamiltonian_hermitian
  have root := effect_root_error (sourceOutputObservable Load.Source.loadTotalHamiltonian) B ha hermitian
  have complement := complement_root_error (sourceOutputObservable Load.Source.loadTotalHamiltonian) B ha hermitian
  change ‖dilationMatrix sourceEffect-dilationMatrix (approximatedBodyEffect B)‖ ≤ _
  apply (pointer_dilation_error _ _).trans
  have first : ‖effectRoot sourceEffect-effectRoot (approximatedBodyEffect B)‖ ≤
      rootErrorBudget (sourceOutputObservable Load.Source.loadTotalHamiltonian) B := by
    apply (body_root_error _ _ (boundedEffect_positive _ ha) (boundedEffect_positive B hermitian)).trans root
  have second : ‖complementRoot sourceEffect-complementRoot (approximatedBodyEffect B)‖ ≤
      rootErrorBudget (sourceOutputObservable Load.Source.loadTotalHamiltonian) B := by
    change ‖CFC.sqrt (1-Incidence.bodyObservable (boundedEffect _))-
      CFC.sqrt (1-Incidence.bodyObservable (boundedEffect B))‖ ≤ _
    rw [bodyObservable_complement,bodyObservable_complement]
    exact (body_root_error _ _ (boundedEffect_complement_positive _ ha)
      (boundedEffect_complement_positive B hermitian)).trans complement
  linarith

/-- The complete actual instrument output is compared, including both pointer branches and coherence. -/
theorem original_pointer_state_error (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) :
    ‖sourceTarget-Quantum.conjugation (approximatedPointerUnitary B hermitian) sourceInitial‖ ≤
      4*rootErrorBudget (sourceOutputObservable Load.Source.loadTotalHamiltonian) B*‖sourceInitial‖ := by
  rw [sourceTarget_generated]
  exact (conjugation_action_error sourceUnitary (approximatedPointerUnitary B hermitian) sourceInitial).trans
    (by nlinarith [mul_le_mul_of_nonneg_right (original_pointer_action_error B hermitian) (norm_nonneg sourceInitial)])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
