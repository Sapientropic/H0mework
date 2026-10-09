import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerActuation
import H0mework.Chemistry.LAlanineThermalLoad.EnergyNorm

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open Collision Measurement Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem boundedEffect_strict (A rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) :
    0 < energy (boundedEffect A) rho ∧ energy (boundedEffect A) rho < 1 := by
  have bound := abs_le.mp (energy_abs_le_norm A rho positive normalized)
  have M := measurementScale_pos A
  have scaled : (2 * measurementScale A) * energy (boundedEffect A) rho =
      measurementScale A + energy A rho := by
    rw [boundedEffect_read A rho normalized]
    field_simp
  have scale : measurementScale A = 1 + ‖A‖ := rfl
  constructor <;> nlinarith

omit [DecidableEq ι] in
theorem prepared_one_read (rho : Matrix ι ι ℂ) : oneRead (prepared rho) = 0 := by
  simp [oneRead, prepared]
end Generic

theorem sourceTarget_strict : 0 < zeroRead sourceTarget ∧ zeroRead sourceTarget < 1 := by
  rw [sourceTarget_zero, sourceEffect, Incidence.bodyObservable_energy]
  exact boundedEffect_strict (sourceOutputObservable Load.Source.loadTotalHamiltonian)
    (Incidence.bodyRead received.joint) (Incidence.bodyRead_positive _ received.positive)
    ((Incidence.bodyRead_trace _).trans received.normalized)

theorem sourceTarget_one_positive : 0 < oneRead sourceTarget := by
  have binary := sourceTarget_binary.2.2
  have upper := sourceTarget_strict.2
  linarith

def pointerEnergy (joint : PointerJoint) : ℝ := 2 * oneRead joint

theorem sourceInitial_pointerEnergy : pointerEnergy sourceInitial = 0 := by
  rw [pointerEnergy, sourceInitial, prepared_one_read, mul_zero]

theorem sourceTarget_pointerEnergy : 0 < pointerEnergy sourceTarget :=
  mul_pos (by norm_num) sourceTarget_one_positive

theorem sourceTarget_not_prepared : sourceTarget ≠ sourceInitial := by
  intro same
  have changed := sourceTarget_pointerEnergy
  rw [same, sourceInitial_pointerEnergy] at changed
  exact (lt_irrefl _) changed

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
