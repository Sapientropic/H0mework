import H0mework.Chemistry.LAlanineEntropy.SpectralEntropy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerBlockReadout

/-! The original diagonal PMF reads both raw matrix blocks without changing their weight. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born

open scoped ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι]
variable (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (positive : joint.PosSemidef) (normalized : joint.trace = 1)

theorem diagonal_pointer_zero :
    (((Quantum.diagonalPMF joint positive normalized).map
      (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)))) 0).toReal = zeroRead joint := by
  have sum : ((Quantum.diagonalPMF joint positive normalized).map
      (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)))) 0 =
      ∑ index : ι, Quantum.diagonalPMF joint positive normalized (Sum.inl index) := by
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]
    simp
  rw [sum, ENNReal.toReal_sum
    (fun index _ => (Quantum.diagonalPMF joint positive normalized).apply_ne_top (Sum.inl index))]
  simp_rw [Quantum.diagonalPMF_toReal]
  rw [← Complex.re_sum]
  rfl

theorem diagonal_pointer_one :
    (((Quantum.diagonalPMF joint positive normalized).map
      (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)))) 1).toReal = oneRead joint := by
  have sum : ((Quantum.diagonalPMF joint positive normalized).map
      (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)))) 1 =
      ∑ index : ι, Quantum.diagonalPMF joint positive normalized (Sum.inr index) := by
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]
    simp
  rw [sum, ENNReal.toReal_sum
    (fun index _ => (Quantum.diagonalPMF joint positive normalized).apply_ne_top (Sum.inr index))]
  simp_rw [Quantum.diagonalPMF_toReal]
  rw [← Complex.re_sum]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
