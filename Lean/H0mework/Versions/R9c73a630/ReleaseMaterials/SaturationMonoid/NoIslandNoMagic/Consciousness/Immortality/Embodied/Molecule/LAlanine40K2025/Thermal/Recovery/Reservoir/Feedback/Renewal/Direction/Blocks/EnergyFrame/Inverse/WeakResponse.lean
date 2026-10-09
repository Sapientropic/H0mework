import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.ExchangeResponse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem local_unitary_star (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    star (Load.Quantum.localUnitary U V)=Load.Quantum.localUnitary (star U) (star V) := by
  apply Subtype.ext
  simp only [Load.Quantum.localUnitary,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.kronecker,
    Matrix.conjTranspose_kronecker]

theorem pair_free_PC_observable (time : ℝ) :
    Quantum.conjugation (star (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)))
      (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix PairController PairController ℂ))=
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix PairController PairController ℂ) := by
  have same : Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time)=
      Load.Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time) := rfl
  rw [same,local_unitary_star]
  have tensor := Load.Quantum.localConjugation_tensor (star (Native.freePCUnitary time)) (star (Native.freePCUnitary time))
    Powered.Producer.poweredTotalHamiltonian (1 : Matrix PairController PairController ℂ)
  have fixed : Quantum.conjugation (star (Native.freePCUnitary time)) (1 : Matrix PairController PairController ℂ)=1 :=
    map_one (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) (star (Native.freePCUnitary time)))
  rw [original_free_PC_observable,fixed] at tensor
  exact tensor

theorem original_weak_pair_response (time : ℝ) :
    ‖Quantum.conjugation (star (Weak.pairPulse time))
      (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix PairController PairController ℂ))-
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix PairController PairController ℂ)‖ ≤
      2*|time| * ‖Powered.Producer.poweredTotalHamiltonian‖ := by
  rw [Weak.pair_factor,star_mul,← Environment.conjugation_comp,pair_free_PC_observable]
  apply (exchange_observable_response time _).trans
  have norm := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := PairController))
    Powered.Producer.poweredTotalHamiltonian
  exact mul_le_mul_of_nonneg_left norm (by positivity)

theorem original_weak_body_response (time : ℝ) :
    ‖Quantum.conjugation (star (Weak.fullPulse time)) Sectors.pcObservable-Sectors.pcObservable‖ ≤
      2*|time| * ‖Powered.Producer.poweredTotalHamiltonian‖ := by
  unfold Weak.fullPulse
  rw [local_unitary_star]
  have tensor := Load.Quantum.localConjugation_tensor (star (Weak.pairPulse time))
    (star (Load.Recovery.Control.environmentUnitary time))
    (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix PairController PairController ℂ))
    (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have fixed : Quantum.conjugation (star (Load.Recovery.Control.environmentUnitary time)) (1 : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    map_one (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) (star (Load.Recovery.Control.environmentUnitary time)))
  rw [fixed] at tensor
  change Quantum.conjugation (Load.Quantum.localUnitary (star (Weak.pairPulse time))
    (star (Load.Recovery.Control.environmentUnitary time))) _ = _ at tensor
  unfold Sectors.pcObservable
  rw [tensor]
  have delta (A B : JointMatrix PairController) : Matrix.kronecker A (1 : Matrix (Fin 2) (Fin 2) ℂ)-
      Matrix.kronecker B (1 : Matrix (Fin 2) (Fin 2) ℂ)=Matrix.kronecker (A-B) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [delta]
  exact (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController × PairController) (κ := Fin 2)) _).trans
    (original_weak_pair_response time)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
