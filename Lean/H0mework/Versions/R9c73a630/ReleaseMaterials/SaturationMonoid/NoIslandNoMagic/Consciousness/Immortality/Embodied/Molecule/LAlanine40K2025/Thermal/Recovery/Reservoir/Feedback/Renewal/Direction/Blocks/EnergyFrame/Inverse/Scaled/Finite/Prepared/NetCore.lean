import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.PointerCorner
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Receiver
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Consumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem tensor_hermitian {ι κ : Type*} (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (ha : A.IsHermitian) (hb : B.IsHermitian) : (Matrix.kronecker A B).IsHermitian := by
  change (Matrix.kronecker A B)ᴴ=_
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,ha.eq,hb.eq]

theorem doubled_hermitian {ι : Type*} (A : Matrix ι ι ℂ) (ha : A.IsHermitian) :
    (Matrix.fromBlocks A (0 : Matrix ι ι ℂ) 0 A).IsHermitian := by
  change (Matrix.fromBlocks A (0 : Matrix ι ι ℂ) 0 A)ᴴ=_
  simp only [Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero,ha.eq]

theorem pointer_PC_hermitian : Sectors.pointerPCObservable.IsHermitian :=
  doubled_hermitian _
    (tensor_hermitian _ _ (tensor_hermitian _ _ Powered.Producer.poweredTotalHamiltonian_hermitian (by simp)) (by simp))

theorem original_net_hermitian : (gainObservable Sectors.pointerPCObservable).IsHermitian :=
  (conjugation_hermitian (star afterInstrumentEleven) _ pointer_PC_hermitian).sub
    (conjugation_hermitian (star afterInstrumentNine) _ pointer_PC_hermitian)

def finiteRootGain : PointerJoint :=
  star SquareRoot.Full.sourcePointer *gainObservable Sectors.pointerPCObservable*SquareRoot.Full.sourcePointer

theorem finite_root_gain_hermitian : finiteRootGain.IsHermitian := by
  have paid := Matrix.isHermitian_mul_mul_conjTranspose (star SquareRoot.Full.sourcePointer) original_net_hermitian
  simpa only [finiteRootGain,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using paid

theorem sandwich_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (V A : Matrix ι ι ℂ) :
    ‖star V*A*V‖ ≤ ‖V‖^2*‖A‖ := by
  exact (norm_mul_le (star V*A) V).trans (by
    have product := mul_le_mul_of_nonneg_right (norm_mul_le (star V) A) (norm_nonneg V)
    simpa only [norm_star,pow_two,mul_assoc,mul_left_comm,mul_comm] using product)

theorem finite_root_gain_norm : ‖finiteRootGain‖ ≤ (124/1000 : ℝ) := by
  have normV : ‖SquareRoot.Full.sourcePointer‖ ≤ 1+(4/10^7 : ℝ) :=
    SquareRoot.approximated_pointer_norm SquareRoot.Full.sourceRoot SquareRoot.Full.sourceComplement
      SquareRoot.Full.source_whole_roots_error.1 SquareRoot.Full.source_whole_roots_error.2
  have bound : ‖finiteRootGain‖ ≤ ‖SquareRoot.Full.sourcePointer‖^2*‖gainObservable Sectors.pointerPCObservable‖ :=
    sandwich_norm SquareRoot.Full.sourcePointer (gainObservable Sectors.pointerPCObservable)
  exact bound.trans (by
    have product := mul_le_mul (pow_le_pow_left₀ (norm_nonneg SquareRoot.Full.sourcePointer) normV 2) original_net_PC_norm
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ (1+4/10^7)^2)
    norm_num at product
    exact product.trans (by norm_num))

theorem source_root_gain_read :
    Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine)=
      energy finiteRootGain sourceInitial := by
  rw [← Sectors.pointerPCObservable_energy,← Sectors.pointerPCObservable_energy]
  change energy Sectors.pointerPCObservable (Quantum.conjugation afterInstrumentEleven (SquareRoot.approximatedTarget _ _))-
    energy Sectors.pointerPCObservable (Quantum.conjugation afterInstrumentNine (SquareRoot.approximatedTarget _ _))=_
  rw [gain_read,SquareRoot.approximatedTarget,SquareRoot.raw_pullback]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
