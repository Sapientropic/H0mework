import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Pointer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Collision Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rawDilation (R S : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  pointerDiagonal R+pointerDiagonal S*pointerQuarter

theorem raw_dilation_read (R S : Matrix ι ι ℂ) : rawDilation R S=Matrix.fromBlocks R (-S) S R := by
  change Matrix.fromBlocks R 0 0 R+Matrix.fromBlocks S 0 0 S*Matrix.fromBlocks 0 (-1) 1 0=_
  rw [Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp

theorem raw_dilation_exact (E : Matrix ι ι ℂ) : rawDilation (effectRoot E) (complementRoot E)=dilationMatrix E := by
  rw [raw_dilation_read]
  rfl

theorem raw_dilation_error (R S T V : Matrix ι ι ℂ) :
    ‖rawDilation R S-rawDilation T V‖ ≤ ‖R-T‖+‖S-V‖ := by
  have split : rawDilation R S-rawDilation T V=pointerDiagonal (R-T)+pointerDiagonal (S-V)*pointerQuarter := by
    simp only [rawDilation,map_sub,sub_mul]
    abel
  rw [split]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact NonUnitalStarAlgHom.norm_apply_le pointerDiagonal _
  · rw [CStarRing.norm_mul_mem_unitary _ (pointer_quarter_unitary (ι := ι))]
    exact NonUnitalStarAlgHom.norm_apply_le pointerDiagonal _

def rawConjugation (V rho : Matrix ι ι ℂ) : Matrix ι ι ℂ := V*rho*star V

omit [DecidableEq ι] in
theorem raw_pullback (O V rho : Matrix ι ι ℂ) : energy O (rawConjugation V rho)=energy (star V*O*V) rho := by
  unfold energy rawConjugation
  rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

theorem raw_observable_error (O rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace=1)
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix ι ι ℂ) :
    |energy O (Quantum.conjugation U rho)-energy O (rawConjugation V rho)| ≤
      (1+‖V‖)*‖O‖*‖(U : Matrix ι ι ℂ)-V‖ := by
  change |energy O (rawConjugation (U : Matrix ι ι ℂ) rho)-energy O (rawConjugation V rho)| ≤ _
  rw [raw_pullback,raw_pullback]
  have difference : energy (star (U : Matrix ι ι ℂ)*O*(U : Matrix ι ι ℂ)) rho-energy (star V*O*V) rho=
      energy (star (U : Matrix ι ι ℂ)*O*(U : Matrix ι ι ℂ)-star V*O*V) rho := by
    simp only [energy,sub_mul,Matrix.trace_sub,Complex.sub_re]
  rw [difference]
  apply (energy_abs_le_norm _ rho positive normalized).trans
  have split : star (U : Matrix ι ι ℂ)*O*(U : Matrix ι ι ℂ)-star V*O*V=
      (star (U : Matrix ι ι ℂ)-star V)*O*(U : Matrix ι ι ℂ)+star V*O*((U : Matrix ι ι ℂ)-V) := by noncomm_ring
  rw [split]
  calc
    _ ≤ ‖(star (U : Matrix ι ι ℂ)-star V)*O*(U : Matrix ι ι ℂ)‖+‖star V*O*((U : Matrix ι ι ℂ)-V)‖ := norm_add_le _ _
    _ ≤ ‖(U : Matrix ι ι ℂ)-V‖*‖O‖+‖V‖*‖O‖*‖(U : Matrix ι ι ℂ)-V‖ := by
      rw [CStarRing.norm_mul_coe_unitary]
      apply add_le_add
      · simpa only [← star_sub,norm_star] using norm_mul_le (star (U : Matrix ι ι ℂ)-star V) O
      · calc
          _ ≤ ‖star V*O‖*‖(U : Matrix ι ι ℂ)-V‖ := norm_mul_le _ _
          _ ≤ (‖star V‖*‖O‖)*‖(U : Matrix ι ι ℂ)-V‖ := by gcongr; exact norm_mul_le _ _
          _ = _ := by rw [norm_star]
    _ = _ := by ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
