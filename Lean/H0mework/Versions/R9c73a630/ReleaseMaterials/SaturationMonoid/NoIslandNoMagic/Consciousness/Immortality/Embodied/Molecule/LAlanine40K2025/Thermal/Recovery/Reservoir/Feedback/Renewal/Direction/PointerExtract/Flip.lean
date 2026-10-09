import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Source
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
open Collision Quantum Load.Producer.StrictThermal Propagation.Producer Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def flip : Matrix.unitaryGroup (ι ⊕ ι) ℂ :=
  ⟨Matrix.fromBlocks 0 1 1 0,by
    rw [Unitary.mem_iff]
    change (Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) 1 0)ᴴ*Matrix.fromBlocks 0 1 1 0=1 ∧
      Matrix.fromBlocks 0 1 1 0*(Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) 1 0)ᴴ=1
    constructor <;> simp [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]⟩

theorem flip_conjugation (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    conjugation flip rho=Matrix.fromBlocks rho.toBlocks₂₂ rho.toBlocks₂₁ rho.toBlocks₁₂ rho.toBlocks₁₁ := by
  rw [conjugation_apply]
  change Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) 1 0*rho*
    (Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) 1 0)ᴴ=_
  conv_lhs => arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks rho]
  simp [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]

theorem flip_body (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    bodyRead (conjugation flip rho)=bodyRead rho := by
  rw [flip_conjugation]
  simp only [bodyRead,Matrix.toBlocks_fromBlocks₁₁,Matrix.toBlocks_fromBlocks₂₂]
  exact add_comm _ _

theorem flip_one (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : oneRead (conjugation flip rho)=zeroRead rho := by
  rw [flip_conjugation]
  rfl

theorem flip_zero (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : zeroRead (conjugation flip rho)=oneRead rho := by
  rw [flip_conjugation]
  rfl

theorem flip_left_block (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (conjugation flip rho).toBlocks₁₁=rho.toBlocks₂₂ := by
  rw [flip_conjugation]
  rfl

theorem flip_right_block (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (conjugation flip rho).toBlocks₂₂=rho.toBlocks₁₁ := by
  rw [flip_conjugation]
  rfl

theorem flip_baseline_work (rho : PointerJoint) :
    energy Pointer.baselineHamiltonian rho-energy Pointer.baselineHamiltonian (conjugation flip rho)=
      2*(oneRead rho-zeroRead rho) := by
  have original := block_energy_split Physical.baselineHamiltonian 2 rho
  have target := block_energy_split Physical.baselineHamiltonian 2 (conjugation flip rho)
  change energy Pointer.baselineHamiltonian rho=_ at original
  change energy Pointer.baselineHamiltonian (conjugation flip rho)=_ at target
  rw [flip_body,flip_one] at target
  linarith only [original,target]

omit [DecidableEq ι] in
theorem reads_sum (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : zeroRead rho+oneRead rho=rho.trace.re := by
  have trace := trace_fromBlocks rho.toBlocks₁₁ rho.toBlocks₁₂ rho.toBlocks₂₁ rho.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks] at trace
  simpa only [Complex.add_re,zeroRead,oneRead] using (congrArg Complex.re trace).symm

theorem current_flip_positive :
    0 < energy Pointer.baselineHamiltonian (Extract.Runtime.readCurrent Extract.Runtime.afterFirst).joint-
      energy Pointer.baselineHamiltonian (conjugation flip (Extract.Runtime.readCurrent Extract.Runtime.afterFirst).joint) := by
  rw [flip_baseline_work]
  have total := reads_sum (Extract.Runtime.readCurrent Extract.Runtime.afterFirst).joint
  rw [(Extract.Runtime.readCurrent Extract.Runtime.afterFirst).normalized,Complex.one_re] at total
  linarith only [current_pointer_population,total]

theorem flip_hermitian : (flip (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ).IsHermitian := by
  change (Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) 1 0)ᴴ=_
  simp [Matrix.fromBlocks_conjTranspose,flip]

theorem flip_square : (flip (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*(flip (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)=1 := by
  change Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) 1 0*Matrix.fromBlocks 0 1 1 0=1
  simp [Matrix.fromBlocks_multiply]

theorem flip_half_pi :
    NormedSpace.exp ((-Complex.I*((Real.pi/2 : ℝ) : ℂ)) •
      (flip (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ))=
      (-Complex.I) • (flip (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  simpa only [Real.cos_pi_div_two,Real.sin_pi_div_two,Complex.ofReal_zero,Complex.ofReal_one,
    zero_smul,mul_one,zero_sub,neg_smul] using!
    Dynamics.exp_neg_I_smul_involution (flip (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
      (flip_square (ι := ι)) (Real.pi/2)


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
