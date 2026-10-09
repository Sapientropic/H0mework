import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCProjectors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open scoped Matrix BigOperators
noncomputable section

def pcAssembly (coefficients : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ a, coefficients a • pcProjection a

theorem pc_assembly_one : pcAssembly (fun _ => 1)=1 := by
  simpa only [pcAssembly,one_smul] using pc_projection_total

theorem pc_assembly_mul (f g : Fin 4 → ℂ) : pcAssembly f*pcAssembly g=pcAssembly (fun a => f a*g a) := by
  simp only [pcAssembly,Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [pc_projection_orthogonal,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,smul_smul,mul_comm]

theorem pc_assembly_smul (f : Fin 4 → ℂ) (c : ℂ) : c • pcAssembly f=pcAssembly (fun a => c*f a) := by
  simp only [pcAssembly,Finset.smul_sum,smul_smul]

theorem pc_assembly_pow (f : Fin 4 → ℂ) (n : Nat) : (pcAssembly f)^n=pcAssembly (fun a => (f a)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using pc_assembly_one.symm
  | succ n ih => rw [pow_succ,ih,pc_assembly_mul]; simp only [pow_succ]

theorem pc_assembly_sum {τ : Type*} (s : Finset τ) (f : τ → Fin 4 → ℂ) :
    (∑ n ∈ s, pcAssembly (f n))=pcAssembly (fun a => ∑ n ∈ s, f n a) := by
  simp only [pcAssembly]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_smul.symm

def scalarPolynomial (z : ℂ) (N : Nat) : ℂ := ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹)*z^n

theorem pc_polynomial_resolution (f : Fin 4 → ℂ) (N : Nat) :
    Phase.polynomial (pcAssembly f) N=pcAssembly (fun a => scalarPolynomial (f a) N) := by
  unfold Phase.polynomial
  simp only [pc_assembly_pow,pc_assembly_smul]
  exact pc_assembly_sum _ _

theorem pc_flow_resolution (x y time : ℝ) :
    Phase.flowPolynomial (packedHpc x y) time=
      pcAssembly (fun a => scalarPolynomial (((time : ℂ)*(-Complex.I))*pcValues x y a) 14) := by
  rw [Phase.flowPolynomial,original_pc_resolution]
  change Phase.polynomial (time • (-Complex.I • pcAssembly (pcValues x y))) 14=_
  have scalar (c : ℝ) (M : Matrix (Fin 4) (Fin 4) ℂ) : c • M=(c : ℂ) • M := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  rw [scalar,pc_assembly_smul,pc_assembly_smul,pc_polynomial_resolution]
  congr 1
  funext a
  congr 1
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
