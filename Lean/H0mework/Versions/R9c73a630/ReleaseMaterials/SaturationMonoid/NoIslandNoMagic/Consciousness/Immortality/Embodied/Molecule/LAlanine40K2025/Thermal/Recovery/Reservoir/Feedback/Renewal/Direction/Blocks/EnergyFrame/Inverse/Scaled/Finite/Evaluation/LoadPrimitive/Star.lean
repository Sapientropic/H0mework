import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open scoped Matrix BigOperators
noncomputable section

def starCore (d : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,d; 0,0,1; d,1,0]

def starBasis (d : ℂ) : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ := ![1,starCore d,(starCore d)^2]

def starAssembly (d : ℂ) (f : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ∑ k : Fin 3, f k • starBasis d k

theorem star_cubic (d : ℂ) : (starCore d)^3=(d^2+1) • starCore d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [starCore,pow_succ,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.add_apply,Matrix.one_fin_three,Matrix.one_apply,smul_eq_mul]
  all_goals ring

theorem star_assembly_one (d : ℂ) : starAssembly d ![1,0,0]=1 := by
  simp [starAssembly,starBasis,Fin.sum_univ_succ]

theorem star_assembly_smul (d z : ℂ) (f : Fin 3 → ℂ) :
    z • starAssembly d f=starAssembly d (fun k => z*f k) := by
  simp only [starAssembly,Finset.smul_sum,smul_smul]

theorem star_assembly_sum {ι : Type*} (S : Finset ι) (d : ℂ) (f : ι → Fin 3 → ℂ) :
    (∑ n ∈ S, starAssembly d (f n))=starAssembly d (fun k => ∑ n ∈ S, f n k) := by
  simp only [starAssembly]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_smul.symm

theorem star_assembly_multiply (s d : ℂ) (f : Fin 3 → ℂ) :
    starAssembly d f*(s • (1 : Matrix (Fin 3) (Fin 3) ℂ)+starCore d)=
      starAssembly d ![s*f 0,f 0+s*f 1+(d^2+1)*f 2,f 1+s*f 2] := by
  simp only [starAssembly,starBasis,Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [starAssembly,starBasis,starCore,pow_two,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.add_apply,Matrix.one_fin_three,Matrix.one_apply,smul_eq_mul]
  all_goals ring

def coefficientPower (s d : ℂ) : Nat → Fin 3 → ℂ
  | 0 => ![1,0,0]
  | n+1 => let f := coefficientPower s d n
    ![s*f 0,f 0+s*f 1+(d^2+1)*f 2,f 1+s*f 2]

theorem star_assembly_power (s d : ℂ) (n : Nat) :
    (s • (1 : Matrix (Fin 3) (Fin 3) ℂ)+starCore d)^n=starAssembly d (coefficientPower s d n) := by
  induction n with
  | zero => simpa only [pow_zero,coefficientPower] using (star_assembly_one d).symm
  | succ n ih => rw [pow_succ,ih,star_assembly_multiply]; rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
