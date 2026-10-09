import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Coefficients

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
open scoped Matrix BigOperators
noncomputable section

def middle (f : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![f 0+f 2,f 1; f 1,f 0+f 2]

def middleH (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![s,1; 1,s]

theorem middle_one : middle ![1,0,0]=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [middle,Matrix.cons_val_two,Matrix.one_apply]

theorem middle_smul (z : ℂ) (f : Fin 3 → ℂ) : z • middle f=middle (fun k => z*f k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [middle,Matrix.smul_apply,smul_eq_mul,mul_add]

theorem middle_sum {ι : Type*} (S : Finset ι) (f : ι → Fin 3 → ℂ) :
    (∑ n ∈ S,middle (f n))=middle (fun k => ∑ n ∈ S,f n k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [middle,Matrix.sum_apply,Finset.sum_add_distrib]

theorem middle_multiply (s : ℂ) (f : Fin 3 → ℂ) :
    middle f*middleH s=middle ![s*f 0,f 0+s*f 1+f 2,f 1+s*f 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [middle,Matrix.cons_val_two,middleH,Matrix.mul_apply,Fin.sum_univ_succ]
  all_goals ring

theorem middle_power (s : ℂ) (n : Nat) : (middleH s)^n=middle (LoadPrimitive.coefficientPower s 0 n) := by
  induction n with
  | zero => simpa only [pow_zero,LoadPrimitive.coefficientPower] using middle_one.symm
  | succ n ih =>
    rw [pow_succ,ih,middle_multiply]
    norm_num only [LoadPrimitive.coefficientPower,zero_pow,zero_add,one_mul]

theorem middle_polynomial (s z : ℂ) (n : Nat) :
    Phase.polynomial (z • middleH s) n=middle (LoadPrimitive.coefficientPolynomial s 0 z n) := by
  unfold Phase.polynomial LoadPrimitive.coefficientPolynomial
  simp only [smul_pow,middle_power,middle_smul,mul_assoc]
  exact middle_sum _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
