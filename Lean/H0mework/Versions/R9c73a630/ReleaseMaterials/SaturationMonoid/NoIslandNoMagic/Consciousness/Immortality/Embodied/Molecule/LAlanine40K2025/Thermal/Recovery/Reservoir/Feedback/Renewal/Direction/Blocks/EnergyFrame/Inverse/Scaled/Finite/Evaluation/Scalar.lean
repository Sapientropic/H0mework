import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Consumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Scalar
open scoped BigOperators

abbrev QComplex := ℚ × ℚ

def value (z : QComplex) : ℂ := (z.1 : ℂ)+Complex.I*(z.2 : ℂ)
def multiply (z w : QComplex) : QComplex := (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)
def power (z : QComplex) : ℕ → QComplex
  | 0 => (1,0)
  | n+1 => multiply (power z n) z

def polynomial (z : QComplex) : ℕ → QComplex
  | 0 => (0,0)
  | n+1 => polynomial z n+(n.factorial : ℚ)⁻¹ • power z n

noncomputable def complexPolynomial (z : ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹)*z^k

def distance (z w : QComplex) : ℚ := |z.1-w.1|+|z.2-w.2|

theorem value_add (z w : QComplex) : value (z+w)=value z+value w := by
  simp only [value,Prod.fst_add,Prod.snd_add,Rat.cast_add]
  ring

theorem value_smul (r : ℚ) (z : QComplex) : value (r • z)=(r : ℂ)*value z := by
  simp only [value,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Rat.cast_mul]
  ring

theorem value_multiply (z w : QComplex) : value (multiply z w)=value z*value w := by
  simp only [value,multiply,Rat.cast_add,Rat.cast_sub,Rat.cast_mul]
  linear_combination -((z.2 : ℂ)*(w.2 : ℂ))*Complex.I_sq

theorem value_power (z : QComplex) (n : ℕ) : value (power z n)=(value z)^n := by
  induction n with
  | zero => simp [power,value]
  | succ n ih => rw [power,value_multiply,ih,pow_succ]

theorem value_polynomial (z : QComplex) (n : ℕ) : value (polynomial z n)=complexPolynomial (value z) n := by
  induction n with
  | zero => simp [polynomial,value,complexPolynomial]
  | succ n ih =>
    rw [polynomial,value_add,value_smul,value_power,ih]
    simp only [complexPolynomial,Finset.sum_range_succ,Rat.cast_inv,Rat.cast_natCast]

theorem value_distance (z w : QComplex) : ‖value z-value w‖ ≤ (distance z w : ℝ) := by
  have split : value z-value w=((z.1-w.1 : ℚ) : ℂ)+Complex.I*((z.2-w.2 : ℚ) : ℂ) := by
    simp only [value,Rat.cast_sub]
    ring
  rw [split]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_ratCast,distance,Rat.cast_add,Rat.cast_abs,le_refl]

theorem value_norm_squared (z : QComplex) : ‖value z‖^2=((z.1^2+z.2^2 : ℚ) : ℝ) := by
  simp [value,Complex.sq_norm,Complex.normSq_apply]
  ring

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Scalar
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
