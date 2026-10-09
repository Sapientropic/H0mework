import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor.Jets
import H0mework.Chemistry.LAlanineRefinementDensity.DensityBounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open SourceGaussianModel SourceFiniteData
open scoped BigOperators
noncomputable section

def shift (m a : MultiIndex) : MultiIndex := fun i => m i + a i

def factorial (a : MultiIndex) : ℕ := (a 0).factorial * (a 1).factorial * (a 2).factorial

def monomial (a : MultiIndex) (v : Point) : ℝ := v 0 ^ a 0 * v 1 ^ a 1 * v 2 ^ a 2

/-- The complete homogeneous coordinate census through the cubic remainder. -/
def increments : ℕ → List MultiIndex
  | 0 => [![0,0,0]]
  | 1 => [![1,0,0], ![0,1,0], ![0,0,1]]
  | 2 => [![2,0,0], ![1,1,0], ![1,0,1], ![0,2,0], ![0,1,1], ![0,0,2]]
  | 3 => [![3,0,0], ![2,1,0], ![2,0,1], ![1,2,0], ![1,1,1],
      ![1,0,2], ![0,3,0], ![0,2,1], ![0,1,2], ![0,0,3]]
  | _ => []

def homogeneous (n : ℕ) (f : MultiIndex → ℝ) (m : MultiIndex) (v : Point) : ℝ :=
  ((increments n).map (fun a => f (shift m a) * monomial a v / (factorial a : ℝ))).sum

def directional : ℕ → (MultiIndex → ℝ) → MultiIndex → Point → ℝ
  | 0, f, m, _ => f m
  | n+1, f, m, v => ∑ a : Fin 3, directional n f (raise m a) v * v a

theorem raise_zero (m : MultiIndex) : raise m 0 = ![m 0 + 1,m 1,m 2] := by
  ext i; fin_cases i <;> rfl

theorem raise_one (m : MultiIndex) : raise m 1 = ![m 0,m 1 + 1,m 2] := by
  ext i; fin_cases i <;> rfl

theorem raise_two (m : MultiIndex) : raise m 2 = ![m 0,m 1,m 2 + 1] := by
  ext i; fin_cases i <;> rfl

theorem shift_vector (m a : MultiIndex) : shift m a = ![m 0+a 0,m 1+a 1,m 2+a 2] := by
  ext i; fin_cases i <;> rfl

theorem vector_eta (m : MultiIndex) : ![m 0,m 1,m 2] = m := by
  ext i; fin_cases i <;> rfl

theorem directional_factorial (n : Fin 4) (f : MultiIndex → ℝ) (m : MultiIndex) (v : Point) :
    directional n.val f m v / (n.val.factorial : ℝ) = homogeneous n.val f m v := by
  fin_cases n <;>
    simp [directional, homogeneous, increments, monomial, factorial, Nat.factorial,
      Fin.sum_univ_succ, shift_vector, raise_zero, raise_one, raise_two, Nat.add_assoc, vector_eta] <;> ring

theorem increments_order (n : Fin 4) : ∀ a ∈ increments n.val,
    jetOrder a = n.val := by
  fin_cases n <;> simp [increments, jetOrder]

theorem increments_original_zero : increments 0 = [jetMulti 0] := by
  simp only [increments, List.cons.injEq, and_true]
  ext i; fin_cases i <;> rfl

theorem increments_original_first : increments 1 = [jetMulti 1,jetMulti 2,jetMulti 3] := by
  simp only [increments, List.cons.injEq, and_true]
  repeat' constructor
  all_goals ext i; fin_cases i <;> rfl

theorem increments_original_second : increments 2 =
    [jetMulti 4,jetMulti 5,jetMulti 6,jetMulti 7,jetMulti 8,jetMulti 9] := by
  simp only [increments, List.cons.injEq, and_true]
  repeat' constructor
  all_goals ext i; fin_cases i <;> rfl

theorem increments_original_third : increments 3 =
    [jetMulti 10,jetMulti 11,jetMulti 12,jetMulti 13,jetMulti 14,
      jetMulti 15,jetMulti 16,jetMulti 17,jetMulti 18,jetMulti 19] := by
  simp only [increments, List.cons.injEq, and_true]
  repeat' constructor
  all_goals ext i; fin_cases i <;> rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
