import H0mework.Chemistry.LAlanineBandTaylor.Algebra
import H0mework.Chemistry.LAlanineBandTaylor.Scalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open SourceGaussianModel Set
open scoped BigOperators
noncomputable section

def segment (c v : Point) (t : ℝ) : Point := c + t • v

theorem segment_contDiff (c v : Point) (n : WithTop ℕ∞) : ContDiff ℝ n (segment c v) := by
  unfold segment; fun_prop

theorem segment_hasDerivAt (c v : Point) (t : ℝ) : HasDerivAt (segment c v) v t := by
  convert! (hasDerivAt_const t c).add ((hasDerivAt_id t).smul_const v) using 1
  simp

theorem densityJet_segment_derivative (m : MultiIndex) (c v : Point) (t : ℝ) :
    HasDerivAt (fun s => densityJet m (segment c v s))
      (directional 1 (fun j => densityJet j (segment c v t)) m v) t := by
  convert! (densityJet_hasFDerivAt m (segment c v t)).comp_hasDerivAt t
    (segment_hasDerivAt c v t) using 1

theorem directional_segment_derivative (n : ℕ) (m : MultiIndex) (c v : Point) (t : ℝ) :
    HasDerivAt (fun s => directional n (fun j => densityJet j (segment c v s)) m v)
      (directional (n+1) (fun j => densityJet j (segment c v t)) m v) t := by
  induction n generalizing m with
  | zero => exact densityJet_segment_derivative m c v t
  | succ n ih => exact HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => (ih (raise m a)).mul_const (v a))

theorem densityJet_segment_iterated (n : ℕ) (m : MultiIndex) (c v : Point) :
    iteratedDeriv n (fun t => densityJet m (segment c v t)) =
      fun t => directional n (fun j => densityJet j (segment c v t)) m v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (directional_segment_derivative n m c v t).deriv

def polynomial (n : ℕ) (f : MultiIndex → ℝ) (m : MultiIndex) (v : Point) : ℝ :=
  ∑ k ∈ Finset.range (n+1), homogeneous k f m v

theorem densityJet_taylor (n : Fin 3) (m : MultiIndex) (c v : Point) :
    ∃ t ∈ Ioo (0 : ℝ) 1, densityJet m (c+v) =
      polynomial n.val (fun j => densityJet j c) m v +
        homogeneous (n.val+1) (fun j => densityJet j (segment c v t)) m v := by
  obtain ⟨t, ht, h⟩ := scalar_unit_taylor
    (fun s => densityJet m (segment c v s)) n.val
    ((densityJet_contDiff m (n.val+1)).comp (segment_contDiff c v (n.val+1)))
  simp only [densityJet_segment_iterated] at h
  have hp : (∑ k ∈ Finset.range (n.val+1),
      directional k (fun j => densityJet j (segment c v 0)) m v / (k.factorial : ℝ)) =
      polynomial n.val (fun j => densityJet j c) m v := by
    simp only [segment, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    exact directional_factorial ⟨k, by have := Finset.mem_range.mp hk; omega⟩ _ _ _
  rw [hp, directional_factorial ⟨n.val+1, by omega⟩] at h
  refine ⟨t,ht,?_⟩
  simpa only [segment, one_smul] using h

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
