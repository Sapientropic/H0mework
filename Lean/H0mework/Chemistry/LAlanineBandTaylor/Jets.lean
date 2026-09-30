import H0mework.Chemistry.LAlanineGradient.Model

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open SourceGaussianModel SourceFiniteData ContinuousGradient
open scoped BigOperators
noncomputable section

/-- Coordinate differentiation of the original complete density bilinear form. -/
def wordJet : List (Fin 3) → MultiIndex → MultiIndex → Point → ℝ
  | [], l, r => bilinear sourceTerms densityMatrix l r
  | a :: w, l, r => fun x => wordJet w (raise l a) r x + wordJet w l (raise r a) x

def jetWord (m : MultiIndex) : List (Fin 3) :=
  List.replicate (m 0) 0 ++ List.replicate (m 1) 1 ++ List.replicate (m 2) 2

def densityJet (m : MultiIndex) : Point → ℝ := wordJet (jetWord m) zeroJet zeroJet

def sourceJet (j : JetIndex) : Point → ℝ := densityJet (jetMulti j)

theorem raise_commute (m : MultiIndex) (a b : Fin 3) :
    raise (raise m a) b = raise (raise m b) a := by
  ext i
  by_cases ia : i = a <;> by_cases ib : i = b <;>
    simp_all [raise, Function.update_apply]

theorem wordJet_perm {v w : List (Fin 3)} (h : v.Perm w) (l r : MultiIndex) :
    wordJet v l r = wordJet w l r := by
  induction h generalizing l r with
  | nil => rfl
  | cons a h ih => funext x; simp only [wordJet, ih]
  | swap a b w =>
      funext x
      simp only [wordJet, raise_commute l a b, raise_commute r a b]
      ring
  | trans h₁ h₂ ih₁ ih₂ => rw [ih₁, ih₂]

theorem jetWord_raise (m : MultiIndex) (a : Fin 3) :
    (jetWord m ++ [a]).Perm (jetWord (raise m a)) := by
  apply List.perm_iff_count.mpr
  intro i
  fin_cases a <;> fin_cases i <;>
    simp [jetWord, raise, List.count_append, List.count_replicate]

theorem wordJet_coordinate_derivative (w : List (Fin 3)) (l r : MultiIndex)
    (x : Point) (a : Fin 3) :
    HasDerivAt (fun t => wordJet w l r (Function.update x a t))
      (wordJet (w ++ [a]) l r x) (x a) := by
  induction w generalizing l r with
  | nil => exact bilinear_coordinate_derivative sourceTerms densityMatrix l r x a
  | cons b w ih => exact (ih (raise l b) r).add (ih l (raise r b))

theorem densityJet_coordinate_derivative (m : MultiIndex) (x : Point) (a : Fin 3) :
    HasDerivAt (fun t => densityJet m (Function.update x a t))
      (densityJet (raise m a) x) (x a) := by
  have h := wordJet_coordinate_derivative (jetWord m) zeroJet zeroJet x a
  rw [wordJet_perm (jetWord_raise m a)] at h
  exact h

theorem wordJet_contDiff (w : List (Fin 3)) (l r : MultiIndex) (n : WithTop ℕ∞) :
    ContDiff ℝ n (wordJet w l r) := by
  induction w generalizing l r with
  | nil => exact bilinear_contDiff sourceTerms densityMatrix l r n
  | cons a w ih => exact (ih (raise l a) r).add (ih l (raise r a))

theorem densityJet_contDiff (m : MultiIndex) (n : WithTop ℕ∞) :
    ContDiff ℝ n (densityJet m) := wordJet_contDiff _ _ _ n

def jetLinear (m : MultiIndex) (x : Point) : Point →L[ℝ] ℝ :=
  ∑ a : Fin 3, densityJet (raise m a) x • ContinuousLinearMap.proj a

theorem jetLinear_apply (m : MultiIndex) (x v : Point) :
    jetLinear m x v = ∑ a : Fin 3, densityJet (raise m a) x * v a := by
  simp only [jetLinear, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem densityJet_hasFDerivAt (m : MultiIndex) (x : Point) :
    HasFDerivAt (densityJet m) (jetLinear m x) x := by
  have hd := (densityJet_contDiff m 1).differentiable (by norm_num) x
  have he : fderiv ℝ (densityJet m) x = jetLinear m x := by
    ext v
    rw [linear_apply_coordinates, jetLinear_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [fderiv_coordinate _ x a hd _ (densityJet_coordinate_derivative m x a)]
  rw [← he]
  exact hd.hasFDerivAt

theorem densityJet_zero : densityJet zeroJet = sourceDensity := rfl

theorem densityJet_first (a : Fin 3) :
    densityJet (raise zeroJet a) = fun x => sourceGradient x a := by
  fin_cases a <;> funext x <;> rfl

theorem densityJet_second (a b : Fin 3) :
    densityJet (raise (raise zeroJet a) b) = fun x => sourceHessian x a b := by
  have hp : ([a] ++ [b]).Perm (jetWord (raise (raise zeroJet a) b)) := by
    have h := jetWord_raise (raise zeroJet a) b
    have one : jetWord (raise zeroJet a) = [a] := by fin_cases a <;> rfl
    rwa [one] at h
  rw [densityJet, ← wordJet_perm hp]
  rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
