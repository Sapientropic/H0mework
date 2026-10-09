import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor.Envelopes
import H0mework.Chemistry.LAlanineSignedEvaluator.Arithmetic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open SourceGaussianModel SourceSignedEvaluator
open scoped BigOperators
noncomputable section

def powerPair (p : Pair) (n : ℕ) : Pair :=
  if n = 0 then (1,1) else if n = 1 then p else if n = 2 then square p else mul (square p) p

theorem powerPair_holds (p : Pair) (x : ℝ) (hx : Holds p x) (n : ℕ) (hn : n < 4) :
    Holds (powerPair p n) (x^n) := by
  interval_cases n
  · norm_num [powerPair, Holds]
  · simpa [powerPair] using hx
  · simpa [powerPair] using square_holds p x hx
  · have h := mul_holds (square p) p (x^2) x (square_holds p x hx) hx
    simpa [powerPair, pow_succ] using h

/-- Multiplication order matches the original integer restriction evaluator. -/
def termPair (A : MultiIndex → Pair) (m a : MultiIndex) (d : Fin 3 → Pair) : Pair :=
  mul (mul (mul (mul (A (shift m a)) (powerPair (d 0) (a 0)))
    (powerPair (d 1) (a 1))) (powerPair (d 2) (a 2)))
      (point (1 / (factorial a : ℚ)))

def sumPairs (L : List Pair) : Pair := L.foldr add (0,0)

def homogeneousPair (n : ℕ) (A : MultiIndex → Pair) (m : MultiIndex) (d : Fin 3 → Pair) : Pair :=
  sumPairs ((increments n).map (fun a => termPair A m a d))

def polynomialPair (n : ℕ) (A : MultiIndex → Pair) (m : MultiIndex) (d : Fin 3 → Pair) : Pair :=
  sumPairs ((List.range (n+1)).map (fun k => homogeneousPair k A m d))

def remainderPair (n : ℕ) (B : MultiIndex → ℚ) (m : MultiIndex) (r : Fin 3 → ℚ) : Pair :=
  homogeneousPair (n+1) (fun j => (B j,B j)) m (fun i => (r i,r i))

def enclosure (n : ℕ) (A : MultiIndex → Pair) (B : MultiIndex → ℚ) (m : MultiIndex)
    (d : Fin 3 → Pair) (r : Fin 3 → ℚ) : Pair :=
  let p := polynomialPair n A m d
  let e := (remainderPair n B m r).2
  (p.1-e,p.2+e)

theorem sumPairs_holds {ι : Type*} (L : List ι) (A : ι → Pair) (f : ι → ℝ)
    (h : ∀ a ∈ L, Holds (A a) (f a)) :
    Holds (sumPairs (L.map A)) (L.map f).sum := by
  induction L with
  | nil => norm_num [sumPairs,Holds]
  | cons a L ih =>
      exact add_holds _ _ _ _ (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem termPair_holds (A : MultiIndex → Pair) (f : MultiIndex → ℝ) (m a : MultiIndex)
    (d : Fin 3 → Pair) (v : Point) (ha : ∀ i, a i < 4)
    (hc : Holds (A (shift m a)) (f (shift m a))) (hd : ∀ i, Holds (d i) (v i)) :
    Holds (termPair A m a d) (f (shift m a) * monomial a v / (factorial a : ℝ)) := by
  have h := mul_holds _ _ _ _
    (mul_holds _ _ _ _ (mul_holds _ _ _ _ (mul_holds _ _ _ _ hc
      (powerPair_holds _ _ (hd 0) _ (ha 0))) (powerPair_holds _ _ (hd 1) _ (ha 1)))
        (powerPair_holds _ _ (hd 2) _ (ha 2))) (point_holds (1/(factorial a : ℚ)))
  convert h using 1 <;> simp [termPair, monomial, div_eq_mul_inv, mul_assoc]

theorem homogeneousPair_holds (n : Fin 4) (A : MultiIndex → Pair) (f : MultiIndex → ℝ)
    (m : MultiIndex) (d : Fin 3 → Pair) (v : Point)
    (hc : ∀ a ∈ increments n.val, Holds (A (shift m a)) (f (shift m a)))
    (hd : ∀ i, Holds (d i) (v i)) :
    Holds (homogeneousPair n.val A m d) (homogeneous n.val f m v) := by
  apply sumPairs_holds
  intro a ha
  have order := increments_order n a ha
  apply termPair_holds A f m a d v _ (hc a ha) hd
  intro i
  fin_cases i <;> dsimp <;> unfold jetOrder at order <;> omega

theorem list_range_sum (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem polynomialPair_holds (n : Fin 3) (A : MultiIndex → Pair) (f : MultiIndex → ℝ)
    (m : MultiIndex) (d : Fin 3 → Pair) (v : Point)
    (hc : ∀ k ≤ n.val, ∀ a ∈ increments k, Holds (A (shift m a)) (f (shift m a)))
    (hd : ∀ i, Holds (d i) (v i)) :
    Holds (polynomialPair n.val A m d) (polynomial n.val f m v) := by
  have h := sumPairs_holds (List.range (n.val+1))
    (fun k => homogeneousPair k A m d) (fun k => homogeneous k f m v) (fun k hk =>
      homogeneousPair_holds ⟨k, by have := List.mem_range.mp hk; omega⟩ A f m d v
        (hc k (by have := List.mem_range.mp hk; omega)) hd)
  simpa only [polynomialPair, polynomial, list_range_sum] using h

theorem remainderPair_holds (n : Fin 3) (B : MultiIndex → ℚ) (m : MultiIndex) (r : Fin 3 → ℚ) :
    Holds (remainderPair n.val B m r)
      (homogeneous (n.val+1) (fun j => (B j : ℝ)) m (fun i => (r i : ℝ))) := by
  exact homogeneousPair_holds ⟨n.val+1, by omega⟩ _ _ _ _ _
    (fun _ _ => ⟨le_rfl,le_rfl⟩) (fun _ => ⟨le_rfl,le_rfl⟩)

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
