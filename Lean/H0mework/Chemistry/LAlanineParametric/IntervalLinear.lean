import H0mework.Chemistry.LAlanineParametric.RK4
import H0mework.Chemistry.LAlanineGradient.Model
import H0mework.Chemistry.LAlanineSignedEvaluator.Arithmetic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap

open SourceGaussianModel ContinuousGradient SourceSignedEvaluator
open LAlanineContinuousPatch.Parametric

abbrev VectorPair := Fin 3 → Pair
abbrev MatrixPair := Fin 3 → Fin 3 → Pair

def VectorHolds (a : VectorPair) (x : Point) : Prop := ∀ i, Holds (a i) (x i)
def MatrixHolds (a : MatrixPair) (linear : Point →L[ℝ] Point) : Prop :=
  ∀ i j, Holds (a i j) (linear (Pi.single j 1) i)

def vectorAdd (a b : VectorPair) : VectorPair := fun i => add (a i) (b i)
def vectorScale (c : Pair) (a : VectorPair) : VectorPair := fun i => mul c (a i)
def matrixAdd (a b : MatrixPair) : MatrixPair := fun i j => add (a i j) (b i j)
def matrixScale (c : Pair) (a : MatrixPair) : MatrixPair := fun i j => mul c (a i j)
def outer (a : VectorPair) (b : VectorPair) : MatrixPair := fun i j => mul (a i) (b j)

def dotThree (a b : VectorPair) : Pair :=
  add (add (add (point 0) (mul (a 0) (b 0))) (mul (a 1) (b 1))) (mul (a 2) (b 2))

def matrixMultiply (a b : MatrixPair) : MatrixPair := fun i j => dotThree (a i) (fun k => b k j)

theorem dotThree_contains (a b : VectorPair) (x y : Point)
    (hx : VectorHolds a x) (hy : VectorHolds b y) : Holds (dotThree a b) (∑ i : Fin 3, x i * y i) := by
  have h := add_holds _ _ _ _ (add_holds _ _ _ _
    (add_holds _ _ _ _ (point_holds 0) (mul_holds _ _ _ _ (hx 0) (hy 0)))
      (mul_holds _ _ _ _ (hx 1) (hy 1))) (mul_holds _ _ _ _ (hx 2) (hy 2))
  simpa only [dotThree, Rat.cast_zero, zero_add, Fin.sum_univ_three, add_assoc] using h

theorem vectorAdd_contains (a b : VectorPair) (x y : Point)
    (hx : VectorHolds a x) (hy : VectorHolds b y) : VectorHolds (vectorAdd a b) (x + y) :=
  fun i => add_holds _ _ _ _ (hx i) (hy i)

theorem vectorScale_contains (c : Pair) (a : VectorPair) (scalar : ℝ) (x : Point)
    (hc : Holds c scalar) (hx : VectorHolds a x) : VectorHolds (vectorScale c a) (scalar • x) :=
  fun i => mul_holds _ _ _ _ hc (hx i)

theorem matrixAdd_contains (a b : MatrixPair) (A B : Point →L[ℝ] Point)
    (ha : MatrixHolds a A) (hb : MatrixHolds b B) : MatrixHolds (matrixAdd a b) (A + B) :=
  fun i j => add_holds _ _ _ _ (ha i j) (hb i j)

theorem matrixScale_contains (c : Pair) (a : MatrixPair) (scalar : ℝ) (A : Point →L[ℝ] Point)
    (hc : Holds c scalar) (ha : MatrixHolds a A) : MatrixHolds (matrixScale c a) (scalar • A) :=
  fun i j => mul_holds _ _ _ _ hc (ha i j)

theorem outer_contains (a b : VectorPair) (x : Point) (linear : Point →L[ℝ] ℝ)
    (hx : VectorHolds a x) (hl : ∀ j, Holds (b j) (linear (Pi.single j 1))) :
    MatrixHolds (outer a b) (linear.smulRight x) := by
  intro i j
  simpa only [outer, ContinuousLinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
    mul_holds _ _ _ _ (hx i) (hl j)

theorem hessianMultiply_contains (h a : MatrixPair) (x : Point) (A : Point →L[ℝ] Point)
    (hh : ∀ i j, Holds (h i j) (sourceHessian x i j)) (ha : MatrixHolds a A) :
    MatrixHolds (matrixMultiply h a) ((sourceHessianLinear x).comp A) := by
  intro i j
  change Holds _ (sourceHessianLinear x (A (Pi.single j 1)) i)
  rw [sourceHessianLinear_apply]
  exact dotThree_contains _ _ _ _ (hh i) (fun k => ha k j)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap
