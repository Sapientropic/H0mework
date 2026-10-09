import H0mework.Chemistry.LAlanineSignedEvaluator.Contraction
import H0mework.Versions.AB.Chemistry.LAlanineGradient.Model

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedField

open SourceGaussianModel SourceFiniteData SourceSignedEvaluator ContinuousGradient

noncomputable section

def ReductionValid (box : Rectangle) (steps : Term → ℕ × ℕ) : Prop :=
  ∀ i, ∀ t ∈ sourceTerms i, TermReductionValid t box (steps t).1 (steps t).2

def pairAt (box : Rectangle) (steps : Term → ℕ × ℕ) (left right : MultiIndex) : Pair :=
  rectangleBilinear sourceTerms densityMatrix left right box steps

def firstPair (box : Rectangle) (steps : Term → ℕ × ℕ) (left right : MultiIndex) (axis : Fin 3) : Pair :=
  add (pairAt box steps (raise left axis) right) (pairAt box steps left (raise right axis))

def gradientPair (box : Rectangle) (steps : Term → ℕ × ℕ) (axis : Fin 3) : Pair :=
  firstPair box steps zeroJet zeroJet axis

def hessianPair (box : Rectangle) (steps : Term → ℕ × ℕ) (axis direction : Fin 3) : Pair :=
  add (firstPair box steps (raise zeroJet axis) zeroJet direction)
    (firstPair box steps zeroJet (raise zeroJet axis) direction)

def laplacianPair (box : Rectangle) (steps : Term → ℕ × ℕ) : Pair :=
  add (add (hessianPair box steps 0 0) (hessianPair box steps 1 1)) (hessianPair box steps 2 2)

theorem pairAt_contains (box : Rectangle) (steps : Term → ℕ × ℕ) (valid : ReductionValid box steps)
    (x : Point) (inside : InRectangle box x) (left right : MultiIndex) :
    Holds (pairAt box steps left right) (bilinear sourceTerms densityMatrix left right x) :=
  rectangleBilinear_contains sourceTerms densityMatrix left right box steps valid x inside

theorem firstPair_contains (box : Rectangle) (steps : Term → ℕ × ℕ) (valid : ReductionValid box steps)
    (x : Point) (inside : InRectangle box x) (left right : MultiIndex) (axis : Fin 3) :
    Holds (firstPair box steps left right axis) (firstBilinear sourceTerms densityMatrix left right axis x) :=
  add_holds _ _ _ _ (pairAt_contains box steps valid x inside _ _) (pairAt_contains box steps valid x inside _ _)

theorem gradientPair_contains (box : Rectangle) (steps : Term → ℕ × ℕ) (valid : ReductionValid box steps)
    (x : Point) (inside : InRectangle box x) (axis : Fin 3) :
    Holds (gradientPair box steps axis) (sourceGradient x axis) :=
  firstPair_contains box steps valid x inside zeroJet zeroJet axis

theorem hessianPair_contains (box : Rectangle) (steps : Term → ℕ × ℕ) (valid : ReductionValid box steps)
    (x : Point) (inside : InRectangle box x) (axis direction : Fin 3) :
    Holds (hessianPair box steps axis direction) (sourceHessian x axis direction) :=
  add_holds _ _ _ _ (firstPair_contains box steps valid x inside _ _ direction)
    (firstPair_contains box steps valid x inside _ _ direction)

theorem sourceHessian_diagonal (x : Point) (axis : Fin 3) :
    sourceHessian x axis axis = secondBilinear sourceTerms densityMatrix zeroJet zeroJet axis x := by
  simp only [sourceHessian, firstBilinear, secondBilinear]
  ring

theorem laplacianPair_contains (box : Rectangle) (steps : Term → ℕ × ℕ) (valid : ReductionValid box steps)
    (x : Point) (inside : InRectangle box x) :
    Holds (laplacianPair box steps) (laplacian sourceTerms densityMatrix x) := by
  have h := add_holds _ _ _ _ (add_holds _ _ _ _
    (hessianPair_contains box steps valid x inside 0 0) (hessianPair_contains box steps valid x inside 1 1))
    (hessianPair_contains box steps valid x inside 2 2)
  simp only [sourceHessian_diagonal] at h
  change Holds _ (∑ axis : Fin 3, secondBilinear sourceTerms densityMatrix zeroJet zeroJet axis x)
  simpa only [laplacianPair, Fin.sum_univ_three, add_assoc] using h

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedField
