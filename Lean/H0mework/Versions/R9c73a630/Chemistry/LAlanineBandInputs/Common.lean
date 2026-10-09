import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandInputs.Parameters

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs

open SourceSignedEvaluator SourceExponential SourceRectangle WholeBandSource WholeBandSaturation

def ReductionConditions (radial : Pair) (r : Nat × Nat) : Prop :=
  |reducedArgument radial.1 r.1| ≤ 1/2 ∧ |reducedArgument radial.2 r.2| ≤ 1/2

def SaturationConditions (radial : Pair) (r : Nat × Nat) : Prop :=
  ReductionConditions radial r ∧
  ((r.1 = 8 ∧ reducedArgument radial.1 r.1 ≤ -7/16) ∨
    (9 ≤ r.1 ∧ reducedArgument radial.1 r.1 ≤ -7/32)) ∧
  ((r.2 = 8 ∧ reducedArgument radial.2 r.2 ≤ -7/16) ∨
    (9 ≤ r.2 ∧ reducedArgument radial.2 r.2 ≤ -7/32))

instance (a : Pair) (r : Nat × Nat) : Decidable (ReductionConditions a r) := by
  unfold ReductionConditions
  infer_instance

instance (a : Pair) (r : Nat × Nat) : Decidable (SaturationConditions a r) := by
  unfold SaturationConditions
  infer_instance

/-- The shared radius values precede the original exponent/reduction inequalities. -/
structure InputCalculation (box : Rectangle) (r : Group → Nat × Nat) where
  radii : Atom → Pair
  radii_exact : ∀ a, radii a = squaredRadius box (atomCentre a)
  reductions : ∀ g, ReductionConditions (sharedRadial radii g) (r g)
  saturated : ∀ s : SaturatedGroup,
    SaturationConditions (sharedRadial radii (groupAt s)) (r (groupAt s))

theorem InputCalculation.reductions_valid {box : Rectangle} {r : Group → Nat × Nat}
    (calculation : InputCalculation box r) (g : Group) :
    TermReductionValid (groupTerm g) box (r g).1 (r g).2 := by
  change ReductionConditions (radialPair (groupTerm g) box) (r g)
  rw [radialPair_shared, show (fun a => squaredRadius box (atomCentre a)) = calculation.radii from
    funext (fun a => (calculation.radii_exact a).symm)]
  exact calculation.reductions g

theorem InputCalculation.saturated_inputs {box : Rectangle} {r : Group → Nat × Nat}
    (calculation : InputCalculation box r) (s : SaturatedGroup) :
    InputBounds box r (groupAt s) := by
  change SaturationConditions (radialPair (groupTerm (groupAt s)) box) (r (groupAt s))
  rw [radialPair_shared, show (fun a => squaredRadius box (atomCentre a)) = calculation.radii from
    funext (fun a => (calculation.radii_exact a).symm)]
  exact calculation.saturated s

end LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
