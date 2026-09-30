import H0mework.Chemistry.LAlanineBandFlow.ActualFirstStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandActual

open SourceGaussianModel SourceSignedEvaluator WholeBandSource WholeBandGeometry WholeBandReplay Set
noncomputable section

def InitialAt (d : Direction) := {x : Point // InRectangle (initialBox 0 d 0) x}
def TargetAt (d : Direction) := {x : Point // InRectangle (initialBox 0 d 1) x}

def firstCurve (d : Direction) (initial : InitialAt d) : ℝ → Point :=
  Classical.choose (source_first_step d initial.val initial.property)

theorem firstCurve_spec (d : Direction) (initial : InitialAt d) :
    firstCurve d initial 0 = initial.val ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt (firstCurve d initial)
          (TrueTubeTrace.signedGradient (sign d) (firstCurve d initial t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox 0 d 0) (firstCurve d initial t)) ∧
      InRectangle (endpointBox 0 d 0) (firstCurve d initial stepSize) :=
  Classical.choose_spec (source_first_step d initial.val initial.property)

def firstTarget (d : Direction) (initial : InitialAt d) : TargetAt d :=
  ⟨firstCurve d initial stepSize,
    (show endpointBox 0 d 0 = initialBox 0 d 1 from endpoint_next_initial 0 d (0 : Fin 15)) ▸
      (firstCurve_spec d initial).2.2⟩

theorem firstTarget_generated (d : Direction) (initial : InitialAt d) :
    (firstTarget d initial).val = firstCurve d initial stepSize := rfl

def cell0Initial (d : Direction) (p : {p : Point // p ∈ cellDomain 0}) : InitialAt d :=
  ⟨cellSeed 0 p.val, cell0_seed_in_initial d p.val p.property⟩

theorem firstCurve_continuousOn (d : Direction) (initial : InitialAt d) :
    ContinuousOn (firstCurve d initial) (Icc 0 (stepSize : ℝ)) :=
  HasDerivWithinAt.continuousOn (fun t ht => ((firstCurve_spec d initial).2.1 t ht).1)

theorem firstCurve_stays_in_sourceCube (d : Direction) (initial : InitialAt d)
    (t : ℝ) (ht : t ∈ Icc 0 (stepSize : ℝ)) :
    firstCurve d initial t ∈ ContinuousGradient.sourceCube :=
  tube_in_sourceCube (all_row_arithmetic 0 d 0) _ ((firstCurve_spec d initial).2.1 t ht).2

theorem firstTarget_in_next_arithmetic_current (d : Direction) (initial : InitialAt d) :
    InRectangle (initialBox 0 d 1) (firstTarget d initial).val ∧ RowArithmetic 0 d 1 :=
  ⟨(firstTarget d initial).property, all_row_arithmetic 0 d 1⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
