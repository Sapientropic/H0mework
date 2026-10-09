import H0mework.Versions.AB.Chemistry.LAlanineTrueTube.SourceData
import H0mework.Versions.R9c73a630.Chemistry.LAlanineGradient.Bounds
import H0mework.Versions.AB.Chemistry.LAlanineTrueTubeWhole.SourceData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks

open TrueTubeSource TrueTubeWholeSource SourceFiniteData SourceGaussianModel SourceSignedEvaluator ContinuousGradient
noncomputable section

theorem call_cube_bounds : ∀ c : Call, ∀ axis : Fin 3,
    boxCentre axis - boxRadius ≤ (callBox c axis).1 ∧
      (callBox c axis).2 ≤ boxCentre axis + boxRadius := by decide +kernel

theorem call_in_sourceCube (c : Call) (x : Point) (inside : InRectangle (callBox c) x) :
    x ∈ sourceCube := by
  intro axis
  have lower : (boxCentre axis : ℝ) - (boxRadius : ℝ) ≤ ((callBox c axis).1 : ℝ) := by
    exact_mod_cast (call_cube_bounds c axis).1
  have upper : ((callBox c axis).2 : ℝ) ≤ (boxCentre axis : ℝ) + (boxRadius : ℝ) := by
    exact_mod_cast (call_cube_bounds c axis).2
  apply abs_le.mpr
  constructor <;> linarith [(inside axis).1, (inside axis).2]

theorem initial_call_cells : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    callBox (initialCallAt d i) axis = initialBox d i axis := by decide +kernel
theorem tube_call_cells : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    callBox (tubeCallAt d i) axis = tubeBox d i axis := by decide +kernel

theorem initial_call_box (d : Direction) (i : Step) : callBox (initialCallAt d i) = initialBox d i :=
  funext (initial_call_cells d i)
theorem tube_call_box (d : Direction) (i : Step) : callBox (tubeCallAt d i) = tubeBox d i :=
  funext (tube_call_cells d i)

theorem initial_call_address (d : Direction) (i : Step) :
    1024 + (initialCallAt d i).val = initialCall d i := by
  rfl

theorem tube_call_address (d : Direction) (i : Step) :
    1024 + (tubeCallAt d i).val = tubeCall d i := by
  simp only [tubeCallAt, tubeCall, initialCall, rowOffset]
  omega

theorem tube_in_sourceCube (d : Direction) (i : Step) (x : Point) (inside : InRectangle (tubeBox d i) x) :
    x ∈ sourceCube := call_in_sourceCube (tubeCallAt d i) x ((tube_call_box d i).symm ▸ inside)

theorem initial_in_sourceCube (d : Direction) (i : Step) (x : Point) (inside : InRectangle (initialBox d i) x) :
    x ∈ sourceCube := call_in_sourceCube (initialCallAt d i) x ((initial_call_box d i).symm ▸ inside)

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
