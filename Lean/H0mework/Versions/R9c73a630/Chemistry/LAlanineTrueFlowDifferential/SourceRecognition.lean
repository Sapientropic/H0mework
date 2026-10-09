import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceRawPath
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueTubeTrace TrueTubeContinuation ContinuousGradient Set
noncomputable section

/-- Uniqueness identifies a source-cube solution of the original integral equation
with the existing two-direction window family. -/
theorem solvedPath_eq_rawPath (x : Point) (u : Path)
    (equation : u = pathConst x + volterra (pathGradient u))
    (inside : ∀ t : Time, u t ∈ sourceCube) : u = rawPath x := by
  let curve : ℝ → Point := fun t => x + pathPrimitive (pathGradient u) t
  have curve_eq (t : Time) : curve t.val = u t := by
    have pointwise := congrArg (fun f : Path => f t) equation
    exact pointwise.symm
  have curve_derivative (t : ℝ) (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      HasDerivAt curve (globalField 1 (curve t)) t := by
    let time : Time := ⟨t, ht.1.le, ht.2.le⟩
    rw [curve_eq time, globalField_eq_original 1 _ (inside time)]
    simp only [signedGradient, TrueTubeChecks.directions.2, Rat.cast_one, one_smul]
    exact (hasDerivAt_pathPrimitive (pathGradient u) time).const_add x
  have same : EqOn curve (rawFlow x) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
    ODE_solution_unique_of_mem_Icc
      (v := fun _ => globalField 1) (s := fun _ => univ) (t₀ := 0)
      (fun _ _ => (globalField_lipschitz 1).lipschitzOnWith)
      (by constructor <;> norm_num)
      (continuous_const.add (continuous_pathPrimitive (pathGradient u))).continuousOn
      curve_derivative (fun _ _ => mem_univ _)
      (rawFlow_extended x).continuousOn
      (fun t ht => (rawFlow_extended x t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))
      (fun _ _ => mem_univ _)
      (by simp [curve, pathPrimitive, rawFlow_starts])
  apply ContinuousMap.ext
  intro t
  exact (curve_eq t).symm.trans (same t.property)

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
