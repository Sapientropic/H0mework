import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledPath
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueTubeTrace TrueTubeContinuation ContinuousGradient Set
noncomputable section

/-- The scaled integral equation identifies the same raw trajectory by global-field uniqueness. -/
theorem solvedScaledPath_eq_rawPath (x : Point) (a : ℝ) (u : Path) (ha : |a| ≤ 1)
    (equation : u = pathConst x + a • volterra (pathGradient u))
    (inside : ∀ t : Time, u t ∈ sourceCube) : u = scaledRawPath x a := by
  let curve : ℝ → Point := fun t => x + a • pathPrimitive (pathGradient u) t
  have curve_eq (t : Time) : curve t.val = u t := by
    have pointwise := congrArg (fun f : Path => f t) equation
    exact pointwise.symm
  have curve_derivative (t : ℝ) (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      HasDerivAt curve (a • globalField 1 (curve t)) t := by
    let time : Time := ⟨t, ht.1.le, ht.2.le⟩
    rw [curve_eq time, globalField_eq_original 1 _ (inside time)]
    simp only [signedGradient, TrueTubeChecks.directions.2, Rat.cast_one, one_smul]
    exact ((hasDerivAt_pathPrimitive (pathGradient u) time).const_smul a).const_add x
  have same : EqOn curve (scaledRawFlow x a) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
    ODE_solution_unique_of_mem_Icc
      (v := fun _ z => a • globalField 1 z) (s := fun _ => univ) (t₀ := 0)
      (fun _ _ => ((lipschitzWith_smul a).comp (globalField_lipschitz 1)).lipschitzOnWith)
      (by constructor <;> norm_num)
      (continuous_const.add ((continuous_pathPrimitive (pathGradient u)).const_smul a)).continuousOn
      curve_derivative (fun _ _ => mem_univ _)
      (scaledRawFlow_extended x a ha).continuousOn
      (fun t ht => (scaledRawFlow_extended x a ha t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))
      (fun _ _ => mem_univ _)
      (by simp [curve, pathPrimitive, scaledRawFlow, rawFlow_starts])
  apply ContinuousMap.ext
  intro t
  exact (curve_eq t).symm.trans ((same t.property).trans
    (scaledRawPath_eq_scaledRawFlow x a ha t).symm)

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
