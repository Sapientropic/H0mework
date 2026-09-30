import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceEvolution
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceSeedColumns

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed TrueFlowDifferential TrueTubeWholeActual
open Set Metric
noncomputable section

/-- The actual gradient and the initial-value response satisfy the same Hessian equation. -/
theorem initialFlowDerivative_gradient (p : BandPoint) (s : Time) :
    initialFlowDerivative p s (sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val)) =
      sourceGradient (actualPath p s) := by
  let seed := sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val)
  have equal : EqOn (extendPath (sourceResponse p seed)) (fun t => sourceGradient (fullFlow p t))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun t h => sourceHessianLinear (fullFlow p t) h)
      (s := fun _ => Set.univ) (K := TrueTubeHull.lipschitzConstant) (t₀ := 0)
    · intro t ht
      exact ((sourceHessianLinear (fullFlow p t)).lipschitzWith_of_opNorm_le
        (actualPath_hessian_bound p ⟨t, Ioo_subset_Icc_self ht⟩)).lipschitzOnWith
    · constructor <;> norm_num
    · exact (continuous_extendPath (sourceResponse p seed)).continuousOn
    · intro t ht
      have derivative := sourceResponse_actual_variational p seed ⟨t, Ioo_subset_Icc_self ht⟩
      have agrees := extendPath_coe (sourceResponse p seed) ⟨t, Ioo_subset_Icc_self ht⟩
      change extendPath (sourceResponse p seed) t = sourceResponse p seed ⟨t, Ioo_subset_Icc_self ht⟩ at agrees
      rw [← agrees] at derivative
      exact derivative.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · intro t _
      trivial
    · exact (sourceGradient_contDiff 1).continuous.comp_continuousOn (fullFlow_original p).continuousOn
    · intro t ht
      exact (sourceGradient_hasFDerivAt (fullFlow p t)).comp_hasDerivAt t
        ((fullFlow_original p t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    · intro t _
      trivial
    · rw [fullFlow_starts]
      change extendPath (sourceResponse p seed) (zeroTime : ℝ) = seed
      rw [extendPath_coe, sourceResponse_starts]
  have result : extendPath (sourceResponse p seed) (s : ℝ) = sourceGradient (fullFlow p s) :=
    equal s.property
  rw [extendPath_coe] at result
  exact result

/-- The true Jacobian is the generated initial-value response of the full seed-time tangent. -/
theorem trueJacobian_flow_factorization (p : BandPoint) :
    trueJacobian p = (initialFlowDerivative p (actualParameterTime p)).comp
      (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val +
        (ContinuousLinearMap.proj 2).smulRight
          (sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val))) := by
  apply ContinuousLinearMap.ext
  intro h
  rw [trueJacobian_decomposition]
  change initialFlowDerivative p (actualParameterTime p)
      (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val h) +
        h 2 • sourceGradient (trueParameterMap p.val) =
    initialFlowDerivative p (actualParameterTime p)
      (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val h +
        h 2 • sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val))
  rw [map_add, map_smul, initialFlowDerivative_gradient]
  rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
