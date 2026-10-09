import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Variational

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel
open _root_.LAlanineTrueFlowDifferential
noncomputable section

def oppositeTime (t : Time) : Time := ⟨-(t : ℝ),by constructor <;> linarith [t.property.1,t.property.2]⟩

theorem original_inverse_map (t : Time) :
    (fun y => flow (flow y (spatialStep*(t : ℝ))) (spatialStep*(oppositeTime t : ℝ))) = id := by
  funext y
  change flow (flow y (spatialStep*(t : ℝ))) (spatialStep*(-(t : ℝ))) = y
  rw [mul_neg]
  exact flow_inverse y _

theorem flowDerivative_left_inverse (x : Point) (t : Time) :
    (flowDerivative (flow x (spatialStep*(t : ℝ))) (oppositeTime t)).comp (flowDerivative x t) =
      ContinuousLinearMap.id ℝ Point := by
  have chain := (original_flow_strictDerivative (flow x (spatialStep*(t : ℝ))) (oppositeTime t)).comp x
    (original_flow_strictDerivative x t)
  have actual : HasStrictFDerivAt id
      ((flowDerivative (flow x (spatialStep*(t : ℝ))) (oppositeTime t)).comp (flowDerivative x t)) x := by
    rw [← original_inverse_map t]
    exact chain
  exact actual.hasFDerivAt.unique (hasFDerivAt_id x)

theorem flowDerivative_injective (x : Point) (t : Time) : Function.Injective (flowDerivative x t) := by
  intro v w same
  have read := congrArg (flowDerivative (flow x (spatialStep*(t : ℝ))) (oppositeTime t)) same
  change ((flowDerivative (flow x (spatialStep*(t : ℝ))) (oppositeTime t)).comp (flowDerivative x t)) v =
    ((flowDerivative (flow x (spatialStep*(t : ℝ))) (oppositeTime t)).comp (flowDerivative x t)) w at read
  rw [flowDerivative_left_inverse] at read
  exact read

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
