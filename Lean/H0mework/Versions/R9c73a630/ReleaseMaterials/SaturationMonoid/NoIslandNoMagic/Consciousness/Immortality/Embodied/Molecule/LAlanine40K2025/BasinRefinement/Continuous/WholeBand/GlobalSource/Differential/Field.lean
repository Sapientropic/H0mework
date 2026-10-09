import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Flow.Transport
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusCompositionStrict
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel ContinuousGradient
open _root_.LAlanineTrueFlowDifferential
noncomputable section

/-- Exact restriction of the original spatial flow parameter; no new physical clock. -/
def spatialStep : ℝ := 1 / ((sourceLipschitzBound : ℝ)+1)
theorem spatialStep_positive : 0 < spatialStep := by unfold spatialStep; positivity

def field (x : Point) : Point := spatialStep • sourceGradient x
def derivative (x : Point) : Point →L[ℝ] Point := spatialStep • sourceHessianLinear x

theorem field_contDiff : ContDiff ℝ 1 field := (sourceGradient_contDiff 1).const_smul spatialStep

theorem field_hasFDerivAt (x : Point) : HasFDerivAt field (derivative x) x :=
  (sourceGradient_hasFDerivAt x).const_smul spatialStep

theorem derivative_bound (x : Point) : ‖derivative x‖ ≤ 1 := by
  have h := sourceHessianLinear_uniform_bound x
  rw [derivative,norm_smul,Real.norm_eq_abs,abs_of_pos spatialStep_positive]
  have small : spatialStep*(sourceLipschitzBound : ℝ) < 1 := by
    unfold spatialStep
    rw [one_div_mul_eq_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_left h spatialStep_positive.le).trans small.le

def actualPath (x : Point) : Path :=
  ⟨fun t => flow x (spatialStep*(t : ℝ)),(flow_continuous x).comp (continuous_const.mul continuous_subtype_val)⟩

theorem actual_derivative (x : Point) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow x (spatialStep*s)) (field (flow x (spatialStep*t))) t := by
  have dt : HasDerivAt (fun s : ℝ => spatialStep*s) spatialStep t := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul spatialStep
  exact (flow_hasDerivAt x (spatialStep*t)).scomp t dt

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
