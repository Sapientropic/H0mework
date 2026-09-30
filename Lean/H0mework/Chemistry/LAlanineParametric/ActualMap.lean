import H0mework.Chemistry.LAlanineParametric.RK4
import H0mework.Chemistry.LAlanineParametric.SeedDerivative
import H0mework.Chemistry.LAlanineGradient.Model

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousParameterMap

open SourceGaussianModel ContinuousGradient ContinuousSeed
open LAlanineContinuousPatch.Parametric
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Geometry

noncomputable section

def stepCount (run : Data.RunIndex) : Nat := (Source.run run).steps
def parameterTimeLinear (run : Data.RunIndex) : Point →L[ℝ] ℝ :=
  (1 / (stepCount run : ℝ)) • ContinuousLinearMap.proj 2

def initialMap (run : Data.RunIndex) (segment : Segment) : Point → Point :=
  bandSeed segment (Source.epsilon run)

def parameterMap (run : Data.RunIndex) (segment : Segment) (p : Point) : Point :=
  ((rk4Step sourceGradient (parameterTimeLinear run p))^[stepCount run]) (initialMap run segment p)

def parameterJacobian (run : Data.RunIndex) (segment : Segment) (p : Point) : Point →L[ℝ] Point :=
  (rk4JetIterate sourceGradient sourceHessianLinear (stepCount run)
    (parameterTimeLinear run p) (parameterTimeLinear run)
    (initialMap run segment p) (bandSeedDerivative segment (Source.epsilon run) p)).2

theorem source_counts_positive : ∀ run : Data.RunIndex, 0 < stepCount run := by decide +kernel

theorem parameterTime_readout (run : Data.RunIndex) (p : Point) :
    parameterTimeLinear run p = p 2 / (stepCount run : ℝ) := by
  simp only [parameterTimeLinear, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, one_div_mul_eq_div]

theorem parameterMap_hasFDerivAt (run : Data.RunIndex) (segment : Segment) (p : Point) :
    HasFDerivAt (parameterMap run segment) (parameterJacobian run segment p) p := by
  exact rk4Iterate_hasFDerivAt sourceGradient sourceHessianLinear sourceGradient_hasFDerivAt
    (parameterTimeLinear run).hasFDerivAt (bandSeed_hasFDerivAt segment (Source.epsilon run) p) (stepCount run)

theorem parameterJacobian_eq_fderiv (run : Data.RunIndex) (segment : Segment) (p : Point) :
    parameterJacobian run segment p = fderiv ℝ (parameterMap run segment) p :=
  (parameterMap_hasFDerivAt run segment p).fderiv.symm

theorem parameterMap_contDiff (run : Data.RunIndex) (segment : Segment) (order : WithTop ℕ∞) :
    ContDiff ℝ order (parameterMap run segment) :=
  rk4Iterate_contDiff sourceGradient (sourceGradient_contDiff order)
    (parameterTimeLinear run).contDiff (bandSeed_contDiff segment (Source.epsilon run) order) (stepCount run)

theorem parameterJacobian_contDiff (run : Data.RunIndex) (segment : Segment) :
    ContDiff ℝ 2 (parameterJacobian run segment) := by
  have exactJac : parameterJacobian run segment = fderiv ℝ (parameterMap run segment) :=
    funext (parameterJacobian_eq_fderiv run segment)
  rw [exactJac]
  exact (parameterMap_contDiff run segment 3).fderiv_right (by norm_num)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousParameterMap
