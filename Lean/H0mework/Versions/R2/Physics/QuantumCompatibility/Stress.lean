import H0mework.Versions.R2.Physics.QuantumCompatibility.DualResponse
import H0mework.Versions.R2.Physics.SpinPair.CoframeMatter

/-! The quantum response consumes the full source covariant derivative.
The same response load supplies the existing coframe variation, including
all sixteen stress entries and the actual lapse, spin and gauge scales. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open StageNineDiracDualFormNativeCoframeLocalVariation
open Stage9C.Material.SpinPair
open Stage9C.Dynamics.Homogeneous
open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

def temporalAction : Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (Matrix.diagonal
    ![Complex.I * (frequency : ℂ), Complex.I * (frequency : ℂ),
      -Complex.I * (frequency : ℂ), -Complex.I * (frequency : ℂ)])

def covariantAction : LorentzianIndex → Module.End ℂ DiracExteriorMatterCarrier :=
  Fin.cases temporalAction (fun direction =>
    (((spinScale - gaugeScale : ℝ) : ℂ) / 2) • diracMatrixMatterAction (spinRotation direction))

theorem actual_covariantAction (point : BasePoint) (direction : LorentzianIndex) :
    covariantAction direction (actual.matter point) =
      holonomicMatterCovariantDerivative actual point direction := by
  induction direction using Fin.cases with
  | zero =>
      rw [actual_matterCovariant_time, actual_matter]
      change diracMatrixMatterAction _ (spinPairMatter _ _) = _
      unfold spinPairMatter
      rw [sourceColorDiracMatter_matrix]
      congr 1
      ext spin color
      fin_cases spin <;> fin_cases color <;>
        simp [spinPairCoefficients, Fin.sum_univ_four]
  | succ direction =>
      rw [actual_matterCovariant_spatial, actual_matter]
      rfl

def kineticAction (internal direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • (diracMatrixMatterAction (diracGamma internal)).comp (covariantAction direction)

def kineticObservable (internal direction : LorentzianIndex) : Matrix8 :=
  responseMatrix (kineticAction internal direction)

def kineticLoad (point : BasePoint) : LorentzianCoframe :=
  fun internal direction => 4 * spinScale *
    (vectorRead point (kineticObservable internal direction)).re

theorem kineticLoad_eq_actual (point : BasePoint) : kineticLoad point = actualKineticLoad point := by
  ext internal direction
  have observed := congrArg Complex.re (actual_action_quantumResponse point (kineticAction internal direction))
  change (actual.conjugateMatter point
    (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (covariantAction direction (actual.matter point)))).re = _ at observed
  rw [actual_covariantAction] at observed
  change actualKineticLoad point internal direction = _ at observed
  simpa [kineticLoad, kineticObservable, Complex.mul_re, Complex.mul_im] using observed.symm

def frozenMatterDensity (point : BasePoint) (coframe : LorentzianCoframe) : ℝ :=
  |coframe.det| * ∑ direction, ∑ internal, coframe⁻¹ direction internal * kineticLoad point internal direction

theorem frozenMatterDensity_eq_classical (point : BasePoint) (coframe : LorentzianCoframe) :
    frozenMatterDensity point coframe =
      diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource point
        (toContinuumPointField actual point) coframe := by
  rw [actual_frozenMatterDensity]
  simp only [frozenMatterDensity, kineticLoad_eq_actual]

theorem frozenMatterDensity_hasDerivAt (point : BasePoint) (direction : LorentzianCoframe) :
    HasDerivAt (fun parameter : ℝ =>
      frozenMatterDensity point (actual.coframe point + parameter • direction))
      (-6*(spinScale-gaugeScale)*spinScale*direction 0 0 +
        2*lapse*(spinScale-gaugeScale)*spinScale*(direction 1 1 + direction 2 2 + direction 3 3)) 0 := by
  simp_rw [frozenMatterDensity_eq_classical]
  have derivative := diracDualFormNativeCoframeMatterDensity_hasFDerivAt positiveSmoothUnifiedSource point
    (toContinuumPointField actual point) (actual_nondegenerate point)
  rw [show (toContinuumPointField actual point).coframe = actual.coframe point from rfl] at derivative
  have derivative' : HasFDerivAt
      (diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource point
        (toContinuumPointField actual point))
      (diracDualFormNativeCoframeMatterEulerCovector positiveSmoothUnifiedSource point
        (toContinuumPointField actual point))
      (actual.coframe point + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using derivative
  have line := derivative'.comp_hasDerivAt (0 : ℝ)
    (coframe_line_hasDerivAt (actual.coframe point) direction)
  exact line.congr_deriv (actual_matterCoframe point direction)

theorem kineticLoad_source_prediction (point : BasePoint) :
    kineticLoad point = Matrix.diagonal
      ![4*spinScale*frequency, -2*spinScale*(spinScale-gaugeScale),
        -2*spinScale*(spinScale-gaugeScale), -2*spinScale*(spinScale-gaugeScale)] := by
  rw [kineticLoad_eq_actual, actualKineticLoad_diagonal]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
