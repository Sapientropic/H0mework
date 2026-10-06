import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCoframeDilation
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceKineticScale

/-! The original coframe dilation differentiates the actual scalar coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceDilationMultiplier
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussNativeForm GaussCoframeCore
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceKineticScale
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Topology InnerProductSpace

private theorem component_multiply (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (f : QuantumTest) (word : Occupation) :
    (component word (multiply a smooth f) : SourceCoordinateSlice → ℂ) =
      fun z => (a z : ℂ)*component word f z := rfl

private theorem derivative_multiply (a ap : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (he : ∀ z : physicalChart, fderiv ℝ a z.val (euler z.val)=ap z.val)
    (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    fderiv ℝ (component word (multiply a smooth f)) z.val (euler z.val) =
      (a z.val : ℂ)*fderiv ℝ (component word f) z.val (euler z.val)+
        (ap z.val : ℂ)*f z.val word := by
  rw [component_multiply]
  have hc := (Complex.ofRealCLM.hasFDerivAt (x := a z.val)).comp z.val
    ((smooth z).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (fun w => (a w : ℂ)) _ z.val at hc
  rw [fderiv_fun_mul hc.differentiableAt
    ((component word f).contDiff.differentiable (by simp)).differentiableAt, hc.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply]
  rw [he]
  change (a z.val : ℂ)*fderiv ℝ (component word f) z.val (euler z.val)+
    f z.val word*(ap z.val : ℂ)=_
  ring

theorem dilation_multiply (a ap : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (smoothp : ∀ z : physicalChart, ContDiffAt ℝ ∞ ap z.val)
    (he : ∀ z : physicalChart, fderiv ℝ a z.val (euler z.val)=ap z.val)
    (f : QuantumTest) :
    dilation (multiply a smooth f) = multiply a smooth (dilation f) -
      (2*Complex.I/3) • multiply ap smoothp f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · apply PiLp.ext
    intro word
    change dilation (multiply a smooth f) z word =
      (a z : ℂ)*dilation f z word-(2*Complex.I/3)*((ap z : ℂ)*f z word)
    rw [dilation_apply (multiply a smooth f) word ⟨z,hz⟩,
      dilation_apply f word ⟨z,hz⟩, derivative_multiply a ap smooth he f word ⟨z,hz⟩]
    change -Complex.I*((2/3 : ℂ)*((a z : ℂ)*
      fderiv ℝ (component word f) z (euler z)+(ap z : ℂ)*f z word)+
      (word.card+4 : ℂ)*((a z : ℂ)*f z word)) = _
    ring
  · have hl : dilation (multiply a smooth f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz
        ((dilation (multiply a smooth f)).tsupport_subset h))
    have hr : (multiply a smooth (dilation f)-(2*Complex.I/3) • multiply ap smoothp f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz
        ((multiply a smooth (dilation f)-(2*Complex.I/3) • multiply ap smoothp f).tsupport_subset h))
    exact hl.trans hr.symm

theorem multiplier_commutator (a ap : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (smoothp : ∀ z : physicalChart, ContDiffAt ℝ ∞ ap z.val)
    (he : ∀ z : physicalChart, fderiv ℝ a z.val (euler z.val)=ap z.val) :
    dilation*multiply a smooth-multiply a smooth*dilation =
      (-2*Complex.I/3) • multiply ap smoothp := by
  apply LinearMap.ext
  intro f
  change dilation (multiply a smooth f)-multiply a smooth (dilation f) =
    (-2*Complex.I/3) • multiply ap smoothp f
  rw [dilation_multiply a ap smooth smoothp he]
  module

theorem homogeneous_multiplier (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) (k : ℝ)
    (he : ∀ z : physicalChart, fderiv ℝ a z.val (euler z.val)=k*a z.val) :
    dilation*multiply a smooth-multiply a smooth*dilation =
      ((-2*Complex.I/3)*(k : ℂ)) • multiply a smooth := by
  let smoothp : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => k*a w) z.val :=
    fun z => contDiffAt_const.mul (smooth z)
  have hm : multiply (fun w => k*a w) smoothp = (k : ℂ) • multiply a smooth := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change ((k*a z : ℝ) : ℂ) • f z=(k : ℂ) • ((a z : ℂ) • f z)
    rw [Complex.ofReal_mul, mul_smul]
  rw [multiplier_commutator a (fun w => k*a w) smooth smoothp he, hm, smul_smul]

theorem scalar_weight_commutator :
    dilation*multiply scalarWeight scalarWeight_smooth-
      multiply scalarWeight scalarWeight_smooth*dilation =
      (2*Complex.I) • multiply scalarWeight scalarWeight_smooth := by
  have h := homogeneous_multiplier scalarWeight scalarWeight_smooth (-3)
    (fun z => scalar_weight_euler z)
  have hc : (-2*Complex.I/3)*((-3 : ℝ) : ℂ)=2*Complex.I := by push_cast; ring
  rw [hc] at h
  exact h

theorem gauge_weight_commutator (i j : Fin 3) :
    dilation*multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)-
      multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*dilation =
      (-2*Complex.I/3) • multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) := by
  have h := homogeneous_multiplier (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) 1
    (fun z => by simpa only [one_mul] using gauge_weight_euler z i j)
  simpa using h

theorem coframe_coefficient_commutator (i j : Fin 6) :
    dilation*coefficientAction i j-coefficientAction i j*dilation =
      (2*Complex.I/3) • coefficientAction i j := by
  have h := homogeneous_multiplier (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j) (-1)
    (fun z => by simpa only [neg_one_mul] using coframe_coefficient_euler z i j)
  change dilation*coefficientAction i j-coefficientAction i j*dilation =
    ((-2*Complex.I/3)*((-1 : ℝ) : ℂ)) • coefficientAction i j at h
  have hc : (-2*Complex.I/3)*((-1 : ℝ) : ℂ)=2*Complex.I/3 := by push_cast; ring
  rw [hc] at h
  exact h

theorem current_coefficient_commutator (i : Fin 6) :
    dilation*multiply (GaussCoframeForm.currentCoefficient i) (GaussCoframeForm.currentCoefficient_smooth i)-
      multiply (GaussCoframeForm.currentCoefficient i) (GaussCoframeForm.currentCoefficient_smooth i)*dilation =
      (4*Complex.I/3) • multiply (GaussCoframeForm.currentCoefficient i)
        (GaussCoframeForm.currentCoefficient_smooth i) := by
  have h := homogeneous_multiplier (GaussCoframeForm.currentCoefficient i)
    (GaussCoframeForm.currentCoefficient_smooth i) (-2)
    (fun z => current_coefficient_euler z i)
  have hc : (-2*Complex.I/3)*((-2 : ℝ) : ℂ)=4*Complex.I/3 := by push_cast; ring
  rw [hc] at h
  exact h

theorem inverse_volume_commutator :
    dilation*multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth-
      multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*dilation =
      (2*Complex.I) • multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth := by
  have h := homogeneous_multiplier GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth (-3)
    (fun z => inverse_volume_euler z)
  have hc : (-2*Complex.I/3)*((-3 : ℝ) : ℂ)=2*Complex.I := by push_cast; ring
  rw [hc] at h
  exact h

end LowEnergy.SourceDilationMultiplier
