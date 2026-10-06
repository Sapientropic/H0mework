import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceDilationMomentum
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceHamiltonianVolume

/-! The full original kinetic action carries the source scale current. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceDilationKinetic
open GaussCoreDifferential GaussNativeForm GaussNativeEnergy GaussCoframeForm GaussHistoryHilbert
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceEulerCore
open SourceDilationAlgebra SourceDilationMomentum SourceDilationMultiplier SourceKineticTranspose
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff

private theorem quantum_current (A : Matrix Mode Mode ℂ) :
    dilation*GaussQuantumMultiplier.action (fun _ => A) (fun _ => contDiffAt_const)-
      GaussQuantumMultiplier.action (fun _ => A) (fun _ => contDiffAt_const)*dilation=0 := by
  let T := GaussQuantumMultiplier.action (fun _ => A) (fun _ => contDiffAt_const)
  have hE : Commute eulerAction T := euler_invariant_multiplier _ _ (fun _ _ => rfl)
  have hN : Commute number T := number_multiplier _ _ (fun _ => GaussQuantumMultiplier.number_commute A)
  have h : eulerAction*T-T*eulerAction=(0 : ℂ) • T := by rw [hE.eq,sub_self,zero_smul]
  rw [dilation_operator]
  simpa only [mul_zero,zero_smul,Module.End.one_eq_id] using! affine_dilation _ _ _ 0 h hN

theorem spin_current (a : Fin 7) :
    dilation*GaussCoframeSpin.current a-GaussCoframeSpin.current a*dilation=0 :=
  quantum_current (GaussCoframeSpin.full a)

theorem number_current : dilation*number-number*dilation=0 := quantum_current _

private theorem native_sandwich_current (v w : GaussLiveMomentum.Ambient)
    (c : SourceCoordinateSlice → ℝ) (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (a : ℂ) (h : dilation*multiply c smooth-multiply c smooth*dilation=a • multiply c smooth) :
    dilation*sandwich v w c smooth-sandwich v w c smooth*dilation=a • sandwich v w c smooth := by
  have h1 := homogeneous_mul dilation (multiply c smooth) (GaussCoreDifferential.covariantMomentum w)
    a 0 h (by simpa only [zero_smul] using native_momentum_current w)
  have h2 := homogeneous_mul dilation (GaussMomentumAdjoint.adjoint v)
    (multiply c smooth*GaussCoreDifferential.covariantMomentum w) 0 (a+0)
    (by simpa only [zero_smul] using native_adjoint_current v) h1
  simpa only [zero_add,add_zero] using! h2

theorem scalar_kinetic_current :
    dilation*scalarKinetic-scalarKinetic*dilation=(2*Complex.I) • scalarKinetic :=
  homogeneous_smul _ _ _ _ (homogeneous_sum _ _ _ (fun a =>
    native_sandwich_current (scalarDirection a) (scalarDirection a) _ _ _ scalar_weight_commutator))

theorem gauge_kinetic_current :
    dilation*gaugeKinetic-gaugeKinetic*dilation=(-2*Complex.I/3) • gaugeKinetic :=
  homogeneous_smul _ _ _ _ (homogeneous_sum _ _ _ (fun a =>
    homogeneous_sum _ _ _ (fun i => homogeneous_sum _ _ _ (fun j =>
      native_sandwich_current (gaugeDirection i a) (gaugeDirection j a) _ _ _
        (gauge_weight_commutator i j)))))

theorem coframe_term_current (i j : Fin 6) :
    dilation*GaussCoframeKinetic.term i j-GaussCoframeKinetic.term i j*dilation=
      (2*Complex.I) • GaussCoframeKinetic.term i j := by
  have h1 := homogeneous_mul dilation (coefficientAction i j) (GaussCoframeCore.momentum j)
    (2*Complex.I/3) (2*Complex.I/3) (coframe_coefficient_commutator i j)
      (coframe_momentum_current j)
  have h2 := homogeneous_mul dilation (GaussCoframeCore.adjoint i)
    (coefficientAction i j*GaussCoframeCore.momentum j)
    (2*Complex.I/3) (2*Complex.I/3+2*Complex.I/3) (coframe_adjoint_current i) h1
  have hc : 2*Complex.I/3+(2*Complex.I/3+2*Complex.I/3)=2*Complex.I := by ring
  simpa only [hc] using! h2

theorem coframe_kinetic_current :
    dilation*GaussCoframeKinetic.kinetic-GaussCoframeKinetic.kinetic*dilation=
      (2*Complex.I) • GaussCoframeKinetic.kinetic :=
  homogeneous_sum _ _ _ (fun i => homogeneous_sum _ _ _ (coframe_term_current i))

private theorem mixed_current (i : Fin 6) (a : Fin 7)
    (c : SourceCoordinateSlice → ℝ) (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (hc : dilation*multiply c smooth-multiply c smooth*dilation=
      (4*Complex.I/3) • multiply c smooth) :
    dilation*mixed i a c smooth-mixed i a c smooth*dilation=(2*Complex.I) • mixed i a c smooth := by
  have hS : dilation*GaussCoframeSpin.current a-GaussCoframeSpin.current a*dilation=
      (0 : ℂ) • GaussCoframeSpin.current a := by simpa only [zero_smul] using spin_current a
  have h1 := homogeneous_mul dilation (GaussCoframeSpin.current a)
    (multiply c smooth*GaussCoframeCore.momentum i) 0 (4*Complex.I/3+2*Complex.I/3) hS
    (homogeneous_mul _ _ _ _ _ hc (coframe_momentum_current i))
  have h2 := homogeneous_mul dilation (GaussCoframeCore.adjoint i)
    (multiply c smooth*GaussCoframeSpin.current a) (2*Complex.I/3) (4*Complex.I/3+0)
    (coframe_adjoint_current i) (homogeneous_mul _ _ _ _ _ hc hS)
  have hfirst : 0+(4*Complex.I/3+2*Complex.I/3)=2*Complex.I := by ring
  have hsecond : 2*Complex.I/3+(4*Complex.I/3+0)=2*Complex.I := by ring
  rw [hfirst] at h1
  rw [hsecond] at h2
  exact homogeneous_smul _ _ _ _ (homogeneous_add _ _ _ _ h1 h2)

private theorem multiply_scale (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (r : ℝ)
    (smoothr : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => r*c w) z.val) :
    multiply (fun w => r*c w) smoothr=(r : ℂ) • multiply c smooth := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((r*c z : ℝ) : ℂ) • f z=(r : ℂ) • ((c z : ℂ) • f z)
  rw [Complex.ofReal_mul,mul_smul]

theorem coframe_current_current :
    dilation*currentAction-currentAction*dilation=(2*Complex.I) • currentAction := by
  have hneg : dilation*multiply (fun z => -currentCoefficient 0 z)
      (fun z => (currentCoefficient_smooth 0 z).neg)-
    multiply (fun z => -currentCoefficient 0 z)
      (fun z => (currentCoefficient_smooth 0 z).neg)*dilation=
    (4*Complex.I/3) • multiply (fun z => -currentCoefficient 0 z)
      (fun z => (currentCoefficient_smooth 0 z).neg) := by
    have hm : multiply (fun z => -currentCoefficient 0 z)
      (fun z => (currentCoefficient_smooth 0 z).neg)=
      (-1 : ℂ) • multiply (currentCoefficient 0) (currentCoefficient_smooth 0) := by
      simpa only [neg_one_mul,Complex.ofReal_neg,Complex.ofReal_one] using!
        multiply_scale (currentCoefficient 0) (currentCoefficient_smooth 0) (-1)
          (fun z => contDiffAt_const.mul (currentCoefficient_smooth 0 z))
    rw [hm]
    exact homogeneous_smul _ _ _ _ (current_coefficient_commutator 0)
  exact homogeneous_add _ _ _ _ (homogeneous_add _ _ _ _ (homogeneous_add _ _ _ _
    (mixed_current 1 5 _ _ (current_coefficient_commutator 0))
    (mixed_current 3 3 _ _ (current_coefficient_commutator 1)))
    (mixed_current 3 4 _ _ hneg)) (mixed_current 4 3 _ _ (current_coefficient_commutator 2))

theorem spin_square_current (a : Fin 7) :
    dilation*spinSquare a-spinSquare a*dilation=(2*Complex.I) • spinSquare a := by
  have hS : dilation*GaussCoframeSpin.current a-GaussCoframeSpin.current a*dilation=
      (0 : ℂ) • GaussCoframeSpin.current a := by simpa only [zero_smul] using spin_current a
  have h1 := homogeneous_mul _ _ _ _ _ inverse_volume_commutator hS
  have h2 := homogeneous_mul _ _ _ _ _ hS h1
  have h := homogeneous_smul _ _ _ (spinWeight a : ℂ) h2
  simpa only [zero_add,add_zero] using! h

theorem number_shift_current :
    dilation*numberShift-numberShift*dilation=(2*Complex.I) • numberShift := by
  have hm : multiply numberCoefficient numberCoefficient_smooth=
      ((-(9/8 : ℝ) : ℝ) : ℂ) • multiply inverseVolume inverseVolume_smooth :=
    multiply_scale inverseVolume inverseVolume_smooth _ _
  have hc : dilation*multiply numberCoefficient numberCoefficient_smooth-
      multiply numberCoefficient numberCoefficient_smooth*dilation=
      (2*Complex.I) • multiply numberCoefficient numberCoefficient_smooth := by
    rw [hm]
    exact homogeneous_smul _ _ _ _ inverse_volume_commutator
  have hN : dilation*number-number*dilation=(0 : ℂ) • number := by
    simpa only [zero_smul] using number_current
  have h1 := homogeneous_mul _ _ _ _ _ hN hc
  have h2 := homogeneous_mul _ _ _ _ _ hc hN
  simp only [zero_add,add_zero] at h1 h2
  exact homogeneous_smul _ _ _ _ (homogeneous_add _ _ _ _ h1 h2)

theorem kinetic_scale_current :
    dilation*kineticAction-kineticAction*dilation=
      (2*Complex.I) • kineticAction-(8*Complex.I/3) • gaugeKinetic := by
  let C := GaussCoframeKinetic.kinetic+currentAction+(∑ a : Fin 7,spinSquare a)+numberShift
  have hC : dilation*C-C*dilation=(2*Complex.I) • C :=
    homogeneous_add _ _ _ _ (homogeneous_add _ _ _ _
      (homogeneous_add _ _ _ _ coframe_kinetic_current coframe_current_current)
      (homogeneous_sum _ _ _ spin_square_current)) number_shift_current
  have hk : kineticAction=scalarKinetic+gaugeKinetic+C := by
    unfold kineticAction coframeAction C
    abel
  rw [hk]
  calc
    _ = (dilation*scalarKinetic-scalarKinetic*dilation)+
        (dilation*gaugeKinetic-gaugeKinetic*dilation)+(dilation*C-C*dilation) := by noncomm_ring
    _ = _ := by
      rw [scalar_kinetic_current,gauge_kinetic_current,hC]
      module

theorem volume_scale_current :
    dilation*volumeAction-volumeAction*dilation=(-2*Complex.I) • volumeAction := by
  have h := homogeneous_multiplier volume (fun _ => volume_smooth.contDiffAt) 3
    (fun z => SourceKineticScale.euler_of_scale volume 3 z volume_smooth.contDiffAt
      (fun r _ => by simpa only [zpow_natCast] using! volume_scale r z.val))
  have hc : (-2*Complex.I/3)*((3 : ℝ) : ℂ)= -2*Complex.I := by push_cast; ring
  simpa only [hc] using! h

end LowEnergy.SourceDilationKinetic
