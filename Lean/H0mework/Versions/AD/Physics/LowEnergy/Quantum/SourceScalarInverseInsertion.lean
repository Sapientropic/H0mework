import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarAffineScaleTransport
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceNativeMixedCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseInsertionAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarInverseInsertion
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativePotential
open GaussYukawaCoefficient GaussQuantumMultiplier GaussFockWeights
open SourceEulerCore SourceDilationAlgebra GaussCoframeForm
open SourceMixedNativeReturn SourceCoframeDilation SourceCoframeVolumeCurrent
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet
open scoped InnerProductSpace ContDiff
abbrev End := SourceScalarGaugeScale.End
abbrev Flow := SourceScalarAffineScaleTransport.coreFlow
abbrev Phi := SourceScalarAffineScaleTransport.generator

private theorem full_apply (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  cases sharp <;> rfl

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (fullAction sharp g)=sourcePair (fullAction (!sharp) f) g := by
  cases sharp
  · change sourcePair f (GaussYukawaOperator.originalAction g)=
      sourcePair (GaussFullHamiltonian.adjointAction f) g
    have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem field_scale (t : ℝ) (z : SourceCoordinateSlice) :
    scalarField (SourceScalarAffineScaleTransport.scaleEquiv t z)=
      Real.exp t • scalarField z := by
  change (vacuum : Scalar)+
    ((Real.exp t) • ((z.2.1 : Scalar)+(vacuum : Scalar))-(vacuum : Scalar))=
      Real.exp t • ((vacuum : Scalar)+(z.2.1 : Scalar))
  rw [add_comm (vacuum : Scalar) (z.2.1 : Scalar)]
  abel

/-- The actual affine source field scales the complete original Yukawa branch. -/
theorem original_full_affine_flow (sharp : Bool) (t : ℝ) (f : QuantumTest) :
    Flow t (fullAction sharp f)=(Real.exp t : ℂ) • fullAction sharp (Flow t f) := by
  apply DFunLike.ext
  intro z
  have h (q : QuantumTest) : Flow t q z=
      (Real.exp ((61/2 : ℝ)*t) : ℂ) • q (SourceScalarAffineScaleTransport.scaleEquiv t z) := rfl
  have hs (c : ℂ) (q : QuantumTest) : (c • q) z=c • q z := rfl
  rw [h,full_apply,field_scale,map_smul,smul_apply,hs,full_apply,h,map_smul]
  rw [←algebraMap_smul ℂ (Real.exp t)
    ((branchMap sharp (scalarField z)) (f (SourceScalarAffineScaleTransport.scaleEquiv t z)))]
  exact smul_comm _ _ _

/-- Source homogeneity follows from the true weak derivatives, without a bounded-Y hypothesis. -/
theorem original_full_affine_jet (sharp : Bool) : deltaPhi (fullAction sharp)=fullAction sharp := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  apply LinearMap.ext
  intro f
  apply GaussCoreLabel.pair_separates
  intro k
  have hL := SourceScalarAffineScaleTransport.weak_flow_derivative k (fullAction sharp f) 0
  have hR := SourceScalarAffineScaleTransport.weak_flow_derivative (fullAction (!sharp) k) f 0
  have hExp : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ)) (1 : ℂ) 0 := by
    simpa only [Real.exp_zero,Complex.ofRealCLM_apply,Complex.ofReal_one,Function.comp_apply] using!
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_exp 0)
  have h := hExp.mul hR
  have he (t : ℝ) : sourcePair k (Flow t (fullAction sharp f))=
      (Real.exp t : ℂ)*sourcePair (fullAction (!sharp) k) (Flow t f) := by
    rw [original_full_affine_flow]
    simpa only [sourcePair,map_smul,inner_smul_right] using
      congrArg (fun c : ℂ => (Real.exp t : ℂ)*c) (full_pair sharp k (Flow t f))
  have hd := (hL.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => (he t).symm))).unique h
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero,Real.exp_zero,
    Complex.ofReal_one,one_mul] at hd
  rw [←full_pair sharp k f,←full_pair sharp k (Phi f)] at hd
  change sourcePair k (Phi (fullAction sharp f)-fullAction sharp (Phi f))=_
  simp only [sourcePair,map_sub,inner_sub_right] at hd ⊢
  linear_combination hd

private theorem full_gauge_flow (sharp : Bool) (t : ℝ) (f : QuantumTest) :
    SourceGaugeScaleTransport.coreFlow t (fullAction sharp f)=
      fullAction sharp (SourceGaugeScaleTransport.coreFlow t f) := by
  apply DFunLike.ext
  intro z
  have h (q : QuantumTest) : SourceGaugeScaleTransport.coreFlow t q z=
      (Real.exp (18*t) : ℂ) • q (SourceGaugeScaleTransport.scaleEquiv t z) := rfl
  have hs : scalarField (SourceGaugeScaleTransport.scaleEquiv t z)=scalarField z := rfl
  rw [h,full_apply,hs,full_apply,h,map_smul]

theorem original_full_gauge_jet (sharp : Bool) : deltaGauge (fullAction sharp)=0 := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  apply LinearMap.ext
  intro f
  apply GaussCoreLabel.pair_separates
  intro k
  have hL := SourceGaugeScaleTransport.weak_flow_derivative k (fullAction sharp f) 0
  have hR := SourceGaugeScaleTransport.weak_flow_derivative (fullAction (!sharp) k) f 0
  have he (t : ℝ) : sourcePair k (SourceGaugeScaleTransport.coreFlow t (fullAction sharp f))=
      sourcePair (fullAction (!sharp) k) (SourceGaugeScaleTransport.coreFlow t f) := by
    rw [full_gauge_flow,full_pair]
  have hd := (hL.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => (he t).symm))).unique hR
  simp only [SourceGaugeScaleTransport.coreFlow_zero] at hd
  rw [←full_pair sharp k (SourceGaugeScaleTransport.generator f)] at hd
  change sourcePair k (SourceGaugeScaleTransport.generator (fullAction sharp f)-
    fullAction sharp (SourceGaugeScaleTransport.generator f))=sourcePair k 0
  simp only [sourcePair,map_sub,map_zero,inner_sub_right,inner_zero_right] at hd ⊢
  exact sub_eq_zero.mpr hd

private theorem full_dilation_native : Commute dilation (fullAction false) := by
  have hE : Commute eulerAction (fullAction false) :=
    euler_invariant_multiplier (fun z => sourceMap (scalarField z))
      (fun _ => (sourceMap.contDiff.comp scalarField_smooth).contDiffAt) (fun _ _ => rfl)
  have hN : Commute number (fullAction false) := by
    apply number_multiplier (fun z => sourceMap (scalarField z))
      (fun _ => (sourceMap.contDiff.comp scalarField_smooth).contDiffAt)
    intro z
    rw [source_map_return]
    exact number_commute _
  apply sub_eq_zero.mp
  have he : eulerAction*fullAction false-fullAction false*eulerAction=
      (0 : ℂ) • fullAction false := by rw [hE.eq,sub_self,zero_smul]
  rw [dilation_operator]
  simpa only [mul_zero,zero_smul,Module.End.one_eq_id] using! affine_dilation _ _ _ 0 he hN

private theorem full_dilation (sharp : Bool) : Commute dilation (fullAction sharp) := by
  cases sharp
  · exact full_dilation_native
  · apply LinearMap.ext
    intro g
    apply SourceCoframeVolume.pair_ext
    intro f
    change sourcePair f (dilation (fullAction true g))=sourcePair f (fullAction true (dilation g))
    rw [dilation_pair,full_pair,full_pair]
    simp only [Bool.not_true]
    have h := LinearMap.congr_fun full_dilation_native.eq f
    change dilation (fullAction false f)=fullAction false (dilation f) at h
    rw [←h,←dilation_pair]

theorem original_full_coframe_jet (sharp : Bool) : scaleDerivative (fullAction sharp)=0 := by
  change (3*Complex.I/2) • (dilation*fullAction sharp-fullAction sharp*dilation)=0
  rw [(full_dilation sharp).eq,sub_self,smul_zero]

/-- This source coefficient is read from all three original fields, on both full branches. -/
theorem original_full_inverse_jet (sharp : Bool) :
    InverseVolumeWardAlgebra.inverseWard deltaPhi deltaGauge scaleDerivative
      (vacuumJetCoefficient : ℂ) (fullAction sharp)=(4 : ℂ) • fullAction sharp :=
  InverseVolumeInsertionAlgebra.weight_one deltaPhi deltaGauge scaleDerivative
    (vacuumJetCoefficient : ℂ) (fullAction sharp)
    (original_full_affine_jet sharp) (original_full_gauge_jet sharp)
    (original_full_coframe_jet sharp)

end LowEnergy.SourceScalarInverseInsertion
