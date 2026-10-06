import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCoframeScaleTransport
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceJointScaleBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceCoframeScaleAction
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent
open SourceCoframeScaleTransport SourceKineticScale SourceDilationRemainder SourceJointScaleBudget
open GaussNativeForm GaussCoframeForm GaussNativeEnergy GaussMatterCore
open scoped ContDiff Distributions Topology InnerProductSpace

private theorem flow_inverse (t : ℝ) : coreFlow t*coreFlow (-t)=1 := by
  apply LinearMap.ext
  intro f
  change coreFlow t (coreFlow (-t) f)=f
  rw [coreFlow_add,add_neg_cancel,coreFlow_zero]

def conjugation (t : ℝ) : CoreEnd →ₐ[ℂ] CoreEnd where
  toFun A := coreFlow t*A*coreFlow (-t)
  map_zero' := by simp
  map_add' A B := by simp only [mul_add,add_mul]
  map_one' := by simpa using flow_inverse t
  map_mul' A B := by
    have hi := flow_inverse (-t)
    rw [neg_neg] at hi
    calc
      _ = coreFlow t*A*(coreFlow (-t)*coreFlow t)*B*coreFlow (-t) := by
        rw [hi]; noncomm_ring
      _ = _ := by noncomm_ring
  commutes' c := by
    change coreFlow t*(c • (1 : CoreEnd))*coreFlow (-t)=c • (1 : CoreEnd)
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,flow_inverse]

theorem conjugation_apply (t : ℝ) (A : CoreEnd) (f : QuantumTest) :
    conjugation t A f=coreFlow t (A (coreFlow (-t) f)) := rfl

private theorem conjugation_smul (t : ℝ) (c : ℂ) (A : CoreEnd) :
    conjugation t (c • A)=c • conjugation t A := by
  change coreFlow t*(c • A)*coreFlow (-t)=c • (coreFlow t*A*coreFlow (-t))
  rw [mul_smul_comm,smul_mul_assoc]

private theorem flow_value (t : ℝ) (f : QuantumTest) :
    (coreFlow t f : SourceCoordinateSlice → FockFiber)=
      (fiberAmplitude t).toContinuousLinearMap ∘ f ∘ scaleEquiv t := rfl

private theorem flow_fderiv (t : ℝ) (f : QuantumTest) (z v : SourceCoordinateSlice) :
    fderiv ℝ (coreFlow t f) z v =
      fiberAmplitude t (fderiv ℝ f (scaleEquiv t z) (scaleEquiv t v)) := by
  let C := (fiberAmplitude t).toContinuousLinearMap.restrictScalars ℝ
  have h := C.hasFDerivAt.comp z
    (((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
      (x := scaleEquiv t z)).comp z (scaleEquiv t).hasFDerivAt)
  rw [flow_value]
  change fderiv ℝ (C ∘ f ∘ scaleEquiv t) z v=_
  rw [h.fderiv]
  rfl

private theorem flow_derivative (t : ℝ) (v : SourceCoordinateSlice) (f : QuantumTest) :
    GaussCoframeCore.derivative v (coreFlow t f)=
      coreFlow t (GaussCoframeCore.derivative (scaleEquiv t v) f) := by
  apply DFunLike.ext
  intro z
  rw [GaussCoframeCore.derivative_apply,flow_fderiv]
  change _=fiberAmplitude t (GaussCoframeCore.derivative (scaleEquiv t v) f (scaleEquiv t z))
  rw [GaussCoframeCore.derivative_apply]

private theorem rate_neg (t : ℝ) : rate (-t)=(rate t)⁻¹ := by
  simp [rate,Real.exp_neg]

theorem coframe_momentum_conjugation (t : ℝ) (i : Fin 6) :
    conjugation t (GaussCoframeCore.momentum i)=
      Complex.ofReal ((rate t)⁻¹) • GaussCoframeCore.momentum i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change coreFlow t ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)
    (coreFlow (-t) f)) z=_
  rw [map_smul,flow_derivative]
  have hv : scaleEquiv (-t) (GaussCoframeCore.coframeDirection i)=
      (rate t)⁻¹ • GaussCoframeCore.coframeDirection i := by
    simp [scaleEquiv_apply,scale,GaussCoframeCore.coframeDirection,rate_neg]
  rw [hv]
  change _=(Complex.ofReal ((rate t)⁻¹) • GaussCoframeCore.momentum i f) z
  have hd : GaussCoframeCore.derivative ((rate t)⁻¹ • GaussCoframeCore.coframeDirection i) f=
      Complex.ofReal ((rate t)⁻¹) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f := by
    apply DFunLike.ext
    intro w
    rw [smul_apply,GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply]
    change fderiv ℝ f w ((rate t)⁻¹ • GaussCoframeCore.coframeDirection i)=
      Complex.ofReal ((rate t)⁻¹) • (fderiv ℝ f w (GaussCoframeCore.coframeDirection i))
    rw [map_smul]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [hd,map_smul,map_smul,coreFlow_add,add_neg_cancel,coreFlow_zero]
  simp only [GaussCoframeCore.momentum,LinearMap.smul_apply,smul_apply,smul_smul,Complex.ofReal_inv,mul_comm]

private theorem pair_flow_right (t : ℝ) (f g : QuantumTest) :
    sourcePair f (coreFlow t g)=sourcePair (coreFlow (-t) f) g := by
  have h := coreFlow_pair t (coreFlow (-t) f) g
  rw [coreFlow_add,add_neg_cancel,coreFlow_zero] at h
  exact h

private theorem pair_flow_left (t : ℝ) (f g : QuantumTest) :
    sourcePair (coreFlow t f) g=sourcePair f (coreFlow (-t) g) := by
  have h := coreFlow_pair t f (coreFlow (-t) g)
  rw [coreFlow_add,add_neg_cancel,coreFlow_zero] at h
  exact h

private theorem adjoint_conjugation (t : ℝ) (A B : CoreEnd) (a : ℝ)
    (pair : ∀ f g, sourcePair f (B g)=sourcePair (A f) g)
    (action : conjugation t A=(a : ℂ) • A) : conjugation t B=(a : ℂ) • B := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  rw [conjugation_apply,pair_flow_right,pair,←pair_flow_left]
  change sourcePair (conjugation t A f) g=sourcePair f ((a : ℂ) • B g)
  rw [action]
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  exact congrArg ((a : ℂ)*·) (pair f g).symm

theorem coframe_adjoint_conjugation (t : ℝ) (i : Fin 6) :
    conjugation t (GaussCoframeCore.adjoint i)=
      Complex.ofReal ((rate t)⁻¹) • GaussCoframeCore.adjoint i := by
  apply adjoint_conjugation t (GaussCoframeCore.momentum i) _ ((rate t)⁻¹)
    (GaussCoframeKinetic.adjoint_pair i)
  exact coframe_momentum_conjugation t i

private theorem multiply_conjugation (t : ℝ) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (a : ℝ)
    (law : ∀ z, c (scale (rate t) z)=a*c z) :
    conjugation t (multiply c smooth)=(a : ℂ) • multiply c smooth := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have hz : scale (rate (-t)) (scale (rate t) z)=z := by
    rw [scale_add,neg_add_cancel]
    simp [rate,scale]
  simp only [conjugation_apply,coreFlow_apply,multiply_apply,smul_apply,PiLp.smul_apply,LinearMap.smul_apply,smul_eq_mul]
  change (Real.exp ((word.card+4 : ℝ)*t) : ℂ)*(((c (scale (rate t) z) : ℝ) : ℂ)*
      ((Real.exp ((word.card+4 : ℝ)*(-t)) : ℂ)*f (scale (rate (-t)) (scale (rate t) z)) word))=
    (a : ℂ)*((c z : ℂ)*f z word)
  rw [hz,law]
  have he : (Real.exp ((word.card+4 : ℝ)*t) : ℂ)*
      (Real.exp ((word.card+4 : ℝ)*(-t)) : ℂ)=1 := by
    rw [←Complex.ofReal_mul,←Real.exp_add]
    simp
  rw [Complex.ofReal_mul]
  linear_combination (a : ℂ)*(c z : ℂ)*f z word*he

theorem local_conjugation (t : ℝ) :
    conjugation t localAction=((rate t^3 : ℝ) : ℂ) • localAction :=
  multiply_conjugation t localPotential local_smooth ((rate t)^3) (local_scale (rate t))

theorem spatial_conjugation (t : ℝ) :
    conjugation t spatialAction=(rate t : ℂ) • spatialAction :=
  multiply_conjugation t spatialPotential spatial_smooth (rate t)
    (spatial_scale (rate t) (Real.exp_ne_zero _))

private theorem native_momentum_intertwine (t : ℝ) (v : GaussLiveMomentum.Ambient)
    (f : QuantumTest) : coreFlow t (covariantMomentum v f)=covariantMomentum v (coreFlow t f) := by
  apply DFunLike.ext
  intro z
  have hs : scaleEquiv t (0,(GaussLiveMomentum.inverseL z v).2)=
      (0,(GaussLiveMomentum.inverseL z v).2) := by simp [scaleEquiv_apply,scale]
  have hc := congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f (scaleEquiv t z)))
    (GaussFockWeights.native_weight_commute (fun N => (Real.exp ((N+4 : ℝ)*t) : ℂ))
      (GaussLiveMomentum.inverseL z v).1).eq
  change fiberAmplitude t (GaussNativeMatter.nativeFock (GaussLiveMomentum.inverseL z v).1
      (f (scaleEquiv t z)))=
    GaussNativeMatter.nativeFock (GaussLiveMomentum.inverseL z v).1
      (fiberAmplitude t (f (scaleEquiv t z))) at hc
  change fiberAmplitude t (covariantMomentum v f (scaleEquiv t z))=covariantMomentum v (coreFlow t f) z
  rw [covariantMomentum_apply,covariantMomentum_apply,flow_fderiv,hs]
  rw [scaleEquiv_apply] at hc
  rw [scaleEquiv_apply,inverse_coframe_scale,map_smul,map_add,hc]
  rfl

theorem native_momentum_conjugation (t : ℝ) (v : GaussLiveMomentum.Ambient) :
    conjugation t (covariantMomentum v)=covariantMomentum v := by
  apply LinearMap.ext
  intro f
  rw [conjugation_apply,native_momentum_intertwine,coreFlow_add,add_neg_cancel,coreFlow_zero]

theorem native_adjoint_conjugation (t : ℝ) (v : GaussLiveMomentum.Ambient) :
    conjugation t (GaussMomentumAdjoint.adjoint v)=GaussMomentumAdjoint.adjoint v := by
  have h := adjoint_conjugation t (covariantMomentum v) (GaussMomentumAdjoint.adjoint v) 1
    (GaussNativeForm.adjoint_pair v) (by simpa using native_momentum_conjugation t v)
  simpa using h

private theorem quantum_conjugation (t : ℝ) (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val)
    (a : ℝ) (law : ∀ z, A (scale (rate t) z)=(a : ℂ) • A z) :
    conjugation t (GaussQuantumMultiplier.action A smooth)=
      (a : ℂ) • GaussQuantumMultiplier.action A smooth := by
  apply LinearMap.ext
  intro f
  have hi := coreFlow_add t (-t) f
  rw [add_neg_cancel,coreFlow_zero] at hi
  apply DFunLike.ext
  intro z
  have hc := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T ((coreFlow (-t) f) (scale (rate t) z)))
    (GaussQuantumMultiplier.weight_commute (fun N => (Real.exp ((N+4 : ℝ)*t) : ℂ)) (A z)).eq
  change fiberAmplitude t (GaussQuantumMultiplier.quantized (A z)
      ((coreFlow (-t) f) (scale (rate t) z)))=
    GaussQuantumMultiplier.quantized (A z)
      (fiberAmplitude t ((coreFlow (-t) f) (scale (rate t) z))) at hc
  change fiberAmplitude t (GaussQuantumMultiplier.quantized (A (scale (rate t) z))
    ((coreFlow (-t) f) (scale (rate t) z)))=
    (a : ℂ) • GaussQuantumMultiplier.quantized (A z) (f z)
  rw [law]
  change fiberAmplitude t ((GaussQuantumMultiplier.quantizer ((a : ℂ) • A z))
    ((coreFlow (-t) f) (scale (rate t) z)))=_
  rw [map_smul]
  change fiberAmplitude t ((a : ℂ) • (GaussQuantumMultiplier.quantized (A z)
    ((coreFlow (-t) f) (scale (rate t) z))))=_
  rw [map_smul,hc]
  change (a : ℂ) • GaussQuantumMultiplier.quantized (A z) (coreFlow t (coreFlow (-t) f) z)=_
  rw [hi]

theorem spin_conjugation (t : ℝ) (a : Fin 7) :
    conjugation t (GaussCoframeSpin.current a)=GaussCoframeSpin.current a := by
  simpa only [GaussCoframeSpin.current,Complex.ofReal_one,one_smul] using! quantum_conjugation t
    (fun _ => GaussCoframeSpin.full a) (fun _ => contDiffAt_const) 1 (by simp)

theorem number_conjugation (t : ℝ) : conjugation t number=number := by
  have h (f : QuantumTest) : coreFlow t (number f)=number (coreFlow t f) := by
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    rw [coreFlow_apply,number_apply,number_apply,coreFlow_apply]
    ring
  apply LinearMap.ext
  intro f
  rw [conjugation_apply,h,coreFlow_add,add_neg_cancel,coreFlow_zero]

private theorem sandwich_conjugation (t : ℝ) (v w : GaussLiveMomentum.Ambient)
    (c : SourceCoordinateSlice → ℝ) (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (a : ℝ) (law : ∀ z, c (scale (rate t) z)=a*c z) :
    conjugation t (sandwich v w c smooth)=(a : ℂ) • sandwich v w c smooth := by
  change conjugation t ((GaussMomentumAdjoint.adjoint v)*(multiply c smooth)*(covariantMomentum w))=_
  rw [map_mul,map_mul,native_adjoint_conjugation,native_momentum_conjugation,
    multiply_conjugation t c smooth a law,mul_smul_comm,smul_mul_assoc]
  rfl

theorem scalar_kinetic_conjugation (t : ℝ) :
    conjugation t scalarKinetic=Complex.ofReal ((rate t)⁻¹^3) • scalarKinetic := by
  have h (a : ScalarIndex) := sandwich_conjugation t (scalarDirection a) (scalarDirection a)
    scalarWeight scalarWeight_smooth ((rate t)⁻¹^3) (scalar_weight_scale (rate t))
  simp only [scalarKinetic,conjugation_smul,map_sum,h,←Finset.smul_sum,smul_smul]
  congr 1
  ring

theorem gauge_kinetic_conjugation (t : ℝ) :
    conjugation t gaugeKinetic=(rate t : ℂ) • gaugeKinetic := by
  have h (a : LieIndex) (i j : Fin 3) := sandwich_conjugation t (gaugeDirection i a)
    (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (rate t)
    (fun z => gauge_weight_scale (rate t) (Real.exp_ne_zero _) z i j)
  simp only [gaugeKinetic,conjugation_smul,map_sum,h,←Finset.smul_sum,smul_smul]
  congr 1
  ring

theorem coframe_term_conjugation (t : ℝ) (i j : Fin 6) :
    conjugation t (GaussCoframeKinetic.term i j)=
      Complex.ofReal ((rate t)⁻¹^3) • GaussCoframeKinetic.term i j := by
  change conjugation t (GaussCoframeCore.adjoint i *
    (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)) *
      GaussCoframeCore.momentum j)=_
  rw [map_mul,map_mul,coframe_adjoint_conjugation,coframe_momentum_conjugation,
    multiply_conjugation t _ _ ((rate t)⁻¹)
      (fun z => coframe_coefficient_scale (rate t) (Real.exp_ne_zero _) z i j)]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [Complex.ofReal_pow]
  congr 1
  ring

theorem coframe_kinetic_conjugation (t : ℝ) :
    conjugation t GaussCoframeKinetic.kinetic=
      Complex.ofReal ((rate t)⁻¹^3) • GaussCoframeKinetic.kinetic := by
  simp only [GaussCoframeKinetic.kinetic,map_sum,coframe_term_conjugation,←Finset.smul_sum]

private theorem mixed_conjugation (t : ℝ) (i : Fin 6) (a : Fin 7)
    (c : SourceCoordinateSlice → ℝ) (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (law : ∀ z, c (scale (rate t) z)=(rate t)⁻¹^2*c z) :
    conjugation t (mixed i a c smooth)=Complex.ofReal ((rate t)⁻¹^3) • mixed i a c smooth := by
  change conjugation t ((1/2 : ℂ) • (GaussCoframeSpin.current a * multiply c smooth *
    GaussCoframeCore.momentum i + GaussCoframeCore.adjoint i * multiply c smooth *
      GaussCoframeSpin.current a))=_
  rw [conjugation_smul,map_add,map_mul,map_mul,map_mul,map_mul,spin_conjugation,
    coframe_momentum_conjugation,coframe_adjoint_conjugation,multiply_conjugation t c smooth _ law]
  simp only [mixed,smul_mul_assoc,mul_smul_comm,smul_smul,Complex.ofReal_pow]
  module

theorem coframe_current_conjugation (t : ℝ) :
    conjugation t currentAction=Complex.ofReal ((rate t)⁻¹^3) • currentAction := by
  have hp (j : Fin 6) (z : SourceCoordinateSlice) :=
    current_coefficient_scale (rate t) (Real.exp_ne_zero _) z j
  have hn (z : SourceCoordinateSlice) : -currentCoefficient 0 (scale (rate t) z)=
      (rate t)⁻¹^2*(-currentCoefficient 0 z) := by rw [hp]; ring
  simp only [currentAction,map_add,mixed_conjugation t _ _ _ _ (hp _),
    mixed_conjugation t 3 4 (fun z => -currentCoefficient 0 z)
      (fun z => (currentCoefficient_smooth 0 z).neg) hn,smul_add]

theorem spin_square_conjugation (t : ℝ) (a : Fin 7) :
    conjugation t (spinSquare a)=Complex.ofReal ((rate t)⁻¹^3) • spinSquare a := by
  change conjugation t ((spinWeight a : ℂ) • (GaussCoframeSpin.current a *
    multiply inverseVolume inverseVolume_smooth * GaussCoframeSpin.current a))=_
  rw [conjugation_smul,map_mul,map_mul,spin_conjugation,
    multiply_conjugation t _ _ _ (inverse_volume_scale (rate t))]
  simp only [spinSquare,smul_mul_assoc,mul_smul_comm,smul_smul]
  congr 1
  ring

theorem number_shift_conjugation (t : ℝ) :
    conjugation t numberShift=Complex.ofReal ((rate t)⁻¹^3) • numberShift := by
  have hc (z : SourceCoordinateSlice) : numberCoefficient (scale (rate t) z)=
      (rate t)⁻¹^3*numberCoefficient z := by
    unfold numberCoefficient
    rw [inverse_volume_scale]
    ring
  change conjugation t ((1/2 : ℂ) • (number*multiply numberCoefficient numberCoefficient_smooth+
    multiply numberCoefficient numberCoefficient_smooth*number))=_
  rw [conjugation_smul,map_add,map_mul,map_mul,number_conjugation,multiply_conjugation t _ _ _ hc]
  simp only [numberShift,smul_mul_assoc,mul_smul_comm,smul_smul]
  module

theorem matter_conjugation (t : ℝ) :
    conjugation t matterAction=Complex.ofReal ((rate t)⁻¹) • matterAction := by
  have hl (i b : Fin 3) (z : SourceCoordinateSlice) :
      localMatrix i b (scale (rate t) z)=Complex.ofReal ((rate t)⁻¹) • localMatrix i b z := by
    unfold localMatrix coefficient
    rw [triad_inverse_scale]
    change ((2*sourceTime 0*((rate t)⁻¹*triadInverse z.1 i b) : ℝ) : ℂ) •
      matrixTerm b (GaussNativePotential.connectionField z i)=_
    rw [smul_smul]
    congr 1
    push_cast
    ring
  simp only [matterAction,map_sum,quantum_conjugation t _ _ _ (hl _ _),←Finset.smul_sum]

theorem kinetic_conjugation (t : ℝ) :
    conjugation t SourceKineticTranspose.kineticAction=
      Complex.ofReal ((rate t)⁻¹^3) • (SourceKineticTranspose.kineticAction-gaugeKinetic)+
        (rate t : ℂ) • gaugeKinetic := by
  have hk : SourceKineticTranspose.kineticAction=scalarKinetic+gaugeKinetic+
      GaussCoframeKinetic.kinetic+currentAction+(∑ a : Fin 7,spinSquare a)+numberShift := by
    unfold SourceKineticTranspose.kineticAction coframeAction
    abel
  rw [hk]
  simp only [map_add,map_sum,scalar_kinetic_conjugation,gauge_kinetic_conjugation,
    coframe_kinetic_conjugation,coframe_current_conjugation,spin_square_conjugation,
    number_shift_conjugation,←Finset.smul_sum]
  module

theorem original_hamiltonian_conjugation (t : ℝ) :
    conjugation t GaussDiagonalHistory.diagonalAction=sourceScale (rate t) := by
  rw [original_action_split]
  simp only [map_add,kinetic_conjugation,matter_conjugation,local_conjugation,spatial_conjugation]
  change _=Complex.ofReal ((rate t)⁻¹^3) • (SourceKineticTranspose.kineticAction-gaugeKinetic)+
    (rate t : ℂ) • (gaugeKinetic+spatialAction)+Complex.ofReal ((rate t)⁻¹) • matterAction+
      Complex.ofReal ((rate t)^3) • localAction
  module

theorem original_hamiltonian_core_return (t : ℝ) (f : QuantumTest) :
    coreFlow t (GaussDiagonalHistory.diagonalAction (coreFlow (-t) f))=sourceScale (rate t) f :=
  LinearMap.congr_fun (original_hamiltonian_conjugation t) f

theorem original_hamiltonian_hilbert_return (t : ℝ) (f : QuantumTest) :
    hilbertFlow t (GaussDiagonalHistory.diagonal (coreEquiv (coreFlow (-t) f)))=
      embed (sourceScale (rate t) f) := by
  change hilbertFlow t (embed (GaussDiagonalHistory.diagonalAction
    (coreEquiv.symm (coreEquiv (coreFlow (-t) f)))))=_
  rw [coreEquiv.symm_apply_apply,hilbertFlow_on_core,original_hamiltonian_core_return]

end LowEnergy.SourceCoframeScaleAction
