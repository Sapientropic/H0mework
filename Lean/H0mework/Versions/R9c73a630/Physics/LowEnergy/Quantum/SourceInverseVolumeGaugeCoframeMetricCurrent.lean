import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeCoframeCompatibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceGaugeCoframeMetricCurrent
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open GaussScalarTransport GaussDensityCore SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceNativeMomentumCurvature SourceNativeDensityTrace
open SourceDoubleGramCurvatureForm SourceNativeMatterCovarianceCancellation SourceUnmixedPotentialCancellation
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceDilationRemainder SourceScalarOscillatorAbsorption SourceInverseNoetherEnergy
open SourceScalarPositiveBulkWard SourceEulerCore
open SourceNativeCoframeCompatibility
open scoped ContDiff Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

private theorem paired_commute (A B C : End)
    (hA : ∀ f g,sourcePair f (A g)=sourcePair (A f) g)
    (hC : ∀ f g,sourcePair f (C g)=sourcePair (B f) g) (h : Commute A B) : Commute A C := by
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  change sourcePair f (A (C g))=sourcePair f (C (A g))
  calc
    _=sourcePair (A f) (C g) := hA _ _
    _=sourcePair (B (A f)) g := hC _ _
    _=sourcePair (A (B f)) g := congrArg (fun x => sourcePair x g) (LinearMap.congr_fun h.eq f).symm
    _=sourcePair (B f) (A g) := (hA _ _).symm
    _=_ := (hC _ _).symm

private theorem native_coframe_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : ∀ z s,c (z.1,s)=c z)
    (v : Ambient) : Commute (multiply c hc) (covariantMomentum v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hd : fderiv ℝ c z (direction v z)=0 := by
      have hg : HasDerivAt (fun t : ℝ => z+t • direction v z) (direction v z) 0 := by
        simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z)).const_add z
      have he (t : ℝ) : c (z+t • direction v z)=c z := by
        change c (z.1+t • (0 : Coframe),z.2+t • (inverseL z v).2)=c z
        rw [smul_zero,add_zero,hi]
      have dh := ((hc ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt
        |>.comp_hasDerivAt_of_eq 0 hg (by simp)
      apply dh.unique
      change HasDerivAt (fun t : ℝ => c (z+t • direction v z)) 0 0
      rw [show (fun t : ℝ => c (z+t • direction v z))=(fun _ : ℝ => c z) from funext he]
      exact hasDerivAt_const (0 : ℝ) (c z)
    have hf : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    have hD : directional v (multiply c hc f) z=(c z : ℂ) • directional v f z := by
      rw [directional_apply,hf,fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change c z • fderiv ℝ f z (direction v z)+fderiv ℝ c z (direction v z) • f z=_
      rw [hd,zero_smul,add_zero]
      apply PiLp.ext
      intro word
      exact Complex.real_smul
    change (c z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))=
      (-Complex.I) • (directional v (multiply c hc f) z+connection v z ((c z : ℂ) • f z))
    rw [hD,map_smul,←smul_add,smul_comm]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

open GaussNativeMatter GaussQuantumMultiplier
open SaturationMonoid.PhysicsCore
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

private theorem full_spin_native (a : Fin 7) (b : NativeLie) : Commute (GaussCoframeSpin.full a) (nativeFull b) := by
  have hp := GaussMatterCore.spin_native_commute (GaussCoframeSpin.sourceSpin a) b
  change GaussCoframeSpin.primal a*nativePrimal b=nativePrimal b*GaussCoframeSpin.primal a at hp
  have hd := congrArg (fun M : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ => M.map (starRingEnd ℂ)) hp
  rw [Matrix.map_mul,Matrix.map_mul] at hd
  change Matrix.fromBlocks (GaussCoframeSpin.primal a) 0 0
    (if a.val<3 then (GaussCoframeSpin.primal a).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal a).map (starRingEnd ℂ))*
    Matrix.fromBlocks (nativePrimal b) 0 0 ((nativePrimal b).map (starRingEnd ℂ))=_
  change _=Matrix.fromBlocks (nativePrimal b) 0 0 ((nativePrimal b).map (starRingEnd ℂ))*
    Matrix.fromBlocks (GaussCoframeSpin.primal a) 0 0
      (if a.val<3 then (GaussCoframeSpin.primal a).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal a).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero]
  apply congrArg₂ (fun A B : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ => Matrix.fromBlocks A 0 0 B) hp
  split_ifs <;> simp only [Matrix.neg_mul,Matrix.mul_neg,hd]

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem spin_fiber_native (a : Fin 7) (b : NativeLie) :
    Commute (quantized (GaussCoframeSpin.full a)) (nativeFock b) := by
  apply sub_eq_zero.mp
  change quantized (GaussCoframeSpin.full a)*quantized (nativeFull b)-
    quantized (nativeFull b)*quantized (GaussCoframeSpin.full a)=0
  rw [quantized_bracket,(full_spin_native a b).eq,sub_self]
  exact map_zero quantizer

private theorem spin_directional (a : Fin 7) (v : Ambient) : Commute (GaussCoframeSpin.current a) (directional v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let T := (quantized (GaussCoframeSpin.full a)).restrictScalars ℝ
  have hf : (GaussCoframeSpin.current a f : SourceCoordinateSlice → FockFiber)=T ∘ f := rfl
  have hd := T.hasFDerivAt.comp z (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change quantized (GaussCoframeSpin.full a) (directional v f z)=directional v (GaussCoframeSpin.current a f) z
  rw [directional_apply,directional_apply,hf,hd.fderiv]
  rfl

private theorem spin_momentum (a : Fin 7) (v : Ambient) : Commute (GaussCoframeSpin.current a) (covariantMomentum v) := by
  have hc : Commute (GaussCoframeSpin.current a) (localMultiplier (connection v) (connection_smooth v)) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z)) (spin_fiber_native a (inverseL z v).1).eq
  unfold covariantMomentum
  exact ((spin_directional a v).add_right hc).smul_right _

private theorem native_coframe_momentum (v : Ambient) (i : Fin 6) :
    Commute (covariantMomentum v) (GaussCoframeCore.momentum i) := by
  unfold GaussCoframeCore.momentum
  exact (original_native_coframe_derivative v i).symm.smul_right _

private theorem native_coframe_adjoint (v : Ambient) (i : Fin 6) :
    Commute (covariantMomentum v) (GaussCoframeCore.adjoint i) := by
  have hd : Commute (GaussMomentumAdjoint.adjoint v) (GaussCoframeCore.momentum i) := by
    unfold GaussCoframeCore.momentum
    exact (original_native_adjoint_coframe_derivative v i).symm.smul_right _
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  change sourcePair f (covariantMomentum v (GaussCoframeCore.adjoint i g))=
    sourcePair f (GaussCoframeCore.adjoint i (covariantMomentum v g))
  calc
    _=sourcePair (GaussMomentumAdjoint.adjoint v f) (GaussCoframeCore.adjoint i g) := GaussMomentumAdjoint.momentum_pair _ _ _
    _=sourcePair (GaussCoframeCore.momentum i (GaussMomentumAdjoint.adjoint v f)) g := GaussCoframeKinetic.adjoint_pair _ _ _
    _=sourcePair (GaussMomentumAdjoint.adjoint v (GaussCoframeCore.momentum i f)) g :=
      congrArg (fun x => sourcePair x g) (LinearMap.congr_fun hd.eq f).symm
    _=sourcePair (GaussCoframeCore.momentum i f) (covariantMomentum v g) := (GaussMomentumAdjoint.momentum_pair _ _ _).symm
    _=_ := (GaussCoframeKinetic.adjoint_pair _ _ _).symm

private theorem native_number (v : Ambient) : Commute (covariantMomentum v) GaussCoframeForm.number := by
  apply Commute.symm
  unfold covariantMomentum
  exact ((number_directional _).add_right (number_connection _)).smul_right _

private theorem native_coframe_kinetic (v : Ambient) : Commute (covariantMomentum v) GaussCoframeKinetic.kinetic := by
  unfold GaussCoframeKinetic.kinetic
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  change Commute (covariantMomentum v) (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j))
  exact (native_coframe_adjoint v i).mul_right
    ((native_coframe_coefficient _ _ (fun _ _ => rfl) v).symm.mul_right (native_coframe_momentum v j))

private theorem native_coframe_mixed (v : Ambient) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : ∀ z s,c (z.1,s)=c z) :
    Commute (covariantMomentum v) (GaussCoframeForm.mixed i a c hc) := by
  change Commute (covariantMomentum v) ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply c hc*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply c hc*GaussCoframeSpin.current a)))
  have hm := (native_coframe_coefficient c hc hi v).symm
  exact ((spin_momentum a v).symm.mul_right (hm.mul_right (native_coframe_momentum v i)) |>.add_right
    ((native_coframe_adjoint v i).mul_right (hm.mul_right (spin_momentum a v).symm))).smul_right _

/-- Every original native momentum is compatible with the complete coframe action. -/
theorem original_native_whole_coframe (v : Ambient) : Commute (covariantMomentum v) GaussCoframeForm.coframeAction := by
  have hm : Commute (covariantMomentum v) GaussCoframeForm.currentAction := by
    unfold GaussCoframeForm.currentAction
    exact (((native_coframe_mixed v _ _ _ _ (fun _ _ => rfl)).add_right
      (native_coframe_mixed v _ _ _ _ (fun _ _ => rfl))).add_right
      (native_coframe_mixed v _ _ _ _ (fun _ _ => rfl))).add_right
      (native_coframe_mixed v _ _ _ _ (fun _ _ => rfl))
  have hs (a : Fin 7) : Commute (covariantMomentum v) (GaussCoframeForm.spinSquare a) := by
    change Commute (covariantMomentum v) ((GaussCoframeForm.spinWeight a : ℂ) •
      (GaussCoframeSpin.current a*(multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
        GaussCoframeSpin.current a)))
    exact ((spin_momentum a v).symm.mul_right
      ((native_coframe_coefficient _ _ (fun _ _ => rfl) v).symm.mul_right (spin_momentum a v).symm)).smul_right _
  have hn : Commute (covariantMomentum v) GaussCoframeForm.numberShift := by
    change Commute (covariantMomentum v) ((1/2 : ℂ) •
      (GaussCoframeForm.number*multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
        multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number))
    have hc := (native_coframe_coefficient GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth
      (fun _ _ => rfl) v).symm
    exact (((native_number v).mul_right hc).add_right (hc.mul_right (native_number v))).smul_right _
  unfold GaussCoframeForm.coframeAction
  exact ((((native_coframe_kinetic v).add_right hm).add_right (Commute.sum_right _ _ _ (fun a _ => hs a))).add_right hn).add_right
    (native_coframe_coefficient _ _ (fun _ _ => rfl) v).symm

/-- Formal symmetry preserves the independent native transpose in the same coframe compatibility. -/
theorem original_native_adjoint_whole_coframe (v : Ambient) :
    Commute (GaussMomentumAdjoint.adjoint v) GaussCoframeForm.coframeAction :=
  (paired_commute _ _ _ GaussCoframeForm.coframeAction_pair (adjoint_pair v)
    (original_native_whole_coframe v).symm).symm

private theorem gradient_smooth (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => fderiv ℝ c x (GaussCoframeCore.coframeDirection i)) z.val :=
  ((hc z).fderiv_right (by simp)).clm_apply contDiffAt_const

private def gradientAction (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (i : Fin 6) : End :=
  multiply (fun x => fderiv ℝ c x (GaussCoframeCore.coframeDirection i)) (gradient_smooth c hc i)

private theorem coframe_multiply_current (i : Fin 6) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeCore.momentum i*multiply c hc-multiply c hc*GaussCoframeCore.momentum i=
      (-Complex.I) • gradientAction c hc i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have he : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (multiply c hc f) z-
      (c z : ℂ) • ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)=_
    rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,he,
      fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp)) (f.contDiff.differentiable (by simp)).differentiableAt]
    change (-Complex.I) • (c z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
      fderiv ℝ c z (GaussCoframeCore.coframeDirection i) • f z)-
      (c z : ℂ) • ((-Complex.I) • fderiv ℝ f z (GaussCoframeCore.coframeDirection i))=
        (-Complex.I) • ((fderiv ℝ c z (GaussCoframeCore.coframeDirection i) : ℂ) • f z)
    apply PiLp.ext
    intro word
    simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,Complex.real_smul]
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem coframe_adjoint_multiply_current (i : Fin 6) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeCore.adjoint i*multiply c hc-multiply c hc*GaussCoframeCore.adjoint i=
      (-Complex.I) • gradientAction c hc i := by
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  have h := congrArg (fun A : End => sourcePair (A f) g) (coframe_multiply_current i c hc)
  change sourcePair (GaussCoframeCore.momentum i (multiply c hc f)-multiply c hc (GaussCoframeCore.momentum i f)) g=
    sourcePair ((-Complex.I) • gradientAction c hc i f) g at h
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at h
  change sourcePair (GaussCoframeCore.momentum i (multiply c hc f)) g-
    sourcePair (multiply c hc (GaussCoframeCore.momentum i f)) g=Complex.I*sourcePair (gradientAction c hc i f) g at h
  change sourcePair f (GaussCoframeCore.adjoint i (multiply c hc g)-multiply c hc (GaussCoframeCore.adjoint i g))=
    sourcePair f ((-Complex.I) • gradientAction c hc i g)
  simp only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right]
  change sourcePair f (GaussCoframeCore.adjoint i (multiply c hc g))-
    sourcePair f (multiply c hc (GaussCoframeCore.adjoint i g))=(-Complex.I)*sourcePair f (gradientAction c hc i g)
  rw [GaussCoframeKinetic.adjoint_pair,multiply_pair,multiply_pair,GaussCoframeKinetic.adjoint_pair]
  have hg : sourcePair f (gradientAction c hc i g)=sourcePair (gradientAction c hc i f) g := multiply_pair _ _ _ _
  rw [hg]
  linear_combination -h

private theorem multiply_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem quantum_real (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ (fun x => quantized (A x)) z.val)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussQuantumMultiplier.action A hA) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (A z)) (c z : ℂ) (f z)

private theorem product_current {R : Type*} [Ring R] [Algebra ℂ R] (P W Q M CP CQ : R) (c : ℂ)
    (hP : P*M-M*P=c • CP) (hQ : Q*M-M*Q=c • CQ) (hW : Commute W M) :
    (P*(W*Q))*M-M*(P*(W*Q))=c • (P*(W*CQ)+CP*(W*Q)) := by
  calc
    _=P*(W*(Q*M-M*Q))+(P*M-M*P)*(W*Q) := by
      linear_combination (norm := noncomm_ring) P*hW.eq*Q
    _=_ := by rw [hP,hQ,mul_smul_comm,mul_smul_comm,smul_mul_assoc,smul_add]

private def kineticMetricCurrent (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : End :=
  (-Complex.I) • ∑ i : Fin 6,∑ j : Fin 6,
    (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*
      gradientAction c hc j)+gradientAction c hc i*
      (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j))

private theorem kinetic_metric_current (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeKinetic.kinetic*multiply c hc-multiply c hc*GaussCoframeKinetic.kinetic=kineticMetricCurrent c hc := by
  have h (i j : Fin 6) : GaussCoframeKinetic.term i j*multiply c hc-multiply c hc*GaussCoframeKinetic.term i j=
      (-Complex.I) • (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*
        gradientAction c hc j)+gradientAction c hc i*
        (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j)) :=
    product_current _ _ _ _ _ _ _ (coframe_adjoint_multiply_current i c hc) (coframe_multiply_current j c hc)
      (multiply_commute _ _ _ _)
  simp only [GaussCoframeKinetic.kinetic,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,h,←Finset.smul_sum,kineticMetricCurrent]

private def mixedMetricCurrent (i : Fin 6) (a : Fin 7) (d c : SourceCoordinateSlice → ℝ)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : End :=
  (-Complex.I/2 : ℂ) • (GaussCoframeSpin.current a*(multiply d hd*gradientAction c hc i)+
    gradientAction c hc i*(multiply d hd*GaussCoframeSpin.current a))

private theorem mixed_metric_current (i : Fin 6) (a : Fin 7) (d c : SourceCoordinateSlice → ℝ)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeForm.mixed i a d hd*multiply c hc-multiply c hc*GaussCoframeForm.mixed i a d hd=mixedMetricCurrent i a d c hd hc := by
  have hS : GaussCoframeSpin.current a*multiply c hc-multiply c hc*GaussCoframeSpin.current a=(-Complex.I) • (0 : End) := by
    have hs : Commute (GaussCoframeSpin.current a) (multiply c hc) :=
      quantum_real (fun _ => GaussCoframeSpin.full a) (fun _ => contDiffAt_const) c hc
    rw [hs.eq,sub_self,smul_zero]
  have h1 := product_current _ _ _ _ _ _ _ hS (coframe_multiply_current i c hc) (multiply_commute d c hd hc)
  have h2 := product_current _ _ _ _ _ _ _ (coframe_adjoint_multiply_current i c hc) hS (multiply_commute d c hd hc)
  change ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a)))*multiply c hc-
    multiply c hc*((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a)))=_
  simp only [smul_mul_assoc,mul_smul_comm,←smul_sub,add_mul,mul_add]
  rw [show (GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i))*multiply c hc+
      (GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a))*multiply c hc-
      (multiply c hc*(GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i))+
      multiply c hc*(GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a)))=
      ((GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i))*multiply c hc-
      multiply c hc*(GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i)))+
      ((GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a))*multiply c hc-
      multiply c hc*(GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a))) by abel,h1,h2]
  simp only [zero_mul,mul_zero,add_zero,zero_add,←smul_add,smul_smul,mixedMetricCurrent]
  congr 1
  ring

/-- Actual full coframe metric flow: the 6×6 kinetic divergence and all four original spin-current terms. -/
def gaugeMetricCurrent (i j : Fin 3) : End :=
  kineticMetricCurrent (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)+
  mixedMetricCurrent 1 5 (GaussCoframeForm.currentCoefficient 0) (fun z => gaugeWeight z i j)
    (GaussCoframeForm.currentCoefficient_smooth 0) (gaugeWeight_smooth i j)+
  mixedMetricCurrent 3 3 (GaussCoframeForm.currentCoefficient 1) (fun z => gaugeWeight z i j)
    (GaussCoframeForm.currentCoefficient_smooth 1) (gaugeWeight_smooth i j)+
  mixedMetricCurrent 3 4 (fun z => -GaussCoframeForm.currentCoefficient 0 z) (fun z => gaugeWeight z i j)
    (fun z => (GaussCoframeForm.currentCoefficient_smooth 0 z).neg) (gaugeWeight_smooth i j)+
  mixedMetricCurrent 4 3 (GaussCoframeForm.currentCoefficient 2) (fun z => gaugeWeight z i j)
    (GaussCoframeForm.currentCoefficient_smooth 2) (gaugeWeight_smooth i j)

/-- Every source coframe component contributes exactly its actual metric current. -/
theorem original_coframe_metric_current (i j : Fin 3) :
    GaussCoframeForm.coframeAction*multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)-
      multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*GaussCoframeForm.coframeAction=gaugeMetricCurrent i j := by
  let M := multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
  have hs (a : Fin 7) : Commute (GaussCoframeForm.spinSquare a) M := by
    change Commute ((GaussCoframeForm.spinWeight a : ℂ) • (GaussCoframeSpin.current a*
      (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*GaussCoframeSpin.current a))) M
    have hS : Commute (GaussCoframeSpin.current a) M := quantum_real _ _ _ _
    exact (hS.mul_left ((multiply_commute _ _ _ _).mul_left hS)).smul_left _
  have hn : Commute GaussCoframeForm.numberShift M := by
    change Commute ((1/2 : ℂ) • (GaussCoframeForm.number*
      multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
      multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number)) M
    have hN : Commute GaussCoframeForm.number M := quantum_real _ _ _ _
    have hC : Commute (multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth) M := multiply_commute _ _ _ _
    exact ((hN.mul_left hC).add_left (hC.mul_left hN)).smul_left _
  have hvol : Commute (multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth) M := multiply_commute _ _ _ _
  have hspin : Commute (∑ a : Fin 7,GaussCoframeForm.spinSquare a) M := Commute.sum_left _ _ _ (fun a _ => hs a)
  unfold GaussCoframeForm.coframeAction GaussCoframeForm.currentAction gaugeMetricCurrent
  simp only [add_mul,mul_add]
  have hk := kinetic_metric_current (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
  have h1 := mixed_metric_current 1 5 (GaussCoframeForm.currentCoefficient 0) (fun z => gaugeWeight z i j)
    (GaussCoframeForm.currentCoefficient_smooth 0) (gaugeWeight_smooth i j)
  have h2 := mixed_metric_current 3 3 (GaussCoframeForm.currentCoefficient 1) (fun z => gaugeWeight z i j)
    (GaussCoframeForm.currentCoefficient_smooth 1) (gaugeWeight_smooth i j)
  have h3 := mixed_metric_current 3 4 (fun z => -GaussCoframeForm.currentCoefficient 0 z) (fun z => gaugeWeight z i j)
    (fun z => (GaussCoframeForm.currentCoefficient_smooth 0 z).neg) (gaugeWeight_smooth i j)
  have h4 := mixed_metric_current 4 3 (GaussCoframeForm.currentCoefficient 2) (fun z => gaugeWeight z i j)
    (GaussCoframeForm.currentCoefficient_smooth 2) (gaugeWeight_smooth i j)
  linear_combination (norm := module) hk+h1+h2+h3+h4+hspin.eq+hn.eq+hvol.eq

/-- The complete gauge/coframe source current keeps both original gauge legs and every metric entry. -/
def gaugeCoframeDivergence : End := (1/2 : ℂ) • ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
  GaussMomentumAdjoint.adjoint (gaugeDirection i a)*(gaugeMetricCurrent i j*covariantMomentum (gaugeDirection j a))

/-- No native/coframe derivative commutator remains: only the generated source metric flow is sandwiched. -/
theorem original_gauge_coframe_current :
    GaussCoframeForm.coframeAction*gaugeKinetic-gaugeKinetic*GaussCoframeForm.coframeAction=gaugeCoframeDivergence := by
  have h (a : LieIndex) (i j : Fin 3) :
      GaussCoframeForm.coframeAction*sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)-
        sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*GaussCoframeForm.coframeAction=
      GaussMomentumAdjoint.adjoint (gaugeDirection i a)*(gaugeMetricCurrent i j*covariantMomentum (gaugeDirection j a)) := by
    rw [←original_coframe_metric_current]
    change GaussCoframeForm.coframeAction*(GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))-
      (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*(multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*
        covariantMomentum (gaugeDirection j a)))*GaussCoframeForm.coframeAction=_
    linear_combination (norm := noncomm_ring)
      -(original_native_adjoint_whole_coframe (gaugeDirection i a)).eq*
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j))*covariantMomentum (gaugeDirection j a)-
      GaussMomentumAdjoint.adjoint (gaugeDirection i a)*(multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j))*
        (original_native_whole_coframe (gaugeDirection j a)).eq
  simp only [gaugeKinetic,mul_smul_comm,smul_mul_assoc,←smul_sub,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib,h,gaugeCoframeDivergence]

/-- The six original lower-triangular coframe coordinate directions, including all shear directions. -/
def triadTangent (r : Fin 6) : Matrix (Fin 3) (Fin 3) ℝ := triad (EuclideanSpace.single r 1)

private def inverseTriadGradient (r : Fin 6) (z : SourceCoordinateSlice) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => fderiv ℝ (fun x : SourceCoordinateSlice => triadInverse x.1 i j) z (GaussCoframeCore.coframeDirection r)

private theorem coframe_line (z : SourceCoordinateSlice) (r : Fin 6) :
    HasDerivAt (fun t : ℝ => z+t • GaussCoframeCore.coframeDirection r) (GaussCoframeCore.coframeDirection r) 0 := by
  simpa only [one_smul,id_eq] using!
    ((hasDerivAt_id (0 : ℝ)).smul_const (GaussCoframeCore.coframeDirection r)).const_add z

private theorem triad_curve (z : SourceCoordinateSlice) (r : Fin 6) (t : ℝ) :
    triad (z+t • GaussCoframeCore.coframeDirection r).1=triad z.1+t • triadTangent r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triad,triadTangent,GaussCoframeCore.coframeDirection,PiLp.add_apply,PiLp.smul_apply]

private theorem triad_curve_derivative (z : SourceCoordinateSlice) (r : Fin 6) (i j : Fin 3) :
    HasDerivAt (fun t : ℝ => triad (z+t • GaussCoframeCore.coframeDirection r).1 i j) (triadTangent r i j) 0 := by
  simp only [triad_curve,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (triadTangent r i j)).const_add (triad z.1 i j)

private theorem inverse_curve_derivative (z : physicalChart) (r : Fin 6) (i j : Fin 3) :
    HasDerivAt (fun t : ℝ => triadInverse (z.val+t • GaussCoframeCore.coframeDirection r).1 i j)
      (inverseTriadGradient r z.val i j) 0 := by
  have h := ((triadInverse_smooth i j z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 (coframe_line z.val r) (by simp)
  exact h

private theorem inverse_triad_gradient (r : Fin 6) (z : physicalChart) :
    inverseTriadGradient r z.val= -(triadInverse z.val.1*triadTangent r*triadInverse z.val.1) := by
  have hne : ∀ᶠ t : ℝ in nhds 0,z.val+t • GaussCoframeCore.coframeDirection r ∈ physicalChart := by
    have ht := (coframe_line z.val r).continuousAt
    apply ht.eventually
    change (physicalChart : Set SourceCoordinateSlice) ∈ nhds (z.val+(0 : ℝ) • GaussCoframeCore.coframeDirection r)
    simpa only [zero_smul,add_zero] using physicalChart.isOpen.mem_nhds z.property
  have hmat : triad z.val.1*inverseTriadGradient r z.val+triadTangent r*triadInverse z.val.1=0 := by
    ext i j
    have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (triad_curve_derivative z.val r i k).mul (inverse_curve_derivative z r k j))
    have he : (fun t : ℝ => ∑ k : Fin 3,triad (z.val+t • GaussCoframeCore.coframeDirection r).1 i k*
        triadInverse (z.val+t • GaussCoframeCore.coframeDirection r).1 k j)=ᶠ[nhds 0] (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
      filter_upwards [hne] with t ht
      exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) (triad_inverse_right ⟨_,ht⟩)
    have hz := (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j))
    simpa only [zero_smul,add_zero,Matrix.add_apply,Matrix.mul_apply,Matrix.zero_apply,Finset.sum_add_distrib,add_comm] using hz
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => triadInverse z.val.1*M) hmat
  rw [Matrix.mul_add,←Matrix.mul_assoc,triad_inverse_left,Matrix.one_mul,Matrix.mul_zero] at h
  simpa only [Matrix.mul_assoc] using eq_neg_of_add_eq_zero_left h

private theorem spatial_metric_gradient (r : Fin 6) (z : physicalChart) :
    (fun i j : Fin 3 => fderiv ℝ (fun x => inverseSpatial x i j) z.val (GaussCoframeCore.coframeDirection r))=
      -(triadInverse z.val.1*triadTangent r*inverseSpatial z.val+
        inverseSpatial z.val*(triadTangent r).transpose*(triadInverse z.val.1).transpose) := by
  have he : (fun i j : Fin 3 => fderiv ℝ (fun x => inverseSpatial x i j) z.val (GaussCoframeCore.coframeDirection r))=
      inverseTriadGradient r z.val*(triadInverse z.val.1).transpose+
        triadInverse z.val.1*(inverseTriadGradient r z.val).transpose := by
    ext i j
    have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (inverse_curve_derivative z r i k).mul (inverse_curve_derivative z r j k))
    have hg := ((inverseSpatial_smooth i j z).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 (coframe_line z.val r) (by simp)
    change HasDerivAt (fun t : ℝ => ∑ k : Fin 3,
      triadInverse (z.val+t • GaussCoframeCore.coframeDirection r).1 i k*
      triadInverse (z.val+t • GaussCoframeCore.coframeDirection r).1 j k) _ 0 at hg
    have h := hg.unique hd
    simp only [zero_smul,add_zero,Finset.sum_add_distrib] at h
    simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
    rw [h]
  rw [he,inverse_triad_gradient]
  simp only [Matrix.neg_mul,Matrix.mul_neg,Matrix.transpose_neg,Matrix.transpose_mul,inverseSpatial]
  noncomm_ring

/-- The original gauge metric gradient, with volume and all lower-triangular shear terms explicit. -/
def metricGradient (r : Fin 6) (i j : Fin 3) (z : SourceCoordinateSlice) : ℝ :=
  (sourceSigma/sourceTime 0)*(volumeGradient z r*inverseSpatial z i j-
    volume z*((triadInverse z.1*triadTangent r*inverseSpatial z)+
      inverseSpatial z*(triadTangent r).transpose*(triadInverse z.1).transpose) i j)

/-- The actual triad inverse identity generates the full six-direction metric derivative. -/
theorem original_gauge_metric_gradient (r : Fin 6) (i j : Fin 3) (z : physicalChart) :
    fderiv ℝ (fun x => gaugeWeight x i j) z.val (GaussCoframeCore.coframeDirection r)=metricGradient r i j z.val := by
  have hU : fderiv ℝ volume z.val (GaussCoframeCore.coframeDirection r)=volumeGradient z.val r := by
    rw [volume_derivative]
    fin_cases r <;> simp [GaussCoframeCore.coframeDirection,volumeGradient,EuclideanSpace.single]
  have hv := volume_smooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt (x := z.val)
    |>.comp_hasDerivAt_of_eq 0 (coframe_line z.val r) (by simp)
  have hg := ((inverseSpatial_smooth i j z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 (coframe_line z.val r) (by simp)
  have hw := ((gaugeWeight_smooth i j z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 (coframe_line z.val r) (by simp)
  have hp := (hv.mul hg).const_mul (sourceSigma/sourceTime 0)
  have he : (fun t : ℝ => gaugeWeight (z.val+t • GaussCoframeCore.coframeDirection r) i j)=
      fun t => (sourceSigma/sourceTime 0)*(volume (z.val+t • GaussCoframeCore.coframeDirection r)*
        inverseSpatial (z.val+t • GaussCoframeCore.coframeDirection r) i j) := by
    funext t
    unfold gaugeWeight
    ring
  change HasDerivAt (fun t : ℝ => gaugeWeight (z.val+t • GaussCoframeCore.coframeDirection r) i j) _ 0 at hw
  rw [he] at hw
  have h := hw.unique hp
  simp only [zero_smul,add_zero,Function.comp_apply,hU] at h
  have hm := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) (spatial_metric_gradient r z)
  change fderiv ℝ (fun x => inverseSpatial x i j) z.val (GaussCoframeCore.coframeDirection r)=
    -((triadInverse z.val.1*triadTangent r*inverseSpatial z.val)+
      inverseSpatial z.val*(triadTangent r).transpose*(triadInverse z.val.1).transpose) i j at hm
  rw [hm] at h
  rw [h,metricGradient]
  ring

/-- The gradient multiplier in the full coframe metric current reads the explicit volume/shear source coefficient. -/
theorem original_metric_gradient_action (r : Fin 6) (i j : Fin 3) (f : QuantumTest) (z : physicalChart) :
    gradientAction (fun x => gaugeWeight x i j) (gaugeWeight_smooth i j) r f z.val=
      (metricGradient r i j z.val : ℂ) • f z.val := by
  change (fderiv ℝ (fun x => gaugeWeight x i j) z.val (GaussCoframeCore.coframeDirection r) : ℂ) • f z.val=_
  rw [original_gauge_metric_gradient]

private theorem gauge_coframe_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (hi : ∀ z s,c (z.1,s)=c z) :
    Commute gaugeKinetic (multiply c hc) := by
  unfold gaugeKinetic
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  have hp := native_coframe_coefficient c hc hi (gaugeDirection j a)
  have hq := paired_commute _ _ _ (multiply_pair c hc) (adjoint_pair (gaugeDirection i a))
    (native_coframe_coefficient c hc hi (gaugeDirection i a))
  change Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) (multiply c hc)
  exact hq.symm.mul_left ((multiply_commute _ _ _ _).mul_left hp.symm)

private theorem geometric_split : geometricAction=
    GaussCoframeForm.coframeAction-multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth+scalarSpatialAction := by
  unfold geometricAction GaussCoframeForm.coframeAction
  abel

/-- The full bulk now carries the explicit volume/shear metric flow instead of an opaque coframe/gauge current. -/
def metricReducedBulkCurrent : End :=
  (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
    inverseVolumeAction*(-(8 : ℂ) • (((localAction+scalarSpatialAction)*scalarKinetic-
      scalarKinetic*(localAction+scalarSpatialAction))+
      (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*scalarKinetic))+
      (36 : ℂ) • (((magneticAction+scalarSpatialAction)*gaugeKinetic-
        gaugeKinetic*(magneticAction+scalarSpatialAction))+gaugeCoframeDivergence)-
      (36 : ℂ) • gaugeMatterDivergence+
      (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction))

/-- The original complete bulk consumes every gauge/coframe metric entry and all mixed spin-gradient terms. -/
theorem original_bulk_current_metric_reduced : bulkCurrent=metricReducedBulkCurrent := by
  have hg : (magneticAction+geometricAction)*gaugeKinetic-gaugeKinetic*(magneticAction+geometricAction)=
      ((magneticAction+scalarSpatialAction)*gaugeKinetic-gaugeKinetic*(magneticAction+scalarSpatialAction))+gaugeCoframeDivergence := by
    rw [←original_gauge_coframe_current,geometric_split]
    have hv := (gauge_coframe_coefficient GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
      (fun _ _ => rfl)).eq
    simp only [add_mul,mul_add,sub_mul,mul_sub]
    rw [hv]
    module
  rw [original_bulk_current_native_coframe]
  unfold nativeCoframeBulkCurrent metricReducedBulkCurrent
  rw [hg]

/-- Same original F, raised state and full defect; the exact metric flow is consumed before any time or frequency estimate. -/
theorem original_remaining_raised_metric_reduced (F : Index) (A : End) (q : QuantumTest) :
    remainingRaisedCurrent F A q=(sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
      (sourcePair (A q) ((metricReducedBulkCurrent-scalarCurrent) (A q))).im/2 := by
  have h := original_current_split
  rw [original_bulk_current_metric_reduced] at h
  have hr : remainingCurrent=metricReducedBulkCurrent-scalarCurrent := by
    linear_combination (norm := module) -h
  rw [remainingRaisedCurrent,hr]

end LowEnergy.SourceGaugeCoframeMetricCurrent
