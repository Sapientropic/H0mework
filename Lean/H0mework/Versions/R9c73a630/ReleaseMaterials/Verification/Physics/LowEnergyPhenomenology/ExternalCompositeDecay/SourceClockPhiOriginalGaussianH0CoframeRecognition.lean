import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeDriftMomentumPrimitive
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0Recognition
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarVirialBulk
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCombinedScalePressure
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0CoframeRecognition
open SourcePhysicalKineticSquare GaussLiveMomentum
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeCovariantAction SourceCoframeCovariantSquare SourceCoframeSpinConnection
open SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarDoubleCurrent
open SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiOriginalGaussianH0Recognition
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev a:End:=inverseRootAction
private abbrev D:End:=combinedGenerator
private abbrev A:End:=combinedConjugate
private abbrev K:End:=covariantKinetic
private theorem combined_delta(T:End):bracket D T=deltaPhi T-deltaGauge T:=by
  unfold D combinedGenerator bracket
  rw [sub_mul,mul_sub]
  have hp:=SourceScalarAffineScaleTransport.generator_commutator T
  have hg:=SourceGaugeScaleTransport.generator_commutator T
  linear_combination (norm:=module) hp-hg
private theorem combined_connection(i:Fin 6):Commute D (connectionAction i):=by
  have h:=original_coframe_local_phi_gauge (connectionAction i)
    (fun q=>connectionFiber i (q,(0:Slice))) (fun _ _=>rfl)
  exact sub_eq_zero.mp (show bracket D _=0 by rw [combined_delta,h.1,h.2,sub_self])
private theorem combined_momentum(i:Fin 6):Commute D (SourceCoframeCovariantAction.covariantMomentum i):=by
  have hp:=original_coframe_direction_phi_gauge i
  have h:Commute D (GaussCoframeCore.momentum i):=
    sub_eq_zero.mp (show bracket D _=0 by rw [combined_delta,hp.1,hp.2.1,sub_self])
  exact h.add_right (combined_connection i)
private theorem combined_adjoint(i:Fin 6):Commute D (covariantAdjoint i):=by
  have hp:=original_coframe_direction_phi_gauge i
  have h:Commute D (GaussCoframeCore.adjoint i):=
    sub_eq_zero.mp (show bracket D _=0 by rw [combined_delta,hp.2.2.1,hp.2.2.2,sub_self])
  exact h.add_right (combined_connection i)
private theorem combined_metric(i j:Fin 6):Commute D (metricAction i j):=by
  have h:=original_coframe_local_phi_gauge (metricAction i j)
    (fun q=>(GaussCoframeKinetic.coefficient i j (q,(0:Slice)):ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _=>rfl)
  exact sub_eq_zero.mp (show bracket D _=0 by rw [combined_delta,h.1,h.2,sub_self])
theorem original_covariant_kinetic_combined:Commute D K:=by
  exact Commute.sum_right _ _ _ (fun i _=>Commute.sum_right _ _ _ (fun j _=>
    ((combined_adjoint i).mul_right (combined_metric i j)).mul_right (combined_momentum j)))
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem weighted_combined_pair(f g:QuantumTest):
    sourcePair f ((U*D) g)= -sourcePair ((U*D) f) g:=by
  have h:=ClockPhiMatchedNoiseCore.noiseGenerator_pair 0 1 f g
  simpa only [ClockPhiMatchedNoiseCore.noiseGenerator,Complex.ofReal_zero,Complex.ofReal_one,
    zero_smul,one_smul,zero_add] using h
private theorem inverse_dilation_pair(f g:QuantumTest):
    sourcePair f (SourceCoframeVolumeCurrent.dilation (U g))=
      sourcePair (SourceCoframeVolumeCurrent.dilation (U f)) g+
      (2*Complex.I)*sourcePair (U f) g:=by
  have h:=congrArg (fun X:End=>(-2*Complex.I/3) • X) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (SourceCoframeVolumeCurrent.dilation*U-U*SourceCoframeVolumeCurrent.dilation))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1:=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  have hc:(-2*Complex.I/3)*(-3:ℂ)=2*Complex.I:=by ring
  rw [hi,one_smul,hc] at h
  have he:SourceCoframeVolumeCurrent.dilation*U=U*SourceCoframeVolumeCurrent.dilation+(2*Complex.I) • U:=by
    linear_combination (norm:=module) h
  have hh:=LinearMap.congr_fun he f
  change SourceCoframeVolumeCurrent.dilation (U f)=U (SourceCoframeVolumeCurrent.dilation f)+(2*Complex.I) • U f at hh
  rw [dilation_pair]
  change sourcePair (SourceCoframeVolumeCurrent.dilation f) (multiply _ _ g)=_
  rw [multiply_pair]
  rw [hh]
  simp only [pair_add_l,pair_smul_l]
  norm_num [Complex.star_def]
  rfl
private theorem drift_pair(f g:QuantumTest):sourcePair f (driftClock g)= -sourcePair (driftClock f) g:=by
  change sourcePair f ((U*D) g+(3*Complex.I:ℂ) • (SourceCoframeVolumeCurrent.dilation (U g))+(3:ℂ) • U g)=_
  change _= -sourcePair ((U*D) f+(3*Complex.I:ℂ) • (SourceCoframeVolumeCurrent.dilation (U f))+(3:ℂ) • U f) g
  simp only [pair_add_r,pair_add_l,pair_smul_l,pair_smul_r]
  rw [weighted_combined_pair,inverse_dilation_pair]
  have hu:sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ f g
  rw [hu]
  norm_num [Complex.star_def]
  have hi:=Complex.I_mul_I
  linear_combination (norm:=ring) 6*sourcePair (U f) g*hi

private theorem root_local (B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (smooth:∀z:physicalChart,ContDiffAt ℝ ∞ B z.val):Commute a (localMultiplier B smooth):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (B z) (inverseRootVolume z:ℂ) (f z)).symm
private theorem root_connection(i:Fin 6):Commute a (connectionAction i):=root_local _ _
private theorem root_metric(i j:Fin 6):Commute a (metricAction i j):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (inverseRootVolume z:ℂ) (GaussCoframeKinetic.coefficient i j z:ℂ) (f z)
private theorem root_connection_square:Commute a connectionSquare:=
  Commute.sum_right _ _ _ (fun i _=>Commute.sum_right _ _ _ (fun j _=>
    ((root_connection i).mul_right (root_metric i j)).mul_right (root_connection j)))
theorem original_covariant_kinetic_root_contact:
    bracket a (bracket a K)=(-3*(sourceTime 0:ℂ)/8) • (U*U):=by
  have hC:=actual_coframe_current_root.eq
  have hR:=root_connection_square.eq
  unfold K
  rw [original_covariant_kinetic]
  have he:bracket a (bracket a (GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+connectionSquare))=
      bracket a (bracket a GaussCoframeKinetic.kinetic):=by
    unfold bracket
    simp only [add_mul,mul_add,hC,hR]
    noncomm_ring
  rw [he]
  exact actual_coframe_root_double_contact

private theorem bracket_product (X Y Z:End):bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z:=by
  unfold bracket;noncomm_ring
private theorem product_bracket (X Y Z:End):bracket (X*Y) Z=X*bracket Y Z+bracket X Z*Y:=by
  unfold bracket;noncomm_ring
private theorem bracket_add (X Y Z:End):bracket X (Y+Z)=bracket X Y+bracket X Z:=by
  unfold bracket;noncomm_ring

private theorem coframe_double_product (A D H:End)
    (ha:Commute A D)(hb:Commute A (bracket D H)):
    bracket (A*D) (bracket (A*D) H)=
      A*A*bracket D (bracket D H)+bracket A (bracket A H)*D*D := by
  have hda:bracket D A=0 := sub_eq_zero.mpr ha.eq.symm
  have had:bracket A D=0 := sub_eq_zero.mpr ha.eq
  have hab:bracket A (bracket D H)=0 := sub_eq_zero.mpr hb.eq
  have hdc:bracket D (bracket A H)=0 := by
    have hj:bracket D (bracket A H)=bracket A (bracket D H)+bracket (bracket D A) H := by
      unfold bracket;noncomm_ring
    rw [hj,hab,hda]
    simp [bracket]
  rw [product_bracket A D H,bracket_add,bracket_product,bracket_product]
  rw [product_bracket A D A,product_bracket A D (bracket D H),
    product_bracket A D (bracket A H),product_bracket A D D]
  simp only [hda,had,hab,hdc,zero_mul,mul_zero,add_zero,zero_add]
  have hz:bracket A A=0 := sub_self _
  have hzD:bracket D D=0 := sub_self _
  rw [hz,hzD]
  simp only [mul_zero,zero_mul,add_zero,zero_add,mul_assoc]


theorem original_covariant_kinetic_conjugate_contact:
    bracket A (bracket A K)=(-3*(sourceTime 0:ℂ)/8) • (U*U*D*D):=by
  have hD:bracket D K=0:=sub_eq_zero.mpr original_covariant_kinetic_combined.eq
  have hroot:Commute a (bracket D K):=by rw [hD];exact Commute.zero_right _
  change bracket (a*D) (bracket (a*D) K)=_
  rw [coframe_double_product a D K actual_root_combined_commute hroot,hD,
    original_covariant_kinetic_root_contact]
  simp only [bracket,mul_zero,zero_mul,sub_self,zero_add,smul_mul_assoc]

theorem actual_stochastic_covariant_current(f g:QuantumTest):
    stochasticPairJet f g=sourcePair f ((bracket A (bracket A K)) g):=by
  rw [original_covariant_kinetic_conjugate_contact]
  exact stochastic_jet_operator f g

private theorem scale_curve(z:SourceCoordinateSlice):
    HasDerivAt (fun r:ℝ=>SourceCoframeVolume.scale r z) (SourceCoframeVolume.euler z) 1:=by
  simpa only [SourceCoframeVolume.scale,SourceCoframeVolume.euler,id_eq,one_smul] using!
    ((hasDerivAt_id (1:ℝ)).smul_const z.1).prodMk (hasDerivAt_const 1 z.2)
private theorem connection_scale(r:ℝ)(hr:0<r)(z:physicalChart)(i:Fin 6):
    connectionFiber i (SourceCoframeVolume.scale r z.val)=((r⁻¹:ℝ):ℂ) • connectionFiber i z.val:=by
  simp only [connectionFiber,SourceCoframeVolume.scale,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [SourceClockPhiHeatSpinConnectionReturn.actual_spin_connection_scale r hr z i j,mul_smul]
  exact RCLike.real_smul_eq_coe_smul (K:=ℂ) (r⁻¹) ((spinConnection z.val.1 i j) • rotation j)
private theorem connection_euler(i:Fin 6):
    SourceCoframeDilation.eulerAction*connectionAction i-connectionAction i*SourceCoframeDilation.eulerAction=
      (-1:ℂ) • connectionAction i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · let B:=connectionFiber i z
    have hone:SourceCoframeVolume.scale 1 z=z:=by simp [SourceCoframeVolume.scale]
    have hg:=((connectionAction i f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt_of_eq 1 (scale_curve z) hone.symm
    have hf:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt_of_eq 1 (scale_curve z) hone.symm
    have hB:=(B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 1 hf
    have hi:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 ((hasDerivAt_id (1:ℝ)).inv (by norm_num))
    have hr:HasDerivAt (fun r:ℝ=>((r⁻¹:ℝ):ℂ)) (-1:ℂ) 1:=by
      simpa only [Function.comp_def,id_eq,one_pow,div_one,Complex.ofRealCLM_apply,Complex.ofReal_neg,Complex.ofReal_one] using! hi
    have hh:=hr.smul hB
    have he:∀ᶠ r:ℝ in nhds 1,
        connectionAction i f (SourceCoframeVolume.scale r z)=
          ((r⁻¹:ℝ):ℂ) • B (f (SourceCoframeVolume.scale r z)):=by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds (by norm_num:(0:ℝ)<1)] with r hr
      change connectionFiber i (SourceCoframeVolume.scale r z) (f (SourceCoframeVolume.scale r z))=_
      rw [connection_scale r hr ⟨z,hz⟩ i]
      rfl
    have hx:=hg.unique (hh.congr_of_eventuallyEq he)
    simp only [inv_one,Complex.ofReal_one,one_smul,ContinuousLinearMap.coe_restrictScalars',Function.comp_def,hone] at hx
    simp only [LinearMap.sub_apply,Module.End.mul_apply,neg_one_smul]
    change SourceCoframeDilation.eulerAction (connectionAction i f) z-
      connectionAction i (SourceCoframeDilation.eulerAction f) z= -connectionAction i f z
    rw [SourceCoframeDilation.eulerAction_apply]
    change fderiv ℝ (connectionAction i f) z (SourceCoframeVolume.euler z)-
      B (SourceCoframeDilation.eulerAction f z)= -B (f z)
    rw [SourceCoframeDilation.eulerAction_apply]
    rw [hx]
    module
  · have hzero(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    change (SourceCoframeDilation.eulerAction (connectionAction i f)-connectionAction i (SourceCoframeDilation.eulerAction f)) z=
      ((-1:ℂ) • connectionAction i f) z
    rw [hzero,hzero]
private theorem connection_number(i:Fin 6):Commute GaussCoframeForm.number (connectionAction i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeForm.number (connectionAction i f) z=connectionFiber i z (GaussCoframeForm.number f z)
  rw [SourceEulerCore.number_fiber,SourceEulerCore.number_fiber]
  change SourceQuantumFockGauge.fiberNumber (connectionFiber i z (f z))=connectionFiber i z (SourceQuantumFockGauge.fiberNumber (f z))
  simp only [connectionFiber,sum_apply,smul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he:(SourceQuantumFockGauge.fiberNumber.restrictScalars ℝ)
      ((spinConnection z.1 i j:ℝ) • rotation j (f z))=
      (spinConnection z.1 i j:ℝ) • SourceQuantumFockGauge.fiberNumber (rotation j (f z)):=map_smul _ _ _
  have ht:=congrArg (fun X:FockFiber→L[ℂ]FockFiber=>X (f z))
    (GaussQuantumMultiplier.number_commute (GaussCoframeSpin.full ⟨3+j.val,by omega⟩)).eq
  exact he.trans (congrArg (fun q:FockFiber=>(spinConnection z.1 i j:ℝ) • q) ht)
private theorem connection_dilation(i:Fin 6):
    SourceCoframeVolumeCurrent.dilation*connectionAction i-connectionAction i*SourceCoframeVolumeCurrent.dilation=
      (2*Complex.I/3) • connectionAction i:=by
  rw [SourceCoframeDilation.dilation_operator]
  have h:=SourceDilationAlgebra.affine_dilation _ _ _ (-1:ℂ) (connection_euler i) (connection_number i)
  have hc:(-2*Complex.I/3)*(-1:ℂ)=2*Complex.I/3:=by ring
  simpa only [hc,Module.End.one_eq_id] using! h


private theorem drift_homogeneous(T:End)(hU:Commute U T)(hD:Commute D T)
    (hd:SourceCoframeVolumeCurrent.dilation*T-T*SourceCoframeVolumeCurrent.dilation=
      (2*Complex.I/3) • T):
    T*driftClock=driftClock*T+(2:ℂ) • (U*T):=by
  have htd:T*SourceCoframeVolumeCurrent.dilation=
      SourceCoframeVolumeCurrent.dilation*T-(2*Complex.I/3) • T:=by
    linear_combination (norm:=module) -hd
  have htdu:T*(SourceCoframeVolumeCurrent.dilation*U)=
      (SourceCoframeVolumeCurrent.dilation*U)*T-(2*Complex.I/3) • (U*T):=by
    rw [←mul_assoc,htd,sub_mul,smul_mul_assoc,hU.eq.symm]
    simp only [mul_assoc]
    rw [hU.eq.symm]
  have htud:T*(U*D)=(U*D)*T:=by
    rw [←mul_assoc,hU.eq.symm,mul_assoc,hD.eq.symm,←mul_assoc]
  change T*(U*D+(3*Complex.I:ℂ) • (SourceCoframeVolumeCurrent.dilation*U)+(3:ℂ) • U)=_
  simp only [mul_add,mul_smul_comm]
  rw [htud,htdu,hU.eq.symm]
  change _=(U*D+(3*Complex.I:ℂ) • (SourceCoframeVolumeCurrent.dilation*U)+(3:ℂ) • U)*T+(2:ℂ) • (U*T)
  simp only [add_mul,smul_mul_assoc,smul_sub,smul_smul]
  have hi:(3*Complex.I)*(2*Complex.I/3)=(-2:ℂ):=by
    calc _=2*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi]
  module
private theorem inverse_connection(i:Fin 6):Commute U (connectionAction i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (connectionFiber i z) (reciprocalVolume z:ℂ) (f z)).symm
private theorem drift_connection(i:Fin 6):
    connectionAction i*driftClock=driftClock*connectionAction i+(2:ℂ) • (U*connectionAction i):=
  drift_homogeneous _ (inverse_connection i) (combined_connection i) (connection_dilation i)
private theorem inverse_metric(i j:Fin 6):Commute U (metricAction i j):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (reciprocalVolume z:ℂ) (GaussCoframeKinetic.coefficient i j z:ℂ) (f z)
private theorem drift_metric(i j:Fin 6):
    driftClock*metricAction i j=metricAction i j*driftClock-(2:ℂ) • (U*metricAction i j):=by
  have hd:=SourceDilationMultiplier.coframe_coefficient_commutator i j
  change SourceCoframeVolumeCurrent.dilation*metricAction i j-metricAction i j*SourceCoframeVolumeCurrent.dilation=
    (2*Complex.I/3) • metricAction i j at hd
  have h:=drift_homogeneous _ (inverse_metric i j) (combined_metric i j) hd
  linear_combination (norm:=module) -h

private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem covariant_adjoint_pair(i:Fin 6)(f g:QuantumTest):
    sourcePair f (covariantAdjoint i g)=sourcePair (SourceCoframeCovariantAction.covariantMomentum i f) g:=by
  simp only [covariantAdjoint,SourceCoframeCovariantAction.covariantMomentum,
    LinearMap.add_apply,pair_add_l,pair_add_r]
  exact congrArg₂ (·+·) (GaussCoframeKinetic.adjoint_pair i f g) (original_connection_pair i f g)
private theorem kinetic_pair(f g:QuantumTest):
    sourcePair f (K g)=∑i:Fin 6,∑j:Fin 6,
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
        (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j g)):=by
  simp only [K,covariantKinetic,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact covariant_adjoint_pair i f _
private theorem inverse_column(i:Fin 6):Commute U (sourceCurrentColumn i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (reciprocalVolume z:ℂ) ((reciprocalVolume z*volumeGradient z i:ℝ):ℂ) (f z)
private theorem weighted_pair(f g:QuantumTest):sourcePair (U f) g=sourcePair f (U g):=
  (multiply_pair _ _ f g).symm
private theorem drift_pair_left(f g:QuantumTest):sourcePair (driftClock f) g= -sourcePair f (driftClock g):=by
  simpa only [neg_neg] using congrArg Neg.neg (drift_pair f g).symm
private theorem deterministic_row_pair(i j:Fin 6)(f g:QuantumTest)
    (hBf:SourceCoframeCovariantAction.covariantMomentum i (driftClock f)=
      driftClock (SourceCoframeCovariantAction.covariantMomentum i f)+
        (2:ℂ) • U (SourceCoframeCovariantAction.covariantMomentum i f)+
        Complex.I • sourceCurrentColumn i (driftClock f))
    (hBg:SourceCoframeCovariantAction.covariantMomentum j (driftClock g)=
      driftClock (SourceCoframeCovariantAction.covariantMomentum j g)+
        (2:ℂ) • U (SourceCoframeCovariantAction.covariantMomentum j g)+
        Complex.I • sourceCurrentColumn j (driftClock g))
    (hUf:SourceCoframeCovariantAction.covariantMomentum i (U f)=
      U (SourceCoframeCovariantAction.covariantMomentum i f)+Complex.I • U (sourceCurrentColumn i f))
    (hUg:SourceCoframeCovariantAction.covariantMomentum j (U g)=
      U (SourceCoframeCovariantAction.covariantMomentum j g)+Complex.I • U (sourceCurrentColumn j g)):
    (-12:ℂ)*sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
      (U (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j g)))+
      sourcePair (coframeDriftColumn i f) (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j g))+
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i f) (metricAction i j (coframeDriftColumn j g))=
      (3:ℂ)*(-sourcePair (SourceCoframeCovariantAction.covariantMomentum i (driftClock f))
          (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j g))-
        sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
          (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j (driftClock g))))+
      (3:ℂ)*(sourcePair (SourceCoframeCovariantAction.covariantMomentum i (U f))
          (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j g))+
        sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
          (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j (U g)))):=by
  have hc(q:QuantumTest):sourceCurrentColumn i (U q)=U (sourceCurrentColumn i q):=
    LinearMap.congr_fun (inverse_column i).eq.symm q
  have hc'(q:QuantumTest):sourceCurrentColumn j (U q)=U (sourceCurrentColumn j q):=
    LinearMap.congr_fun (inverse_column j).eq.symm q
  have hm(q:QuantumTest):driftClock (metricAction i j q)=
      metricAction i j (driftClock q)-(2:ℂ) • U (metricAction i j q):=
    LinearMap.congr_fun (drift_metric i j) q
  rw [hBf,hBg,hUf,hUg]
  have ht:SourceClockPhiNativeMatchedSource.matchedTester=driftClock-U:=by
    unfold SourceClockPhiNativeMatchedSource.matchedTester driftClock
    module
  unfold coframeDriftColumn
  rw [ht]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,LinearMap.sub_apply,map_add,map_sub,map_smul,
    pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,pair_sub_l,pair_sub_r]
  rw [drift_pair_left,hm,weighted_pair,hc,hc']
  have huM(q:QuantumTest):metricAction i j (U q)=U (metricAction i j q):=
    LinearMap.congr_fun (inverse_metric i j).eq.symm q
  simp only [huM]
  simp only [pair_sub_r,pair_smul_r]
  norm_num [Complex.star_def]
  ring

private theorem deterministic_pair_from_rows(f g:QuantumTest)
    (hB:∀i:Fin 6,∀q:QuantumTest,SourceCoframeCovariantAction.covariantMomentum i (driftClock q)=
      driftClock (SourceCoframeCovariantAction.covariantMomentum i q)+
        (2:ℂ) • U (SourceCoframeCovariantAction.covariantMomentum i q)+
        Complex.I • sourceCurrentColumn i (driftClock q))
    (hU:∀i:Fin 6,∀q:QuantumTest,SourceCoframeCovariantAction.covariantMomentum i (U q)=
      U (SourceCoframeCovariantAction.covariantMomentum i q)+Complex.I • U (sourceCurrentColumn i q)):
    deterministicPairJet f g=(3:ℂ)*sourcePair f ((bracket driftClock K) g)+
      (3:ℂ)*sourcePair f ((U*K+K*U) g):=by
  have hb:sourcePair f ((bracket driftClock K) g)=
      -sourcePair (driftClock f) (K g)-sourcePair f (K (driftClock g)):=by
    change sourcePair f (driftClock (K g)-K (driftClock g))=_
    rw [pair_sub_r,drift_pair]
  have hu:sourcePair f ((U*K+K*U) g)=sourcePair (U f) (K g)+sourcePair f (K (U g)):=by
    change sourcePair f (U (K g)+K (U g))=_
    rw [pair_add_r]
    exact congrArg (fun x=>x+sourcePair f (K (U g))) (weighted_pair f (K g)).symm
  rw [hb,hu,kinetic_pair,kinetic_pair,kinetic_pair,kinetic_pair]
  simp only [deterministicPairJet,Finset.mul_sum,←Finset.sum_neg_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact deterministic_row_pair i j f g (hB i f) (hB j g) (hU i f) (hU j g)
private theorem complete_current_decompose(T:End):
    completeCurrent T=bracket A (bracket A T)+(3:ℂ) • bracket driftClock T+(3:ℂ) • (U*T+T*U):=by
  change ((A*A+(3:ℂ) • driftClock)*T+T*(A*A-(3:ℂ) • driftClock)-(2:ℂ) • (A*T*A))+
    (3:ℂ) • (U*T+T*U)=_
  unfold bracket
  simp only [add_mul,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_sub]
  simp only [mul_assoc,smul_add]
  module


private theorem covariant_inverse_volume(i:Fin 6):
    SourceCoframeCovariantAction.covariantMomentum i*U=U*SourceCoframeCovariantAction.covariantMomentum i+
      Complex.I • (U*sourceCurrentColumn i):=by
  have hr:=ClockPhiCoframeDriftMomentumPrimitive.bare_momentum_inverse_volume i
  have hc:connectionAction i*U=U*connectionAction i:=(inverse_connection i).eq.symm
  change (GaussCoframeCore.momentum i+connectionAction i)*U=U*(GaussCoframeCore.momentum i+connectionAction i)+_
  rw [add_mul,mul_add,hr,hc]
  abel
private theorem covariant_drift_row(i:Fin 6):
    SourceCoframeCovariantAction.covariantMomentum i*driftClock=
      driftClock*SourceCoframeCovariantAction.covariantMomentum i+
        (2:ℂ) • (U*SourceCoframeCovariantAction.covariantMomentum i)+Complex.I • (sourceCurrentColumn i*driftClock):=by
  have hr:=ClockPhiCoframeDriftMomentumPrimitive.bare_momentum_drift_row i
  change (GaussCoframeCore.momentum i+connectionAction i)*driftClock=
    driftClock*(GaussCoframeCore.momentum i+connectionAction i)+(2:ℂ) • (U*(GaussCoframeCore.momentum i+connectionAction i))+_
  rw [add_mul,mul_add,mul_add,hr,drift_connection,smul_add]
  abel

theorem actual_coframe_full36_first_jet_Q(f g:QuantumTest):
    deterministicPairJet f g+stochasticPairJet f g=
      sourcePair f ((completeCurrent SourceCoframeCovariantAction.covariantKinetic) g):=by
  have hB(i:Fin 6)(q:QuantumTest):SourceCoframeCovariantAction.covariantMomentum i (driftClock q)=
      driftClock (SourceCoframeCovariantAction.covariantMomentum i q)+
        (2:ℂ) • U (SourceCoframeCovariantAction.covariantMomentum i q)+
        Complex.I • sourceCurrentColumn i (driftClock q):=LinearMap.congr_fun (covariant_drift_row i) q
  have hU(i:Fin 6)(q:QuantumTest):SourceCoframeCovariantAction.covariantMomentum i (U q)=
      U (SourceCoframeCovariantAction.covariantMomentum i q)+Complex.I • U (sourceCurrentColumn i q):=
    LinearMap.congr_fun (covariant_inverse_volume i) q
  rw [deterministic_pair_from_rows f g hB hU,actual_stochastic_covariant_current,
    complete_current_decompose]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_r,pair_smul_r]
  ring

end LowEnergy.SourceClockPhiOriginalGaussianH0CoframeRecognition
