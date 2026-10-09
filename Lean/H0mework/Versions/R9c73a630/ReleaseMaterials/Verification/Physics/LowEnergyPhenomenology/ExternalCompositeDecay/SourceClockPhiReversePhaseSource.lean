import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeReverseFrequencyWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteClockReverseReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeOuterSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumGaugeSliceCoordinates
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceClockPhiCombinedScalePressure SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiNativeJointPayment SourceClockYukawaCubicCurrent SourceScalarDoubleCurrent
open SourceCoframeVolumeCurrent SourceClockPhiNormalizedScalarBudget ReverseNativeClock ReverseNativeFrequencyWard
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev S:End:=phiInverseAction
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev Gauge:End:=SourceGaugeScaleTransport.generator
private abbrev Dc:End:=dilation
private abbrev Z:End:=reverseNativeClock
attribute [local irreducible] sourcePair embed reverseNativeClock phiInverseAction
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator dilation coreEquiv
private theorem inverse_apply (f:QuantumTest) (z:SourceCoordinateSlice) (word:Occupation) :
    S f z word=(phiReciprocal z:ℂ)*f z word:=by
  unfold S phiInverseAction
  rfl
private theorem gauge_inverse:Commute Gauge S:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have hp:=SourceGaugeScaleTransport.coreFlow_generator (S f) z word
  have hq:=(SourceGaugeScaleTransport.coreFlow_generator f z word).const_mul (phiReciprocal z:ℂ)
  have he:(fun t:ℝ=>SourceGaugeScaleTransport.coreFlow t (S f) z word)=
      fun t=>(phiReciprocal z:ℂ)*SourceGaugeScaleTransport.coreFlow t f z word:=by
    funext t
    simp only [SourceGaugeScaleTransport.coreFlow_apply,inverse_apply]
    change (Real.exp (18*t):ℂ)*((phiReciprocal (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z):ℂ)*
      f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z) word)=_
    have hr:phiReciprocal (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z)=phiReciprocal z:=rfl
    rw [hr]
    ring
  rw [he] at hp
  change Gauge (S f) z word=S (Gauge f) z word
  rw [inverse_apply]
  exact hp.unique hq
private theorem coframe_inverse:Commute Dc S:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext
    intro word
    have hp:=SourceCoframeScaleTransport.coreFlow_generator (S f) ⟨z,hz⟩ word
    have hq:=(SourceCoframeScaleTransport.coreFlow_generator f ⟨z,hz⟩ word).const_mul (phiReciprocal z:ℂ)
    have he:(fun t:ℝ=>SourceCoframeScaleTransport.coreFlow t (S f) z word)=
        fun t=>(phiReciprocal z:ℂ)*SourceCoframeScaleTransport.coreFlow t f z word:=by
      funext t
      simp only [SourceCoframeScaleTransport.coreFlow_apply,inverse_apply]
      change (Real.exp ((word.card+4:ℝ)*t):ℂ)*((phiReciprocal
        (SourceCoframeVolume.scale (SourceCoframeScaleTransport.rate t) z):ℂ)*
          f (SourceCoframeVolume.scale (SourceCoframeScaleTransport.rate t) z) word)=_
      have hr:phiReciprocal (SourceCoframeVolume.scale (SourceCoframeScaleTransport.rate t) z)=phiReciprocal z:=rfl
      rw [hr]
      ring
    rw [he] at hp
    have h:=hp.unique hq
    change Dc (S f) z word=S (Dc f) z word
    rw [inverse_apply]
    apply (mul_left_cancel₀ Complex.I_ne_zero)
    change Complex.I*Dc (S f) z word=Complex.I*((phiReciprocal z:ℂ)*Dc f z word)
    exact h.trans (by ring)
  · have hzero(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm
private theorem row_commute(A:End)(h:Commute A S)(m ell:ℕ)(i:Fin 2):Commute A (phaseRow m ell i):=by
  have hQ:A*(1-S)=(1-S)*A:=by
    apply LinearMap.ext
    intro f
    change A (f-S f)=A f-S (A f)
    rw [map_sub]
    exact congrArg (fun q:QuantumTest=>A f-q) (congrArg (fun Q:End=>Q f) h.eq)
  have hp(k:ℕ):A*((1-S)^k)=((1-S)^k)*A:=by
    induction k with
    | zero => simp only [pow_zero,mul_one,one_mul]
    | succ k ih =>
      rw [pow_succ]
      calc
        _=(A*((1-S)^k))*(1-S):=rfl
        _=(((1-S)^k)*A)*(1-S):=by rw [ih]
        _=((1-S)^k)*(A*(1-S)):=rfl
        _=((1-S)^k)*((1-S)*A):=by rw [hQ]
        _=_:=rfl
  have hT:A*phiThetaAction m ell=phiThetaAction m ell*A:=by
    change A*((1-S)^(m+1)-(1-S)^(ell+1))=((1-S)^(m+1)-(1-S)^(ell+1))*A
    apply LinearMap.ext
    intro f
    change A (((1-S)^(m+1)) f-((1-S)^(ell+1)) f)=
      ((1-S)^(m+1)) (A f)-((1-S)^(ell+1)) (A f)
    rw [map_sub]
    exact congrArg₂ (fun u v:QuantumTest=>u-v)
      (congrArg (fun Q:End=>Q f) (hp (m+1)))
      (congrArg (fun Q:End=>Q f) (hp (ell+1)))
  fin_cases i
  · exact hT
  · change A*(-(S*phiThetaAction m ell))=(-(S*phiThetaAction m ell))*A
    apply LinearMap.ext
    intro f
    change A (-(S (phiThetaAction m ell f)))= -(S (phiThetaAction m ell (A f)))
    rw [map_neg]
    apply congrArg Neg.neg
    exact congrArg (fun Q:End=>Q f) (show A*(S*phiThetaAction m ell)=(S*phiThetaAction m ell)*A from by
    calc
      _=(A*S)*phiThetaAction m ell:=rfl
      _=(S*A)*phiThetaAction m ell:=by rw [h.eq]
      _=S*(A*phiThetaAction m ell):=rfl
      _=S*(phiThetaAction m ell*A):=by rw [hT]
      _=_:=rfl)

/-- The actual gauge and coframe parts preserve the original scalar profile. The full balanced Z profile word is exactly three times the paid Phi jet. -/
theorem actual_reverse_phase_row(m ell:ℕ)(i:Fin 2):
    bracket Z (phaseRow m ell i)=(3:ℂ) • bracket Phi (phaseRow m ell i):=by
  have hg:=row_commute Gauge gauge_inverse m ell i
  have hc:=row_commute Dc coframe_inverse m ell i
  unfold Z reverseNativeClock
  change bracket ((3:ℂ) • (Phi-Gauge)-(9*Complex.I:ℂ) • Dc) (phaseRow m ell i)=_
  unfold bracket
  linear_combination (norm:=(noncomm_ring;module)) (-3:ℂ) • hg.eq-(9*Complex.I:ℂ) • hc.eq

def reverseInputSeed(g:diagonal.domain)(i:Fin 2):diagonal.domain:=
  coreEquiv (Z (coreEquiv.symm (inputSeed g i)))
def reverseInputVector(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  (3:ℂ) • phaseFirst m ell F z hz g+
    ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (reverseInputSeed g i)))

/-- Both Z-inputs are generated from the same original two seeds; no independent response occurrence is selected. -/
theorem actual_reverse_input_vector(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (∑i:Fin 2,(bracket Z (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
      phaseRow m ell i (resolventCore F z hz (Z (coreEquiv.symm (inputSeed g i))))))=
      reverseInputVector m ell F z hz g:=by
  simp only [actual_reverse_phase_row,LinearMap.smul_apply,Finset.sum_add_distrib,←Finset.smul_sum,
    reverseInputVector,reverseInputSeed,coreEquiv.symm_apply_apply]
  congr 2
  simp only [phaseFirst,Fin.sum_univ_two,phaseSeed,inputSeed,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hr:coreEquiv.symm (phiRadiusSource g)=phiRadiusAction (coreEquiv.symm g):=by
    unfold phiRadiusSource
    exact coreEquiv.symm_apply_apply _
  simp only [hr]
end LowEnergy.ReverseNativeOuterSource
