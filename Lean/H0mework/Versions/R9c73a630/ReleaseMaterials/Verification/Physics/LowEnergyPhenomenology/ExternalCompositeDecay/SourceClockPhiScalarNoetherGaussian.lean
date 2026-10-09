import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiAdmissibleElectricSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianPair
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileNativeReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentAdmissibleElectric.ScalarGaussian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceScalarVirialBulk SourceGaugeRadialCurrent SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep SourceClockPhiCompleteHeatGainPayment
open SourceClockPhiProfileCoframeReturn ClockPhiConservativeHeatSource ClockPhiMatchedNoiseCore SourceKineticScale
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace Matrix
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev FiberOp:=FockFiber→L[ℂ]FockFiber
private theorem profileInvariant(c:SourceCoordinateSlice→ℝ)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (u:ℝ)(z:SourceCoordinateSlice):c (combinedMap u z)=c z:=hfirst _ _ rfl
private abbrev input(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):Op:=clockProfileAction c hc (profileInvariant c hfirst) 1
private abbrev heat(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):Op:=sourceForwardCore t ht.le*input c hc hfirst
private theorem input_point(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f:QuantumTest)(z:SourceCoordinateSlice):
    input c hc hfirst f z=(Real.exp ((25/2:ℝ)*c z):ℂ) • f (combinedMap (c z) z):=by
  change (Real.exp ((25/2:ℝ)*(1*c z)):ℂ) • f (combinedMap (1*c z) z)=_
  simp only [one_mul]
private def w(t:ℝ)(c:SourceCoordinateSlice→ℝ)(p q:ℝ)(z:SourceCoordinateSlice):ℝ:=
  (forwardRatio t z)^p*Real.exp (q*c z)
private theorem w_smooth(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(p q:ℝ)(z:physicalChart):ContDiffAt ℝ ∞ (w t c p q) z.val:=by
  have h:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact (h.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne').mul ((contDiffAt_const.mul (hc z)).exp)
private def actualProfileWeight(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(p q:ℝ):Op:=multiply (w t c p q) (w_smooth t ht c hc p q)
private theorem w_invariant(t:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p q s:ℝ)(z:SourceCoordinateSlice):
    w t c p q (combinedMap s z)=w t c p q z:=by
  unfold w
  rw [profileInvariant c hfirst]
  rfl
private theorem complete_forward_point(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f:QuantumTest)(z:physicalChart):
    profileCompleteCore t ht c hc (profileInvariant c hfirst) f (forwardPoint t z.val)=
      GaussFockWeights.weight (fun N=>(Real.rpow (forwardRatio t z.val) (-((N+3:ℝ)/2)):ℂ))
        ((Real.exp ((25/2:ℝ)*c z.val):ℂ) •
          ((gainProfile (Real.sqrt t) z.val:ℂ) • f (combinedMap (c z.val) z.val))):=by
  apply PiLp.ext
  intro word
  change heat t ht c hc hfirst (sourceGain (Real.sqrt t) f) (forwardPoint t z.val) word=_
  rw [Module.End.mul_apply,forwardCore_apply,input_point]
  have hg:gainProfile (Real.sqrt t) (combinedMap (c z.val) z.val)=gainProfile (Real.sqrt t) z.val:=rfl
  change (_:ℂ)*((Real.exp ((25/2:ℝ)*c z.val):ℂ)*
    ((gainProfile (Real.sqrt t) (combinedMap (c z.val) z.val):ℂ)*f _ word))=_
  rw [hg]
  rfl
private theorem local_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p d:ℝ)(T:Op)(B:SourceCoordinateSlice→FiberOp)
    (hT:∀f z,T f z=B z (f z))
    (hNumber:∀z a,Commute (GaussFockWeights.weight a) (B z))
    (hForward:∀z:physicalChart,B (forwardPoint t z.val)=(((forwardRatio t z.val)^p:ℝ):ℂ) • B z.val)
    (hCombined:∀s z,B (combinedMap s z)=(Real.exp (d*s):ℂ) • B z):
    T*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc p (-d)*T):=by
  have hp(z:physicalChart)(f:QuantumTest):
      T (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (forwardPoint t z.val)=
        profileCompleteCore t ht c hc (profileInvariant c hfirst) (actualProfileWeight t ht c hc p (-d) (T f)) (forwardPoint t z.val):=by
    rw [hT,complete_forward_point t ht c hc hfirst,complete_forward_point t ht c hc hfirst,hForward]
    change (((forwardRatio t z.val)^p:ℝ):ℂ) • B z.val
      (GaussFockWeights.weight _ ((_ :ℂ) • ((_ :ℂ) • f _)))=
      GaussFockWeights.weight _ ((_ :ℂ) • ((_ :ℂ) • ((w t c p (-d) _:ℂ) • T f _)))
    rw [w_invariant t c hfirst,hT,hCombined]
    let a:ℕ→ℂ:=fun N=>(Real.rpow (forwardRatio t z.val) (-((N+3:ℝ)/2)):ℂ)
    have hN:GaussFockWeights.weight a (B z.val (f (combinedMap (c z.val) z.val)))=
      B z.val (GaussFockWeights.weight a (f (combinedMap (c z.val) z.val))):=
      congrArg (fun A:FiberOp=>A (f (combinedMap (c z.val) z.val))) (hNumber z.val a).eq
    simp only [smul_apply,map_smul,smul_smul]
    rw [←hN]
    congr 1
    have he:(Real.exp ((-d)*c z.val):ℂ)*(Real.exp (d*c z.val):ℂ)=1:=by
      rw [←Complex.ofReal_mul,←Real.exp_add]
      simp only [neg_mul,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
    rw [show (-d)*c z.val= -(c z.val*d) by ring,
      show d*c z.val=c z.val*d by ring] at he
    dsimp only [w]
    rw [Complex.ofReal_mul]
    linear_combination (norm:=ring) -(((forwardRatio t z.val)^p:ℝ):ℂ)*
      (Real.exp ((25/2:ℝ)*c z.val):ℂ)*(gainProfile (Real.sqrt t) z.val:ℂ)*he
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  by_cases hx:x∈physicalChart
  · by_cases ha:18*t<GaussNativeEnergy.volume x
    · let z:physicalChart:=⟨backwardPoint t x,backward_chart t ht.le ⟨x,hx⟩ ha⟩
      have hz:forwardPoint t z.val=x:=forward_backward t ht.le x ha
      change T (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) x=profileCompleteCore t ht c hc (profileInvariant c hfirst) (actualProfileWeight t ht c hc p (-d) (T f)) x
      rw [←hz]
      exact hp z f
    · change T (heat t ht c hc hfirst (sourceGain (Real.sqrt t) f)) x=
        heat t ht c hc hfirst (sourceGain (Real.sqrt t) (actualProfileWeight t ht c hc p (-d) (T f))) x
      rw [hT]
      change B x (forwardValue t _ x)=forwardValue t _ x
      simp only [forwardValue,if_neg ha,map_zero]
  · have h0(q:QuantumTest):q x=0:=image_eq_zero_of_notMem_tsupport (fun h=>hx (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem scalar_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p d:ℝ)(T:Op)(a:SourceCoordinateSlice→ℝ)
    (hT:∀f z,T f z=(a z:ℂ) • f z)
    (hForward:∀z:physicalChart,a (forwardPoint t z.val)=(forwardRatio t z.val)^p*a z.val)
    (hCombined:∀s z,a (combinedMap s z)=Real.exp (d*s)*a z):
    T*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc p (-d)*T):=by
  apply local_transport t ht c hc hfirst p d T (fun z=>(a z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) hT
  · intro z b
    change GaussFockWeights.weight b*((a z:ℂ) • (1:FiberOp))=((a z:ℂ) • (1:FiberOp))*GaussFockWeights.weight b
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  · intro z
    rw [hForward,Complex.ofReal_mul,smul_smul]
  · intro s z
    rw [hCombined,Complex.ofReal_mul,smul_smul]
private theorem heat_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (heat t ht c hc hfirst f) (heat t ht c hc hfirst g)=sourcePair f g:=by
  change sourcePair (sourceForwardCore t ht.le (input c hc hfirst f))
    (sourceForwardCore t ht.le (input c hc hfirst g))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair,clockProfileAction_pair]
private theorem gain_pair(e:ℝ)(f g:QuantumTest):sourcePair (sourceGain e f) g=sourcePair f (sourceGain e g):=by
  have hs(z:physicalChart):ContDiffAt ℝ ∞ (gainProfile e) z.val:=by
    have h:ContDiffAt ℝ ∞ (forwardRatio (e^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact h.rpow_const_of_ne (forward_ratio_pos (e^2) (sq_nonneg _) z).ne'
  change sourcePair (multiply (gainProfile e) hs f) g=sourcePair f (multiply (gainProfile e) hs g)
  exact (multiply_pair _ _ f g).symm
private theorem gain_squared_weight(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (p q:ℝ):
    sourceGain (Real.sqrt t)*(sourceGain (Real.sqrt t)*actualProfileWeight t ht c hc p q)=actualProfileWeight t ht c hc (p+1/3) q:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hg:(gainProfile (Real.sqrt t) z)^2=(forwardRatio t z)^(1/3:ℝ):=by
      unfold gainProfile
      rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
      congr 1
      norm_num
    have hh:gainProfile (Real.sqrt t) z*gainProfile (Real.sqrt t) z*w t c p q z=w t c (p+1/3) q z:=by
      unfold w
      rw [←pow_two,hg,←mul_assoc,←Real.rpow_add hr,add_comm (1/3:ℝ)]
    apply PiLp.ext
    intro word
    change (gainProfile (Real.sqrt t) z:ℂ)*((gainProfile (Real.sqrt t) z:ℂ)*((w t c p q z:ℂ)*f z word))=(w t c (p+1/3) q z:ℂ)*f z word
    have hc:=congrArg Complex.ofReal hh
    simp only [Complex.ofReal_mul] at hc
    rw [←mul_assoc,←mul_assoc,hc]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (_:ℂ) • ((_ :ℂ) • ((_ :ℂ) • f z))=(_ :ℂ) • f z
    rw [hf,smul_zero,smul_zero,smul_zero,smul_zero]
private theorem paired_return(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p d:ℝ)(T:Op)
    (h:T*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc p (-d)*T))(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (T (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (p+1/3) (-d) (T g)):=by
  have hx:=LinearMap.congr_fun h g
  change T (profileCompleteCore t ht c hc (profileInvariant c hfirst) g)=profileCompleteCore t ht c hc (profileInvariant c hfirst) (actualProfileWeight t ht c hc p (-d) (T g)) at hx
  rw [hx]
  change sourcePair (heat t ht c hc hfirst (sourceGain (Real.sqrt t) f))
    (heat t ht c hc hfirst (sourceGain (Real.sqrt t) (actualProfileWeight t ht c hc p (-d) (T g))))=_
  rw [heat_pair,gain_pair]
  exact congrArg (sourcePair f) (LinearMap.congr_fun (gain_squared_weight t ht c hc p (-d)) (T g))

private theorem scalar_field_finite(s:ℝ)(z:SourceCoordinateSlice):scalarField (combinedMap s z)=Real.exp s • scalarField z:=by
  change vacuum+(Real.exp s • ((z.2.1:Scalar)+vacuum)-vacuum)=Real.exp s • (vacuum+(z.2.1:Scalar))
  module

open SourceClockPhiProfileNativeReturn SourceClockPhiCorrectedGaussianPair ClockPhiHeatCorrectedCovarianceSource
open SourceClockPhiHeatLocalNativeGaussian SourceClockPhiCorrectedWeightTransport SourceClockPhiForwardNativeReturn
open SourceScalarShiftedBulk SourceGammaNativeBudget GaussLiveMomentum
open MeasureTheory
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private def affineColumn(a:ScalarIndex):Op:=multiply
  (fun z=>inner ℝ (scalarField z) (scalarBasis a))
  (fun _=>(scalarField_smooth.inner ℝ contDiff_const).contDiffAt)
private theorem affine_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(a:ScalarIndex):
    affineColumn a*profileCompleteCore t ht c hc (profileInvariant c hfirst)=
      profileCompleteCore t ht c hc (profileInvariant c hfirst)*
        (actualProfileWeight t ht c hc 0 (-1)*affineColumn a):=by
  apply scalar_transport t ht c hc hfirst 0 1 (affineColumn a)
    (fun z=>inner ℝ (scalarField z) (scalarBasis a)) (fun _ _=>rfl)
  · intro z
    simp only[Real.rpow_zero,one_mul]
    rfl
  · intro u z
    rw [scalar_field_finite,real_inner_smul_left]
    simp only[one_mul]
private theorem quarter_split(a:ScalarIndex):quarterColumn a=affineColumn a-
    ((3*inner ℝ (scalarBasis a) vacuum/4:ℝ):ℂ) • (1:Op):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ) • f z+
    ((inner ℝ (scalarBasis a) vacuum/4:ℝ):ℂ) • f z=
    (inner ℝ (scalarField z) (scalarBasis a):ℂ) • f z-
      ((3*inner ℝ (scalarBasis a) vacuum/4:ℝ):ℂ) • f z
  simp only[SourceClosedCostNativeProbe.coordinate,scalarDirection,scalarField,inner_add_left,
    real_inner_comm vacuum (scalarBasis a),←add_smul,←sub_smul]
  congr 1
  push_cast
  ring
private def exponentialWeight(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(q:ℝ):Op:=
  multiply (fun z=>Real.exp (q*c z)) (fun z=>(contDiffAt_const.mul (hc z)).exp)
private theorem exp_weight(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(q:ℝ):
    actualProfileWeight t ht c hc 0 q=exponentialWeight c hc q:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (((forwardRatio t z)^0*Real.exp (q*c z):ℝ):ℂ) • f z=_
  simp only[Real.rpow_zero,one_mul]
  rfl
private theorem real_commute(a b:SourceCoordinateSlice→ℝ)
    (ha:∀z:physicalChart,ContDiffAt ℝ ∞ a z.val)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute (multiply a ha) (multiply b hb):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (a z:ℂ) (b z:ℂ) (f z)
private theorem exp_add(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(p q:ℝ):
    exponentialWeight c hc p*exponentialWeight c hc q=exponentialWeight c hc (p+q):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (Real.exp (p*c z):ℂ) • ((Real.exp (q*c z):ℂ) • f z)=
    (Real.exp ((p+q)*c z):ℂ) • f z
  rw [smul_smul,←Complex.ofReal_mul,←Real.exp_add,add_mul]
private theorem complete_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f)
      (profileCompleteCore t ht c hc (profileInvariant c hfirst) g)=
      sourcePair f ((sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t)) g):=by
  change sourcePair (heat t ht c hc hfirst (sourceGain (Real.sqrt t) f))
    (heat t ht c hc hfirst (sourceGain (Real.sqrt t) g))=_
  rw [heat_pair,gain_pair]
  rfl
private theorem two_exp_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p q:ℝ)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) (exponentialWeight c hc p f))
      (profileCompleteCore t ht c hc (profileInvariant c hfirst) (exponentialWeight c hc q g))=
      sourcePair f (actualProfileWeight t ht c hc (1/3) (p+q) g):=by
  rw [complete_pair t ht c hc hfirst]
  have hp(f g:QuantumTest):sourcePair (exponentialWeight c hc p f) g=sourcePair f (exponentialWeight c hc p g):=
    (multiply_pair _ _ f g).symm
  rw [hp]
  have hG:Commute (exponentialWeight c hc p) (sourceGain (Real.sqrt t)):=real_commute _ _ _ _
  have hp:exponentialWeight c hc p*(sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t))*exponentialWeight c hc q=
      (sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t))*exponentialWeight c hc (p+q):=by
    have hh:exponentialWeight c hc p*(sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t))=
        (sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t))*exponentialWeight c hc p:=by
      linear_combination (norm:=noncomm_ring) hG.eq*sourceGain (Real.sqrt t)+sourceGain (Real.sqrt t)*hG.eq
    rw [hh]
    have he:=exp_add c hc p q
    linear_combination (norm:=noncomm_ring) (sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t))*he
  change sourcePair f ((exponentialWeight c hc p*(sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t))*exponentialWeight c hc q) g)=_
  have hw:(sourceGain (Real.sqrt t)*sourceGain (Real.sqrt t))*exponentialWeight c hc (p+q)=
      actualProfileWeight t ht c hc (1/3) (p+q):=by
    rw [←exp_weight t ht c hc (p+q)]
    have h:=gain_squared_weight t ht c hc 0 (p+q)
    simpa only[zero_add,←mul_assoc] using h
  rw [hp,hw]
private theorem coeff_first(t ξ η:ℝ)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rcases x with ⟨x₁,x₂⟩;rcases y with ⟨y₁,y₂⟩
  dsimp at h;subst y₁;rfl

private theorem U_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    inverseVolumeAction (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η (forwardUAction t ht.le f):=
  LinearMap.congr_fun (actual_corrected_complete_inverse_volume t ht ξ η) f
private theorem exp_forward(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest):
    forwardUAction t ht.le (exponentialWeight c hc 1 f)=
      exponentialWeight c hc 1 (forwardUAction t ht.le f):=
  LinearMap.congr_fun (real_commute _ _ _ _).eq f

/-- The original native momentum and forced affine scalar column return as one deterministic source pair. -/
theorem actual_scalar_affine_profile_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(a:ScalarIndex)(f g:QuantumTest):
    sourcePair (inverseVolumeAction (GaussCoreDifferential.covariantMomentum (scalarDirection a)
      (correctedCompleteCore t ht ξ η f))) (affineColumn a (correctedCompleteCore t ht ξ η g))=
      sourcePair (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
        (correctedProfileWeight t ht (1/3) 0 ξ η (affineColumn a g)):=by
  let c:=correctedCoefficient t ξ η
  let hc:=ClockPhiHeatCorrectedCovarianceSource.coefficient_smooth t ht ξ η
  let hf:=coeff_first t ξ η
  have hP:=LinearMap.congr_fun (actual_complete_profile_scalar_momentum c hc hf t ht (scalarDirection a) rfl) f
  have hQ:=LinearMap.congr_fun (affine_transport t ht c hc hf a) g
  change GaussCoreDifferential.covariantMomentum (scalarDirection a) (correctedCompleteCore t ht ξ η f)=
    correctedCompleteCore t ht ξ η (exponentialWeight c hc 1 (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)) at hP
  change affineColumn a (correctedCompleteCore t ht ξ η g)=
    correctedCompleteCore t ht ξ η (actualProfileWeight t ht c hc 0 (-1) (affineColumn a g)) at hQ
  rw [hP,hQ,exp_weight t ht c hc (-1)]
  rw [U_return t ht]
  rw [exp_forward t ht]
  have hp:=two_exp_pair t ht c hc hf 1 (-1)
    (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)) (affineColumn a g)
  norm_num at hp
  exact hp

private theorem exp_zero(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest):exponentialWeight c hc 0 f=f:=by
  apply DFunLike.ext;intro z
  change (Real.exp (0*c z):ℂ) • f z=f z
  simp only[zero_mul,Real.exp_zero,Complex.ofReal_one,one_smul]
private theorem scalar_linear_profile_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(a:ScalarIndex)(f g:QuantumTest):
    sourcePair (inverseVolumeAction (GaussCoreDifferential.covariantMomentum (scalarDirection a)
      (correctedCompleteCore t ht ξ η f))) (correctedCompleteCore t ht ξ η g)=
      sourcePair (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
        (correctedProfileWeight t ht (1/3) 1 ξ η g):=by
  let c:=correctedCoefficient t ξ η
  let hc:=ClockPhiHeatCorrectedCovarianceSource.coefficient_smooth t ht ξ η
  let hf:=coeff_first t ξ η
  have hP:=LinearMap.congr_fun (actual_complete_profile_scalar_momentum c hc hf t ht (scalarDirection a) rfl) f
  change GaussCoreDifferential.covariantMomentum (scalarDirection a) (correctedCompleteCore t ht ξ η f)=
    correctedCompleteCore t ht ξ η (exponentialWeight c hc 1 (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)) at hP
  rw [hP,U_return t ht]
  rw [exp_forward t ht]
  have hp:=two_exp_pair t ht c hc hf 1 0
    (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)) g
  simp only[exp_zero,add_zero] at hp
  change sourcePair (correctedCompleteCore t ht ξ η
    (exponentialWeight c hc 1 (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))))
    (correctedCompleteCore t ht ξ η g)=
    sourcePair (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
      (correctedProfileWeight t ht (1/3) 1 ξ η g) at hp
  exact hp
private theorem quarter_profile_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(a:ScalarIndex)(f:QuantumTest):
    sourcePair (inverseVolumeAction (GaussCoreDifferential.covariantMomentum (scalarDirection a)
      (correctedCompleteCore t ht ξ η f))) (quarterColumn a (correctedCompleteCore t ht ξ η f))=
      sourcePair (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
        (correctedProfileWeight t ht (1/3) 0 ξ η (affineColumn a f))-
      ((3*inner ℝ (scalarBasis a) vacuum/4:ℝ):ℂ)*
        sourcePair (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
          (correctedProfileWeight t ht (1/3) 1 ξ η f):=by
  rw [quarter_split]
  simp only[LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply]
  have hr(u v w:QuantumTest)(c:ℂ):sourcePair u (v-c • w)=sourcePair u v-c*sourcePair u w:=by
    simp only[sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right]
  rw [hr,actual_scalar_affine_profile_pair,scalar_linear_profile_pair]

def quarterMean(t:ℝ)(ht:0<t)(f:QuantumTest):ℂ:=
  ∑a:ScalarIndex,
    (sourcePair (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
      (gaussianProfileWeight t ht (1/3) (affineColumn a f))-
    ((3*inner ℝ (scalarBasis a) vacuum/4:ℝ):ℂ)*
      sourcePair (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f))
        (gaussianProfileWeight t ht (2/9) f))

/-- Every native covariant momentum and forced quarter-vacuum column comes from the same complete K source. -/
theorem actual_quarter_pair_gaussian(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>quarterPair (correctedCompleteCore t ht x.1 x.2 f)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,quarterPair (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)=quarterMean t ht f:=by
  have h0(a:ScalarIndex):=
    actual_corrected_gaussian_weighted_source_pair t ht (1/3) 0
      (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)) (affineColumn a f)
  have h1(a:ScalarIndex):=
    actual_corrected_gaussian_weighted_source_pair t ht (1/3) 1
      (forwardUAction t ht.le (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)) f
  have hi(a:ScalarIndex):Integrable (fun x:ℝ×ℝ=>sourcePair
      (inverseVolumeAction (GaussCoreDifferential.covariantMomentum (scalarDirection a) (correctedCompleteCore t ht x.1 x.2 f)))
      (quarterColumn a (correctedCompleteCore t ht x.1 x.2 f))) (γ.prod γ):=by
    simp_rw [quarter_profile_pair]
    exact (h0 a).1.sub ((h1 a).1.const_mul _)
  constructor
  · exact integrable_finsetSum _ (fun a _=>hi a)
  · unfold quarterPair quarterMean
    rw [integral_finsetSum _ (fun a _=>hi a)]
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [quarter_profile_pair]
    rw [integral_sub (h0 a).1 ((h1 a).1.const_mul _),integral_const_mul,(h0 a).2,(h1 a).2]
    norm_num

/-- The original complete scalar current has its actual Gaussian source mean, without an H0-squared budget. -/
theorem actual_scalar_current_gaussian(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>(sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (scalarCurrentComplete (correctedCompleteCore t ht x.1 x.2 f))).im/2) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,(sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (scalarCurrentComplete (correctedCompleteCore t ht x.1 x.2 f))).im/2 ∂γ.prod γ)=
      16*(sourceTime 0)^2*(quarterMean t ht f).re:=by
  have h:=actual_quarter_pair_gaussian t ht f
  simp_rw [original_complete_scalar_form]
  refine ⟨h.1.re.const_mul _,?_⟩
  have hr:=Complex.reCLM.integral_comp_comm h.1
  simp only[Complex.reCLM_apply] at hr
  rw [integral_const_mul,hr,h.2]
end LowEnergy.FirstCurrentAdmissibleElectric.ScalarGaussian
