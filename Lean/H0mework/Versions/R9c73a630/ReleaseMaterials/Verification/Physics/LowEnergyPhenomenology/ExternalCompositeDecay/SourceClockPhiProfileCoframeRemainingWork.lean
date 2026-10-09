import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileCoframeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardPair
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatGainPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatSpinConnectionReturn
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeCovariantSquare
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForwardGeneratorTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiProfileCoframeRemainingWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiForwardGeneratorTransport SourceClockPhiActualCovarianceStep
open SourceClockPhiCompleteHeatGainPayment SourceClockPhiHeatSpinConnectionReturn ClockPhiConservativeHeatSource
open ClockPhiMatchedNoiseCore GaussCoframeForm SourceCoframeCovariantSquare
open SourceCoframeSpinConnection SourceClockPhiProfileCoframeReturn
open scoped Topology ContDiff InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev input(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):Op:=clockProfileAction c hc hinv 1
private abbrev profileHeat(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):Op:=
  sourceForwardCore t ht.le*input c hc hinv
private theorem input_source(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):
    sourceForwardCore t ht.le*input c hc hinv=profileHeat t ht c hc hinv:=rfl
private theorem input_point(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (f:QuantumTest)(z:SourceCoordinateSlice):
    input c hc hinv f z=(Real.exp ((25/2:ℝ)*c z):ℂ) • f (combinedMap (c z) z):=by
  change (Real.exp ((25/2:ℝ)*(1*c z)):ℂ) • f (combinedMap (1*c z) z)=_
  simp only [one_mul]
private abbrev constantAction(A:Matrix Mode Mode ℂ):Op:=
  GaussQuantumMultiplier.action (fun _=>A) (fun _=>contDiffAt_const)
private theorem input_constant(t:ℝ)(_ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(A:Matrix Mode Mode ℂ):
    Commute (input c hc hinv) (constantAction A):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change input c hc hinv (constantAction A f) z=GaussQuantumMultiplier.quantized A (input c hc hinv f z)
  rw [input_point,input_point]
  change (_:ℂ) • GaussQuantumMultiplier.quantized A (f _)=GaussQuantumMultiplier.quantized A ((_ :ℂ) • f _)
  exact (map_smul _ _ _).symm
private theorem scalar_constant(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(A:Matrix Mode Mode ℂ):
    Commute (multiply b hb) (constantAction A):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (b z:ℂ) • GaussQuantumMultiplier.quantized A (f z)=GaussQuantumMultiplier.quantized A ((b z:ℂ) • f z)
  exact (map_smul _ _ _).symm
private theorem gain_constant(t:ℝ)(A:Matrix Mode Mode ℂ):
    Commute (sourceGain (Real.sqrt t)) (constantAction A):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (gainProfile (Real.sqrt t) z:ℂ) • GaussQuantumMultiplier.quantized A (f z)=
    GaussQuantumMultiplier.quantized A ((gainProfile (Real.sqrt t) z:ℂ) • f z)
  exact (map_smul _ _ _).symm
private theorem complete_constant(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(A:Matrix Mode Mode ℂ)
    (hJ:Commute (sourceForwardCore t ht.le) (constantAction A)):
    Commute (profileCompleteCore t ht c hc hinv) (constantAction A):=by
  change Commute (profileHeat t ht c hc hinv*sourceGain (Real.sqrt t)) (constantAction A)
  rw [←input_source]
  have hN:input c hc hinv*constantAction A=constantAction A*input c hc hinv:=(input_constant t ht c hc hinv A).eq
  have hG:sourceGain (Real.sqrt t)*constantAction A=constantAction A*sourceGain (Real.sqrt t):=(gain_constant t A).eq
  change (sourceForwardCore t ht.le*input c hc hinv*sourceGain (Real.sqrt t))*constantAction A=
    constantAction A*(sourceForwardCore t ht.le*input c hc hinv*sourceGain (Real.sqrt t))
  calc
    _=sourceForwardCore t ht.le*input c hc hinv*(sourceGain (Real.sqrt t)*constantAction A):=by noncomm_ring
    _=sourceForwardCore t ht.le*input c hc hinv*(constantAction A*sourceGain (Real.sqrt t)):=by rw [hG]
    _=sourceForwardCore t ht.le*(input c hc hinv*constantAction A)*sourceGain (Real.sqrt t):=by noncomm_ring
    _=sourceForwardCore t ht.le*(constantAction A*input c hc hinv)*sourceGain (Real.sqrt t):=by rw [hN]
    _=(sourceForwardCore t ht.le*constantAction A)*input c hc hinv*sourceGain (Real.sqrt t):=by noncomm_ring
    _=(constantAction A*sourceForwardCore t ht.le)*input c hc hinv*sourceGain (Real.sqrt t):=by rw [hJ.eq]
    _=_:=by noncomm_ring

theorem actual_complete_current_commute(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(a:Fin 7):
    Commute (profileCompleteCore t ht c hc hinv) (GaussCoframeSpin.current a):=
  complete_constant t ht c hc hinv (GaussCoframeSpin.full a) (actual_forward_current_commute t ht.le a)
private theorem forward_number(t:ℝ)(ht:0≤t):Commute (sourceForwardCore t ht) GaussCoframeForm.number:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change forwardValue t (GaussCoframeForm.number f) z=
    GaussQuantumMultiplier.quantized (Matrix.diagonal (fun _:Mode=>(1:ℂ))) (forwardValue t f z)
  by_cases hz:18*t<GaussNativeEnergy.volume z
  · simp only [forwardValue,if_pos hz]
    let c:ℕ→ℂ:=fun N=>(Real.rpow (backwardRatio t z) ((N+3:ℝ)/2):ℂ)
    change GaussFockWeights.weight c (GaussQuantumMultiplier.quantized _ (f (backwardPoint t z)))=
      GaussQuantumMultiplier.quantized _ (GaussFockWeights.weight c (f (backwardPoint t z)))
    exact congrArg (fun T:FockFiber→L[ℂ]FockFiber=>T (f (backwardPoint t z)))
      (GaussQuantumMultiplier.weight_commute c (Matrix.diagonal (fun _:Mode=>(1:ℂ)))).eq
  · simp only [forwardValue,if_neg hz,map_zero]
private theorem complete_number(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):Commute (profileCompleteCore t ht c hc hinv) GaussCoframeForm.number:=by
  exact complete_constant t ht c hc hinv (Matrix.diagonal (fun _:Mode=>(1:ℂ))) (forward_number t ht.le)
private theorem heat_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(f g:QuantumTest):
    sourcePair (profileHeat t ht c hc hinv f) (profileHeat t ht c hc hinv g)=sourcePair f g:=by
  change sourcePair (sourceForwardCore t ht.le (input c hc hinv f))
    (sourceForwardCore t ht.le (input c hc hinv g))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair,clockProfileAction_pair]
private theorem price_smooth(t:ℝ)(ht:0<t)(p:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(forwardRatio t x)^p) z.val:=by
  have h:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact h.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne'
private def priceAction(t:ℝ)(ht:0<t)(p:ℝ):Op:=multiply (fun z=>(forwardRatio t z)^p) (price_smooth t ht p)
private def forwardAction(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):Op:=
  multiply (fun x=>b (forwardPoint t x)) (fun z=>by
    simpa only [Function.comp_def] using! (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))
private theorem input_forward_commute(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hbinv:∀s z,b (combinedMap s z)=b z):
    Commute (input c hc hinv) (forwardAction t ht b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change input c hc hinv (forwardAction t ht b hb f) z word=(b (forwardPoint t z):ℂ)*input c hc hinv f z word
  rw [input_point,input_point]
  change (_:ℂ)*((b (forwardPoint t (combinedMap (c z) z)):ℂ)*f _ word)=_
  have he:forwardPoint t (combinedMap (c z) z)=combinedMap (c z) (forwardPoint t z):=rfl
  rw [he,hbinv]
  simp only [PiLp.smul_apply,smul_eq_mul]
  ring
private theorem scalar_gain(t:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute (sourceGain (Real.sqrt t)) (multiply b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (_:ℂ) • ((_ :ℂ) • f z)=(_ :ℂ) • ((_ :ℂ) • f z)
  exact smul_comm _ _ _
private theorem scaled_multiply_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(hbinv:∀s z,b (combinedMap s z)=b z)
    (p:ℝ)(hscale:∀z:physicalChart,b (forwardPoint t z.val)=(forwardRatio t z.val)^p*b z.val):
    multiply b hb*profileCompleteCore t ht c hc hinv=profileCompleteCore t ht c hc hinv*(priceAction t ht p*multiply b hb):=by
  have hJ:=actual_forward_multiplier_transport t ht.le b hb
  change multiply b hb*sourceForwardCore t ht.le=sourceForwardCore t ht.le*forwardAction t ht b hb at hJ
  have hF:forwardAction t ht b hb=priceAction t ht p*multiply b hb:=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    by_cases hz:z∈physicalChart
    · change (b (forwardPoint t z):ℂ) • f z= (((forwardRatio t z)^p:ℝ):ℂ) • ((b z:ℂ) • f z)
      rw [hscale ⟨z,hz⟩,Complex.ofReal_mul,mul_smul]
    · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
      change (_:ℂ) • f z=(_ :ℂ) • ((_ :ℂ) • f z)
      rw [hf,smul_zero,smul_zero,smul_zero]
  have hN:=(input_forward_commute t ht c hc hinv b hb hbinv).eq
  have hG:sourceGain (Real.sqrt t)*forwardAction t ht b hb=forwardAction t ht b hb*sourceGain (Real.sqrt t):=by
    exact (scalar_gain t (fun x=>b (forwardPoint t x)) (fun z=>by
      simpa only [Function.comp_def] using! (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))).eq
  change multiply b hb*(profileHeat t ht c hc hinv*sourceGain (Real.sqrt t))=_
  rw [←input_source]
  calc
    _=(multiply b hb*sourceForwardCore t ht.le)*input c hc hinv*sourceGain (Real.sqrt t):=by noncomm_ring
    _=(sourceForwardCore t ht.le*forwardAction t ht b hb)*input c hc hinv*sourceGain (Real.sqrt t):=by rw [hJ]
    _=(sourceForwardCore t ht.le*(forwardAction t ht b hb*input c hc hinv))*sourceGain (Real.sqrt t):=by noncomm_ring
    _=(sourceForwardCore t ht.le*(input c hc hinv*forwardAction t ht b hb))*sourceGain (Real.sqrt t):=by rw [←hN]
    _=(sourceForwardCore t ht.le*input c hc hinv)*(forwardAction t ht b hb*sourceGain (Real.sqrt t)):=by noncomm_ring
    _=(sourceForwardCore t ht.le*input c hc hinv)*(sourceGain (Real.sqrt t)*forwardAction t ht b hb):=by rw [←hG]
    _=(sourceForwardCore t ht.le*input c hc hinv*sourceGain (Real.sqrt t))*forwardAction t ht b hb:=by noncomm_ring
    _=profileCompleteCore t ht c hc hinv*(priceAction t ht p*multiply b hb):=by rw [hF];rfl
private theorem inverse_scale(t:ℝ)(ht:0<t)(z:physicalChart):
    GaussCoframeForm.inverseVolume (forwardPoint t z.val)=(forwardRatio t z.val)^(-1:ℝ)*GaussCoframeForm.inverseVolume z.val:=by
  unfold GaussCoframeForm.inverseVolume
  rw [forward_volume t ht.le z,Real.rpow_neg_one]
  unfold forwardRatio
  field_simp [(volume_pos z).ne',show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z]]
private theorem inverse_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):
    multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*profileCompleteCore t ht c hc hinv=
      profileCompleteCore t ht c hc hinv*(priceAction t ht (-1)*multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth):=
  scaled_multiply_transport t ht c hc hinv _ _ (fun _ _=>rfl) (-1) (inverse_scale t ht)
private theorem gain_squared_price(t:ℝ)(ht:0<t)(p:ℝ):
    sourceGain (Real.sqrt t)*(sourceGain (Real.sqrt t)*priceAction t ht p)=priceAction t ht (p+1/3):=by
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
    have hh:gainProfile (Real.sqrt t) z*gainProfile (Real.sqrt t) z*(forwardRatio t z)^p=(forwardRatio t z)^(p+1/3):=by
      rw [←pow_two,hg,←Real.rpow_add hr,add_comm]
    apply PiLp.ext
    intro word
    change (gainProfile (Real.sqrt t) z:ℂ)*((gainProfile (Real.sqrt t) z:ℂ)*((((forwardRatio t z)^p:ℝ):ℂ)*f z word))=
      (((forwardRatio t z)^(p+1/3):ℝ):ℂ)*f z word
    have hc:=congrArg Complex.ofReal hh
    simp only [Complex.ofReal_mul] at hc
    rw [←mul_assoc,←mul_assoc,hc]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (_:ℂ) • ((_ :ℂ) • ((_ :ℂ) • f z))=(_ :ℂ) • f z
    rw [hf,smul_zero,smul_zero,smul_zero,smul_zero]
private theorem gain_pair(e:ℝ)(f g:QuantumTest):
    sourcePair (sourceGain e f) g=sourcePair f (sourceGain e g):=by
  have hs(z:physicalChart):ContDiffAt ℝ ∞ (gainProfile e) z.val:=by
    have h:ContDiffAt ℝ ∞ (forwardRatio (e^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact h.rpow_const_of_ne (forward_ratio_pos (e^2) (sq_nonneg _) z).ne'
  change sourcePair (multiply (gainProfile e) hs f) g=sourcePair f (multiply (gainProfile e) hs g)
  exact (multiply_pair _ _ f g).symm
private theorem paired_return(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(p:ℝ)(X:Op)
    (h:X*profileCompleteCore t ht c hc hinv=profileCompleteCore t ht c hc hinv*(priceAction t ht p*X))(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc hinv f) (X (profileCompleteCore t ht c hc hinv g))=
      sourcePair f (priceAction t ht (p+1/3) (X g)):=by
  have hx:=LinearMap.congr_fun h g
  change X (profileCompleteCore t ht c hc hinv g)=profileCompleteCore t ht c hc hinv (priceAction t ht p (X g)) at hx
  rw [hx]
  change sourcePair (profileHeat t ht c hc hinv (sourceGain (Real.sqrt t) f))
    (profileHeat t ht c hc hinv (sourceGain (Real.sqrt t) (priceAction t ht p (X g))))=_
  rw [heat_pair,gain_pair]
  have hg:=LinearMap.congr_fun (gain_squared_price t ht p) (X g)
  exact congrArg (sourcePair f) hg
private theorem sandwich_transport(K W S M:Op)(hS:S*K=K*S)(hW:S*W=W*S)(hM:M*K=K*(W*M)):
    (S*M*S)*K=K*(W*(S*M*S)):=by
  calc
    _=S*M*(S*K):=by noncomm_ring
    _=S*M*(K*S):=by rw [hS]
    _=S*(M*K)*S:=by noncomm_ring
    _=S*(K*(W*M))*S:=by rw [hM]
    _=(S*K)*W*M*S:=by noncomm_ring
    _=(K*S)*W*M*S:=by rw [hS]
    _=K*(S*W)*(M*S):=by noncomm_ring
    _=K*(W*S)*(M*S):=by rw [hW]
    _=K*(W*(S*M*S)):=by noncomm_ring
private theorem spin_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):
    spinRemainder*profileCompleteCore t ht c hc hinv=profileCompleteCore t ht c hc hinv*(priceAction t ht (-1)*spinRemainder):=by
  unfold spinRemainder
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun X:Op=>(residualWeight a:ℂ) • X)
  exact sandwich_transport _ _ _ _ (actual_complete_current_commute t ht c hc hinv a).symm.eq
    (scalar_constant _ _ (GaussCoframeSpin.full a)).symm.eq (inverse_transport t ht c hc hinv)
private theorem mix_transport(K W S M:Op)(hS:S*K=K*S)(hW:S*W=W*S)(hM:M*K=K*(W*M)):
    (S*M+M*S)*K=K*(W*(S*M+M*S)):=by
  have h1:(S*M)*K=K*(W*(S*M)):=by
    calc _=S*(M*K):=by noncomm_ring
         _=S*(K*(W*M)):=by rw [hM]
         _=(S*K)*(W*M):=by noncomm_ring
         _=(K*S)*(W*M):=by rw [hS]
         _=K*(S*W)*M:=by noncomm_ring
         _=K*(W*S)*M:=by rw [hW]
         _=_:=by noncomm_ring
  have h2:(M*S)*K=K*(W*(M*S)):=by
    calc _=M*(S*K):=by noncomm_ring
         _=M*(K*S):=by rw [hS]
         _=(M*K)*S:=by noncomm_ring
         _=(K*(W*M))*S:=by rw [hM]
         _=_:=by noncomm_ring
  linear_combination (norm:=noncomm_ring) h1+h2
private theorem number_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):
    numberShift*profileCompleteCore t ht c hc hinv=profileCompleteCore t ht c hc hinv*(priceAction t ht (-1)*numberShift):=by
  have hM:=scaled_multiply_transport t ht c hc hinv numberCoefficient numberCoefficient_smooth (fun _ _=>rfl) (-1)
    (fun z=>by simp only [numberCoefficient,inverse_scale t ht z];ring)
  change ((1/2:ℂ) • (GaussCoframeForm.number*multiply numberCoefficient numberCoefficient_smooth+
    multiply numberCoefficient numberCoefficient_smooth*GaussCoframeForm.number))*profileCompleteCore t ht c hc hinv=
      profileCompleteCore t ht c hc hinv*(priceAction t ht (-1)*((1/2:ℂ) •
        (GaussCoframeForm.number*multiply numberCoefficient numberCoefficient_smooth+multiply numberCoefficient numberCoefficient_smooth*GaussCoframeForm.number)))
  simp only [smul_mul_assoc,mul_smul_comm]
  apply congrArg (fun X:Op=>(1/2:ℂ) • X)
  exact mix_transport _ _ _ _ (complete_number t ht c hc hinv).symm.eq
    (scalar_constant _ _ (Matrix.diagonal (fun _:Mode=>(1:ℂ)))).symm.eq hM
private theorem volume_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):
    multiply volumePotential volumePotential_smooth*profileCompleteCore t ht c hc hinv=
      profileCompleteCore t ht c hc hinv*(priceAction t ht 1*multiply volumePotential volumePotential_smooth):=by
  apply scaled_multiply_transport t ht c hc hinv _ _ (fun _ _=>rfl) 1
  intro z
  unfold volumePotential
  rw [forward_volume t ht.le z,Real.rpow_one]
  unfold forwardRatio
  field_simp [(volume_pos z).ne']

private theorem beta_smooth(i:Fin 6)(a:Fin 3)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun w:SourceCoordinateSlice=>spinConnection w.1 i a) z.val:=by
  have hv:=(volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at hv
  have h0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
  have h2:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  have h5:=(mul_ne_zero_iff.mp hv).2
  fin_cases i <;> fin_cases a <;> simp [spinConnection] <;> fun_prop (disch:=aesop)
private theorem real_smul_fiber(c:ℝ)(v:FockFiber):c • v=(c:ℂ) • v:=by
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm
private theorem connection_columns(i:Fin 6):
    SourceCoframeCovariantAction.connectionAction i=∑a:Fin 3,
      multiply (fun z=>spinConnection z.1 i a) (beta_smooth i a)*
        GaussCoframeSpin.current ⟨3+a.val,by omega⟩:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (connectionFiber i z) (f z)=_
  simp only [connectionFiber,sum_apply,smul_apply,real_smul_fiber,LinearMap.sum_apply,Module.End.mul_apply]
  rfl

theorem actual_complete_connection_return(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(i:Fin 6):
    SourceCoframeCovariantAction.connectionAction i*profileCompleteCore t ht c hc hinv=
      profileCompleteCore t ht c hc hinv*(multiply (fun z=>(forwardRatio t z)^(-1/3:ℝ))
        (price_smooth t ht (-1/3))*SourceCoframeCovariantAction.connectionAction i):=by
  change SourceCoframeCovariantAction.connectionAction i*profileCompleteCore t ht c hc hinv=
    profileCompleteCore t ht c hc hinv*(priceAction t ht (-1/3)*SourceCoframeCovariantAction.connectionAction i)
  rw [connection_columns]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  let S:Op:=GaussCoframeSpin.current ⟨3+a.val,by omega⟩
  let M:Op:=multiply (fun z=>spinConnection z.1 i a) (beta_smooth i a)
  have hM:M*profileCompleteCore t ht c hc hinv=profileCompleteCore t ht c hc hinv*(priceAction t ht (-1/3)*M):=by
    apply scaled_multiply_transport t ht c hc hinv _ _ (fun _ _=>rfl) (-1/3)
    intro z
    have hr:=forward_ratio_pos t ht.le z
    have hs:=actual_spin_connection_scale ((forwardRatio t z.val)^(1/3:ℝ))
      (Real.rpow_pos_of_pos hr _) z i a
    change spinConnection (((forwardRatio t z.val)^(1/3:ℝ)) • z.val.1) i a=_
    rw [hs,←Real.rpow_neg hr.le]
    congr 2
    norm_num
  have hS:S*profileCompleteCore t ht c hc hinv=profileCompleteCore t ht c hc hinv*S:=
    (actual_complete_current_commute t ht c hc hinv ⟨3+a.val,by omega⟩).symm.eq
  change (M*S)*profileCompleteCore t ht c hc hinv=profileCompleteCore t ht c hc hinv*(priceAction t ht (-1/3)*(M*S))
  calc
    _=M*(S*profileCompleteCore t ht c hc hinv):=by noncomm_ring
    _=M*(profileCompleteCore t ht c hc hinv*S):=by rw [hS]
    _=(M*profileCompleteCore t ht c hc hinv)*S:=by noncomm_ring
    _=(profileCompleteCore t ht c hc hinv*(priceAction t ht (-1/3)*M))*S:=by rw [hM]
    _=_:=by noncomm_ring

theorem actual_complete_spin_remainder_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc hinv f) (spinRemainder (profileCompleteCore t ht c hc hinv g))=
      sourcePair f (multiply (fun z=>(forwardRatio t z)^(-2/3:ℝ)) (price_smooth t ht (-2/3)) (spinRemainder g)):=by
  have h:=paired_return t ht c hc hinv (-1) spinRemainder (spin_transport t ht c hc hinv) f g
  simpa only [show (-1:ℝ)+1/3= -2/3 by norm_num,priceAction] using h

theorem actual_complete_number_shift_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc hinv f) (numberShift (profileCompleteCore t ht c hc hinv g))=
      sourcePair f (multiply (fun z=>(forwardRatio t z)^(-2/3:ℝ)) (price_smooth t ht (-2/3)) (numberShift g)):=by
  have h:=paired_return t ht c hc hinv (-1) numberShift (number_transport t ht c hc hinv) f g
  simpa only [show (-1:ℝ)+1/3= -2/3 by norm_num,priceAction] using h

theorem actual_complete_coframe_volume_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc hinv f)
      (multiply volumePotential volumePotential_smooth (profileCompleteCore t ht c hc hinv g))=
      sourcePair f (multiply (fun z=>(forwardRatio t z)^(4/3:ℝ)) (price_smooth t ht (4/3))
        (multiply volumePotential volumePotential_smooth g)):=by
  have h:=paired_return t ht c hc hinv 1 (multiply volumePotential volumePotential_smooth) (volume_transport t ht c hc hinv) f g
  simpa only [show (1:ℝ)+1/3=4/3 by norm_num,priceAction] using h

theorem profileFirstInvariant(c:SourceCoordinateSlice→ℝ)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (u:ℝ)(z:SourceCoordinateSlice):c (combinedMap u z)=c z:=hfirst _ _ rfl

theorem actual_profile_complete_current_commute(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(a:Fin 7):
    Commute (profileCompleteCore t ht c hc (profileFirstInvariant c hfirst))
      (GaussCoframeSpin.current a):=
  actual_complete_current_commute t ht c hc (profileFirstInvariant c hfirst) a

theorem actual_profile_complete_connection_return(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(i:Fin 6):
    SourceCoframeCovariantAction.connectionAction i*
      profileCompleteCore t ht c hc (profileFirstInvariant c hfirst)=
      profileCompleteCore t ht c hc (profileFirstInvariant c hfirst)*
        (multiply (fun z=>(forwardRatio t z)^(-1/3:ℝ))
          (price_smooth t ht (-1/3))*SourceCoframeCovariantAction.connectionAction i):=
  actual_complete_connection_return t ht c hc (profileFirstInvariant c hfirst) i

theorem actual_profile_complete_spin_remainder_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileFirstInvariant c hfirst) f)
      (spinRemainder (profileCompleteCore t ht c hc (profileFirstInvariant c hfirst) g))=
      sourcePair f (multiply (fun z=>(forwardRatio t z)^(-2/3:ℝ))
        (price_smooth t ht (-2/3)) (spinRemainder g)):=
  actual_complete_spin_remainder_pair t ht c hc (profileFirstInvariant c hfirst) f g

theorem actual_profile_complete_number_shift_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileFirstInvariant c hfirst) f)
      (numberShift (profileCompleteCore t ht c hc (profileFirstInvariant c hfirst) g))=
      sourcePair f (multiply (fun z=>(forwardRatio t z)^(-2/3:ℝ))
        (price_smooth t ht (-2/3)) (numberShift g)):=
  actual_complete_number_shift_pair t ht c hc (profileFirstInvariant c hfirst) f g

theorem actual_profile_complete_coframe_volume_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileFirstInvariant c hfirst) f)
      (multiply volumePotential volumePotential_smooth
        (profileCompleteCore t ht c hc (profileFirstInvariant c hfirst) g))=
      sourcePair f (multiply (fun z=>(forwardRatio t z)^(4/3:ℝ))
        (price_smooth t ht (4/3))
        (multiply volumePotential volumePotential_smooth g)):=
  actual_complete_coframe_volume_pair t ht c hc (profileFirstInvariant c hfirst) f g
end LowEnergy.SourceClockPhiProfileCoframeRemainingWork
