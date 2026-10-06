import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiMatchedElectricSource
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRenormalizedSecondGreen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiMatchedDiffusionSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceGaugeRadialCurrent SourceGaugeRadialPair SourceScalarGaugeScale
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedElectricSource
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockYukawaCubicCurrent SourceClockReflectedForm SourceCoframeBlockHardy SourceClockAcceleration
open SourceCoframeVolumeCurrent SourceCoframeDilation SourcePhysicalHamiltonianSquare
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceLocalizedInverseFormPayment
open Filter
open scoped ContDiff InnerProductSpace RealInnerProductSpace Topology
abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev a:End:=inverseRootAction
private abbrev H0:End:=diagonalAction
private abbrev A:End:=combinedConjugate
private abbrev D:End:=combinedGenerator
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev Gauge:End:=SourceGaugeScaleTransport.generator
private abbrev Dc:End:=dilation
private abbrev n:ℝ:=sourceTime 0
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev T (m ell:ℕ):End:=phiThetaAction m ell
attribute [local irreducible] sourcePair embed diagonalAction compressionCore defectAction resolventCore finiteResolvent
private theorem pair_add_l (f g h:QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]

private theorem pair_add_r (f g h:QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]

private theorem pair_sub_l (f g h:QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]

private theorem pair_sub_r (f g h:QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem pair_smul_l (c:ℂ)(f g:QuantumTest) : sourcePair (c • f) g=(starRingEnd ℂ c)*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left]

private theorem pair_smul_r (c:ℂ)(f g:QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem self_pair (f:QuantumTest) : sourcePair f f=(‖embed f‖^2:ℂ) := by
  simpa only [sourcePair,Complex.ofReal_pow] using!
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)

private theorem flow_pair_generator (flow:ℝ → End)(G:End)
    (hzero:∀f,flow 0 f=f)
    (hpair:∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g:QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=fun _=>inner ℂ (embed f) (embed g) :=
    funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq

private theorem phi_pair (f g:QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g

private theorem gauge_pair (f g:QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g

private theorem combined_pair (f g:QuantumTest) :
    sourcePair f (combinedGenerator g)= -sourcePair (combinedGenerator f) g := by
  simp only [combinedGenerator,LinearMap.sub_apply,pair_sub_l,pair_sub_r,phi_pair,gauge_pair]
  ring

private theorem weight_pair (f g:QuantumTest) : sourcePair f (U g)=sourcePair (U f) g :=
  multiply_pair _ _ f g

private theorem real_commute (c d:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)

private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

private theorem radius_inverse : r*S=(1:End):=(real_commute _ _ _ _).eq.symm.trans inverse_radius

private theorem theta_commute {A:End}(hA:Commute A S)(m ell:ℕ):Commute A (T m ell):=
  (((Commute.one_right A).sub_right hA).pow_right (m+1)).sub_right
    (((Commute.one_right A).sub_right hA).pow_right (ell+1))

private theorem phi_inverse_core(f:QuantumTest):phiInverseBounded (embed f)=embed (S f):=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f

private theorem phi_inverse_norm:‖phiInverseBounded‖ ≤ 1:=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private theorem normalized_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=S (phiResponseCore m ell F z hz g) := by
  have hc(f:QuantumTest):S (T m ell f)=T m ell (S f):=
    LinearMap.congr_fun (theta_commute (Commute.refl S) m ell).eq f
  have hi(f:QuantumTest):S (r f)=f:=LinearMap.congr_fun inverse_radius f
  change T m ell (resolventCore F z hz (coreEquiv.symm g))-
    S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))=
    S (T m ell (r (resolventCore F z hz (coreEquiv.symm g))-
      resolventCore F z hz (r (coreEquiv.symm g))))
  simp only [map_sub,hc,hi]

private theorem source_step (F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    compressionCore F (resolventCore F z hz f)=f+z • resolventCore F z hz f := by
  have he (u:QuantumTest):embed (compressionCore F u)=GaussGradedCompression.compression F (embed u) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr (u:QuantumTest):embed (resolventCore F z hz u)=finiteResolvent F z (embed u) := by
    unfold resolventCore SourceScalarPositiveBulkWard.state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h:=congrArg (fun A:H  →L[ℂ] H=>A (embed f))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  apply embed_injective
  simp only [he,hr,map_add,map_smul]
  have hf:FullYSourceResolventGraphSplice.resolvent (GaussGradedCompression.compression F) z=
      finiteResolvent F z := by unfold finiteResolvent;rfl
  rw [hf] at h
  change (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z (embed f))=embed f at h
  simp only [sub_apply,smul_apply,one_apply_eq_self] at h
  linear_combination (norm:=module) h

private theorem full_source (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    diagonalAction (normalizedState m ell F z hz g)=normalizedForcing m ell F z hz g+
      z • normalizedState m ell F z hz g := by
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let h:=resolventCore F z hz (r (coreEquiv.symm g))
  have hq:diagonalAction q=coreEquiv.symm g+z • q+defectAction F q := by
    have hx:=source_step F z hz (coreEquiv.symm g)
    change compressionCore F q=coreEquiv.symm g+z • q at hx
    rw [←hx]
    simp only [defectAction,LinearMap.sub_apply]
    module
  have hh:diagonalAction h=r (coreEquiv.symm g)+z • h+defectAction F h := by
    have hx:=source_step F z hz (r (coreEquiv.symm g))
    change compressionCore F h=r (coreEquiv.symm g)+z • h at hx
    rw [←hx]
    simp only [defectAction,LinearMap.sub_apply]
    module
  have htr:(S*T m ell)*r=T m ell := by
    rw [(theta_commute (Commute.refl S) m ell).eq, mul_assoc,inverse_radius,mul_one]
  have ht:=LinearMap.congr_fun htr (coreEquiv.symm g)
  unfold normalizedForcing normalizedState bracket
  change diagonalAction (T m ell q-(S*T m ell) h)=
    ((diagonalAction*(T m ell)-(T m ell)*diagonalAction) q-
      (diagonalAction*(S*T m ell)-(S*T m ell)*diagonalAction) h+
      T m ell (defectAction F q)-(S*T m ell) (defectAction F h))+z • (T m ell q-(S*T m ell) h)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hq,hh,map_add,map_smul] at ht ⊢
  linear_combination (norm:=module) -ht

private theorem weight_combined : Commute U D := by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator U
  have hg:=SourceGaugeScaleTransport.generator_commutator U
  rw [SourceScalarInverseBulk.inverse_phi] at hp
  rw [SourceScalarInverseBulk.inverse_gauge] at hg
  change U*(Phi-Gauge)=(Phi-Gauge)*U
  linear_combination (norm:=noncomm_ring) -hp+hg
private theorem weighted_pair (f g:QuantumTest):sourcePair f (U (D g))= -sourcePair (U (D f)) g := by
  rw [weight_pair,combined_pair]
  have hc:=LinearMap.congr_fun weight_combined.eq f
  change U (D f)=D (U f) at hc
  rw [←hc]
private theorem pair_star(f g:QuantumTest):starRingEnd ℂ (sourcePair f g)=sourcePair g f := by
  unfold sourcePair
  exact inner_conj_symm _ _
private theorem pair_sym_re(f g:QuantumTest):(sourcePair f g).re=(sourcePair g f).re := by
  rw [←pair_star,Complex.conj_re]
private theorem weighted_self_real(f:QuantumTest):(sourcePair (U (D f)) f).re=0 := by
  have h:=congrArg Complex.re (weighted_pair f f)
  rw [Complex.neg_re,pair_sym_re f (U (D f))] at h
  linarith
private def phiScale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (z.1,r • (vacuumSlice+z.2.1)-vacuumSlice,z.2.2)
private theorem phi_scale_one (z : SourceCoordinateSlice) : phiScale 1 z=z := by
  simp [phiScale]
private theorem phi_scale_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => phiScale r z) (phiEuler z) 1 := by
  simpa only [phiScale,phiEuler,id_eq,one_smul] using!
    (hasDerivAt_const (1 : ℝ) z.1).prodMk
      ((((hasDerivAt_id (1 : ℝ)).smul_const (vacuumSlice+z.2.1)).sub_const vacuumSlice).prodMk
        (hasDerivAt_const (1 : ℝ) z.2.2))


private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 1) (hz : γ 1=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 1 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem euler_multiplier (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (flow : ℝ → SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (hg : ∀ z,HasDerivAt (fun r => flow r z) (e z) 1) (h1 : ∀ z,flow 1 z=z)
    (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (hinv : ∀ r z,B (flow r z)=B z) : E*A-A*E=0 := by
  apply sub_eq_zero.mpr
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change E (A f) z=A (E f) z
  rw [hE,law,hE]
  have h := invariant_derivative (E := SourceCoordinateSlice) (V := FockFiber)
    ((B z).restrictScalars ℝ) f (A f) (fun r => flow r z) z (e z)
    (hg z) (h1 z) ((f.contDiff.differentiable (by simp)) z) (((A f).contDiff.differentiable (by simp)) z)
    (fun r => by rw [law,hinv]; rfl)
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using! h

private theorem root_commute:Commute a D := by
  have hp:phiEulerAction*a-a*phiEulerAction=0:=
    euler_multiplier phiEulerAction phiEuler phiScale phi_euler_apply phi_scale_derivative phi_scale_one a
      (fun z=>(inverseRootVolume z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) (fun _ _=>rfl) (fun _ _=>rfl)
  have hg:gaugeEulerAction*a-a*gaugeEulerAction=0:=
    euler_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply (fun z=>gauge_scale_derivative z 1) gauge_scale_one a
      (fun z=>(inverseRootVolume z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) (fun _ _=>rfl) (fun _ _=>rfl)
  change a*(Phi-Gauge)=(Phi-Gauge)*a
  unfold Phi Gauge SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator
  linear_combination (norm:=noncomm_ring) -hp+hg
private theorem root_pair(f g:QuantumTest):sourcePair f (a g)=sourcePair (a f) g:=multiply_pair _ _ f g
private theorem conjugate_pair(f g:QuantumTest):sourcePair f (A g)= -sourcePair (A f) g:=by
  change sourcePair f (a (D g))= -sourcePair (a (D f)) g
  rw [root_pair,combined_pair]
  have h:=LinearMap.congr_fun root_commute.eq f
  change a (D f)=D (a f) at h
  rw [←h]
private theorem lapse_nonzero:((sourceTime 0:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos.ne')
private theorem inverse_dilation:Dc*U-U*Dc=(2*Complex.I) • U := by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=(-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring
def driftClock:End:=matchedColumn+(3:ℂ) • U
def diffusionDrift:End:=A*A-(3:ℂ) • driftClock
def diffusionDriftTranspose:End:=A*A+(3:ℂ) • driftClock
def diffusionCurrent(X:End):End:=diffusionDriftTranspose*X+X*diffusionDrift-(2:ℂ) • (A*X*A)
def completeCurrent(X:End):End:=diffusionCurrent X+(3:ℂ) • (U*X+X*U)
private theorem drift_clock:driftClock=U*D+(4*Complex.I/(n:ℂ)) • clockCurrent := by
  have h:U*Dc=Dc*U-(2*Complex.I) • U:=by linear_combination (norm:=module) -inverse_dilation
  have hn:(n:ℂ)≠0:=lapse_nonzero
  have hc:(4*Complex.I/(n:ℂ))*(3*(n:ℂ)/8)=3*Complex.I/2:=by field_simp [hn];ring
  have hi:(3*Complex.I/2)*(2*Complex.I)=(-3:ℂ):=by
    calc _=3*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [original_clock_current]
  change U*D+(3*Complex.I) • (Dc*U)+(3:ℂ) • U=
    U*D+(4*Complex.I/(n:ℂ)) • ((3*(n:ℂ)/8) • (U*Dc+Dc*U))
  rw [smul_smul,hc,h]
  simp only [smul_add,smul_sub,smul_smul,hi]
  module
private theorem drift_clock_pair(f g:QuantumTest):sourcePair f (driftClock g)= -sourcePair (driftClock f) g:=by
  rw [drift_clock]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r]
  rw [weighted_pair,SourceClockFixedInputSeed.original_clock_current_pair]
  have hc:(starRingEnd ℂ (4*Complex.I/(n:ℂ)))= -(4*Complex.I/(n:ℂ)):=by
    simp only [map_div₀,map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal]
    ring
  rw [hc]
  ring
private theorem diffusion_source(X:End):diffusionCurrent X=bracket A (bracket A X)+(3:ℂ) • bracket driftClock X:=by
  unfold diffusionCurrent diffusionDrift diffusionDriftTranspose bracket
  simp only [add_mul,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_sub]
  noncomm_ring
  module
private theorem diffusion_conservative:diffusionCurrent (1:End)=0:=by
  rw [diffusion_source]
  simp only [bracket,mul_one,one_mul,sub_self,mul_zero,zero_mul,smul_zero,add_zero]
private theorem diffusion_carre(X:End):diffusionCurrent (X*X)-diffusionCurrent X*X-X*diffusionCurrent X=
    (2:ℂ) • (bracket A X*bracket A X):=by
  simp only [diffusion_source,bracket,mul_add,add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
  noncomm_ring
  module
private theorem current_pair(X:End)(hX:GaussCoframeForm.Paired X X)(f g:QuantumTest):
    sourcePair f (bracket A X g)=sourcePair (bracket A X f) g:=by
  change sourcePair f (A (X g)-X (A g))=sourcePair (A (X f)-X (A f)) g
  rw [pair_sub_l,pair_sub_r,conjugate_pair,hX,hX,conjugate_pair]
  ring
private theorem actual_carre(F:Index)(f:QuantumTest):
    (sourcePair f ((diffusionCurrent (H0*H0)-diffusionCurrent H0*H0-H0*diffusionCurrent H0) f)).re=
      2*‖embed (bracket A (compressionCore F) f+bracket A (defectAction F) f)‖^2:=by
  rw [diffusion_carre]
  change (sourcePair f ((2:ℂ) • (bracket A H0 (bracket A H0 f)))).re=_
  rw [pair_smul_r,current_pair H0 diagonalAction_pair]
  have hH:H0=compressionCore F+defectAction F:=by unfold H0 defectAction;abel
  have he:bracket A H0=bracket A (compressionCore F)+bracket A (defectAction F):=by
    rw [hH];unfold bracket;noncomm_ring
  rw [he]
  rw [self_pair]
  norm_num only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  norm_cast
/-- The original positive-time volume clock, extended constantly to negative times only for the zero jet. -/
def noiseRow(s:ℝ)(x:physicalChart):ℝ:=(Real.sqrt (GaussNativeEnergy.volume x.val+18*max s 0))⁻¹
def noiseKernel(t:ℝ)(x y:physicalChart):ℝ:=2*∫s in (0:ℝ)..t,noiseRow s x*noiseRow s y
private theorem noise_continuous(x:physicalChart):Continuous (fun s:ℝ=>noiseRow s x):=by
  unfold noiseRow
  apply Continuous.inv₀
  · fun_prop
  · intro s
    exact (Real.sqrt_pos.mpr (by have hv:=volume_pos x;positivity)).ne'
private theorem noise_kernel_zero_jet(x y:physicalChart):
    HasDerivAt (fun t:ℝ=>noiseKernel t x y)
      (2*inverseRootVolume x.val*inverseRootVolume y.val) 0 := by
  have hc:Continuous (fun s:ℝ=>noiseRow s x*noiseRow s y):=(noise_continuous x).mul (noise_continuous y)
  have h:=intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  simpa only [noiseKernel,noiseRow,max_self,mul_zero,add_zero,mul_assoc,inverseRootVolume] using h.const_mul 2
private theorem real_kernel_gram{ι:Type*}[Fintype ι](t:ℝ)(x:ι → physicalChart)(c:ι → ℝ):
    (∑i,∑j,c i*(noiseKernel t (x i) (x j)*c j))=
      2*∫s in (0:ℝ)..t,(∑i,c i*noiseRow s (x i))^2 := by
  have hint(i j:ι):IntervalIntegrable (fun s:ℝ=>c i*(noiseRow s (x i)*noiseRow s (x j))*c j)
      MeasureTheory.volume 0 t:=
    ((continuous_const.mul ((noise_continuous (x i)).mul (noise_continuous (x j)))).mul continuous_const).intervalIntegrable 0 t
  have his(i:ι):IntervalIntegrable (fun s:ℝ=>∑j,c i*(noiseRow s (x i)*noiseRow s (x j))*c j)
      MeasureTheory.volume 0 t:=by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun j _=>
      (continuous_const.mul ((noise_continuous (x i)).mul (noise_continuous (x j)))).mul continuous_const)
  have he:(fun s:ℝ=>(∑i,c i*noiseRow s (x i))^2)=
      fun s:ℝ=>∑i,∑j,c i*(noiseRow s (x i)*noiseRow s (x j))*c j:=by
    funext s
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring
  rw [he,intervalIntegral.integral_finsetSum (fun i _=>his i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _=>hint _ j),
    intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
  unfold noiseKernel
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring
private theorem real_kernel_nonnegative{ι:Type*}[Fintype ι](t:ℝ)(ht:0≤ t)(x:ι → physicalChart)(c:ι → ℝ):
    0≤∑i,∑j,c i*(noiseKernel t (x i) (x j)*c j):=by
  rw [real_kernel_gram]
  exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg_of_forall ht (fun _=>sq_nonneg _))
private theorem complex_kernel_nonnegative{ι:Type*}[Fintype ι](t:ℝ)(ht:0≤ t)(x:ι → physicalChart)(c:ι → ℂ):
    0≤(∑i,∑j,star (c i)*((noiseKernel t (x i) (x j):ℝ):ℂ)*c j).re:=by
  have he:(∑i,∑j,star (c i)*((noiseKernel t (x i) (x j):ℝ):ℂ)*c j).re=
      (∑i,∑j,(c i).re*(noiseKernel t (x i) (x j)*(c j).re))+
      (∑i,∑j,(c i).im*(noiseKernel t (x i) (x j)*(c j).im)):=by
    simp only [Complex.re_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _
    simp only [Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_add]
    ring
  rw [he]
  exact add_nonneg (real_kernel_nonnegative t ht x (fun i=>(c i).re))
    (real_kernel_nonnegative t ht x (fun i=>(c i).im))

private theorem anti_current_source(B:End)
    (hB:∀f g:QuantumTest,sourcePair f (B g)= -sourcePair (B f) g)
    (f w:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    (sourcePair w (bracket B H0 w)).re=
      -2*(sourcePair f (B w)).re+2*z.im*(sourcePair (B w) w).im := by
  change (sourcePair w (B (H0 w)-H0 (B w))).re=_
  rw [pair_sub_r,hB w (H0 w),diagonalAction_pair w (B w),he]
  simp only [pair_add_l,pair_add_r,pair_smul_l,pair_smul_r]
  rw [hB w w]
  simp only [Complex.sub_re,Complex.neg_re,Complex.add_re,Complex.mul_re,
    Complex.conj_re,Complex.conj_im,Complex.neg_im]
  rw [pair_sym_re (B w) f]
  ring
private theorem weight_current_source(f w:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    (sourcePair w ((U*H0+H0*U) w)).re=
      2*(sourcePair f (U w)).re+2*z.re*(sourcePair w (U w)).re := by
  change (sourcePair w (U (H0 w)+H0 (U w))).re=_
  rw [pair_add_r,weight_pair w (H0 w),diagonalAction_pair w (U w),he]
  simp only [pair_add_l,pair_add_r,pair_smul_l,pair_smul_r]
  rw [weight_pair w w]
  simp only [Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  rw [pair_sym_re (U w) f]
  ring
private theorem complete_source(f w:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    (sourcePair w (completeCurrent H0 w)).re=
      (sourcePair w (bracket A (bracket A H0) w)).re-
        6*(sourcePair f (matchedTester w)).re+6*z.re*(sourcePair w (U w)).re+
        6*z.im*(sourcePair (matchedColumn w) w).im := by
  unfold completeCurrent
  rw [diffusion_source]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_r,pair_smul_r,Complex.add_re]
  have hb:=anti_current_source driftClock drift_clock_pair f w z he
  have hu:=weight_current_source f w z he
  norm_num only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  simp only [LinearMap.add_apply,pair_add_r] at hu
  rw [hb,hu]
  have hself:(sourcePair (U w) w).im=0:=by
    have hc:=pair_star (U w) w
    rw [weight_pair] at hc
    have hh:=congrArg Complex.im hc
    simp only [Complex.conj_im] at hh
    linarith
  simp only [driftClock,matchedTester,LinearMap.add_apply,LinearMap.smul_apply,
    pair_add_r,pair_add_l,pair_smul_r,pair_smul_l]
  norm_num only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    map_ofNat,Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero]
  rw [hself]
  ring

def matchedField(w:QuantumTest):ℝ:=
  (sourcePair w (((2:ℂ) • (U*GaussMatterCore.matterAction)+(8/5:ℂ) • (U*vacuumConstantAction)) w)).re+
    12*n*spinForm (U w)+12*n*densityForm (U w)-12*gaugeForm (U w)-12*spatialForm (U w)
def diffusionSourcePrice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  let w:=normalizedState m ell F z hz g
  (sourcePair w (completeCurrent H0 w)).re+matchedField w
private theorem actual_complete_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    diffusionSourcePrice m ell F z hz g=matchedForcingWord m ell F z hz g+
      6*z.im*(sourcePair (matchedColumn (normalizedState m ell F z hz g)) (normalizedState m ell F z hz g)).im := by
  let w:=normalizedState m ell F z hz g
  have h:=complete_source (normalizedForcing m ell F z hz g) w z (full_source m ell F z hz g)
  have hH:H0=compressionCore F+defectAction F:=by unfold H0 defectAction;abel
  have hb:bracket A (bracket A (compressionCore F))+bracket A (bracket A (defectAction F))=
      bracket A (bracket A H0):=by rw [hH];unfold bracket;noncomm_ring
  unfold diffusionSourcePrice matchedForcingWord matchedField
  rw [hb]
  simp only [LinearMap.add_apply,pair_add_r,Complex.add_re]
  dsimp only [w] at h
  linear_combination h
private theorem actual_price_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    diffusionSourcePrice m ell F z hz g=matchedPrice m ell F z hz g := by
  rw [actual_complete_source,(actual_native_matched_source m ell F z hz g).2.1]
private theorem conjugate_square_pair(f g:QuantumTest):sourcePair f (A (A g))=sourcePair (A (A f)) g:=by
  rw [conjugate_pair,conjugate_pair]
  ring
private theorem double_conjugate_source(f w:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    (sourcePair w (bracket A (bracket A H0) w)).re=
      2*(sourcePair f (A (A w))).re+2*(sourcePair (A w) (H0 (A w)-(z.re:ℂ) • A w)).re := by
  have hp:sourcePair w (bracket A (bracket A H0) w)=
      sourcePair (A (A w)) (H0 w)+2*sourcePair (A w) (H0 (A w))+sourcePair (H0 w) (A (A w)):=by
    change sourcePair w (A (A (H0 w)-H0 (A w))-(A (H0 (A w))-H0 (A (A w))))=_
    simp only [map_sub,pair_sub_r,conjugate_pair,diagonalAction_pair]
    ring
  have hself:sourcePair w (A (A w))= -(‖embed (A w)‖^2:ℂ):=by rw [conjugate_pair,self_pair]
  have hself':sourcePair (A (A w)) w= -(‖embed (A w)‖^2:ℂ):=by
    rw [←conjugate_square_pair,hself]
  rw [hp,he]
  simp only [pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,pair_sub_r,hself,hself',self_pair]
  simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.neg_re,Complex.neg_im,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [pair_sym_re (A (A w)) f]
  ring

def remainingDrift:End:=diffusionDrift+(3:ℂ) • U
def diffusionRemainder(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  let w:=normalizedState m ell F z hz g
  2*(sourcePair (normalizedForcing m ell F z hz g) (remainingDrift w)).re+
    6*z.re*(sourcePair w (U w)).re+matchedField w
private theorem actual_middle_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    matchedForcingWord m ell F z hz g=
      2*(sourcePair (A (normalizedState m ell F z hz g))
        (H0 (A (normalizedState m ell F z hz g))-(z.re:ℂ) • A (normalizedState m ell F z hz g))).re+
      diffusionRemainder m ell F z hz g := by
  let w:=normalizedState m ell F z hz g
  have h:=double_conjugate_source (normalizedForcing m ell F z hz g) w z (full_source m ell F z hz g)
  have hH:H0=compressionCore F+defectAction F:=by unfold H0 defectAction;abel
  have hb:bracket A (bracket A (compressionCore F))+bracket A (bracket A (defectAction F))=
      bracket A (bracket A H0):=by rw [hH];unfold bracket;noncomm_ring
  have hr:remainingDrift=A*A-(3:ℂ) • matchedTester:=by
    unfold remainingDrift diffusionDrift driftClock matchedTester
    module
  unfold matchedForcingWord diffusionRemainder matchedField
  rw [hb,hr]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_add_r,pair_sub_r,pair_smul_r,Complex.add_re,Complex.sub_re]
  norm_num only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  dsimp only [w] at h
  simp only [pair_sub_r,pair_smul_r,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h ⊢
  linear_combination h

private theorem combined_volume:Commute D SourceCoframeVolume.volumeAction := by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator SourceCoframeVolume.volumeAction
  have hg:=SourceGaugeScaleTransport.generator_commutator SourceCoframeVolume.volumeAction
  rw [SourceScalarPositiveBulkWard.original_volume_phi] at hp
  rw [SourceScalarPositiveBulkWard.original_volume_gauge] at hg
  change (Phi-Gauge)*SourceCoframeVolume.volumeAction=SourceCoframeVolume.volumeAction*(Phi-Gauge)
  linear_combination (norm:=noncomm_ring) hp-hg
private theorem diffusion_volume:diffusionCurrent SourceCoframeVolume.volumeAction=(18:ℂ) • (1:End) := by
  let V:End:=SourceCoframeVolume.volumeAction
  have hu:Commute U V:=real_commute _ _ _ _
  have ha:Commute A V:=(real_commute _ _ _ _).mul_left combined_volume
  have huv:V*U=(1:End):=by apply LinearMap.ext;exact volume_inverse
  have hd:bracket Dc V=(-2*Complex.I) • V:=SourceDilationKinetic.volume_scale_current
  have hx:bracket A V=0:=sub_eq_zero.mpr ha.eq
  have hB:bracket driftClock V=(6:ℂ) • (1:End):=by
    have hz:bracket (U*D) V=0:=sub_eq_zero.mpr (hu.mul_left combined_volume).eq
    have hUv:bracket U V=0:=sub_eq_zero.mpr hu.eq
    have hDU:bracket (Dc*U) V=(-2*Complex.I) • (1:End):=by
      have hb:bracket (Dc*U) V=Dc*bracket U V+bracket Dc V*U:=by unfold bracket;noncomm_ring
      rw [hb,hUv,hd]
      simp only [mul_zero,zero_add,smul_mul_assoc,huv]
    unfold driftClock matchedColumn
    change bracket (U*D+(3*Complex.I) • (Dc*U)+(3:ℂ) • U) V=_
    have hb(X Y:End):bracket (X+Y) V=bracket X V+bracket Y V:=by unfold bracket;noncomm_ring
    have hs(c:ℂ)(X:End):bracket (c • X) V=c • bracket X V:=by
      simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
    rw [hb,hb,hs,hs,hz,hDU,hUv]
    simp only [smul_zero,zero_add,add_zero,smul_smul]
    congr 1
    calc _= -6*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [diffusion_source,hx]
  have hz:bracket A (0:End)=0:=by unfold bracket;noncomm_ring
  rw [hz,zero_add,hB,smul_smul]
  norm_num
private theorem conjugate_point(f:QuantumTest)(x:SourceCoordinateSlice):
    A f x=(inverseRootVolume x:ℂ) • D f x:=rfl
private theorem noise_source_zero_jet(f g:QuantumTest)(x y:physicalChart):
    HasDerivAt (fun t:ℝ=>(noiseKernel t x y:ℂ)*inner ℂ (D f x.val) (D g y.val))
      (2*inner ℂ (A f x.val) (A g y.val)) 0 := by
  have hk:=noise_kernel_zero_jet x y
  have hc:HasDerivAt (fun t:ℝ=>(noiseKernel t x y:ℂ))
      ((2*inverseRootVolume x.val*inverseRootVolume y.val:ℝ):ℂ) 0:=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hk
  have hi:(((2*inverseRootVolume x.val*inverseRootVolume y.val:ℝ):ℂ)*
      inner ℂ (D f x.val) (D g y.val))=2*inner ℂ (A f x.val) (A g y.val):=by
    rw [conjugate_point,conjugate_point,inner_smul_left,inner_smul_right]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.conj_ofReal]
    ring
  rw [←hi]
  exact hc.mul_const _

private theorem actual_green_source(g:diagonal.domain):
    ∀ᶠ F in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      matchedForcingWord m ell F z hz g=
        SourceClockPhiRenormalizedSecondGreen.renormalizedEndpoint m ell F z hz g/z.im^2-
        (SourceClockPhiRenormalizedSecondGreen.secondCFWord m ell F z hz g-
          2*‖embed (SourceClockPhiRenormalizedSecondGreen.fixedColumn m ell g)‖^2*(z⁻¹).re)/(2*z.im^2)+
        diffusionRemainder m ell F z hz g := by
  filter_upwards [SourceClockPhiRenormalizedSecondGreen.actual_renormalized_second_CF_source g] with F hF
  intro m ell z hz
  have hg:=hF m ell z hz
  have hm:=actual_middle_source m ell F z hz g
  change SourceClockPhiRenormalizedSecondGreen.secondCFWord m ell F z hz g-
      2*‖embed (SourceClockPhiRenormalizedSecondGreen.fixedColumn m ell g)‖^2*(z⁻¹).re=
    2*SourceClockPhiRenormalizedSecondGreen.renormalizedEndpoint m ell F z hz g-
      4*z.im^2*(sourcePair (A (normalizedState m ell F z hz g))
        (H0 (A (normalizedState m ell F z hz g))-(z.re:ℂ) • A (normalizedState m ell F z hz g))).re at hg
  apply (mul_right_inj' (show (2:ℝ)*z.im^2≠0 from mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))).mp
  field_simp [hz]
  linear_combination (norm:=ring) (2*z.im^2)*hm+hg

private theorem lapse_pos:0<n:=by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private def regularizedRootWeight(s:ℝ)(z:SourceCoordinateSlice):ℝ:=
  (Real.sqrt (GaussNativeEnergy.volume z+18*s))⁻¹
private theorem regularized_root_smooth(s:ℝ)(hs:0≤ s)(x:physicalChart):
    ContDiffAt ℝ ∞ (regularizedRootWeight s) x.val:=
  ((volume_smooth.contDiffAt.add contDiffAt_const).sqrt (by have hv:=volume_pos x;positivity)).inv
    (Real.sqrt_pos.mpr (by have hv:=volume_pos x;positivity)).ne'
def regularizedConjugate(s:ℝ)(hs:0≤ s):End:=
  multiply (regularizedRootWeight s) (regularized_root_smooth s hs)*D
private def correctionWeight(s:ℝ)(z:SourceCoordinateSlice):ℝ:=
  Real.sqrt (GaussNativeEnergy.volume z)-GaussNativeEnergy.volume z*regularizedRootWeight s z
private theorem correction_smooth(s:ℝ)(hs:0≤ s)(x:physicalChart):
    ContDiffAt ℝ ∞ (correctionWeight s) x.val:=
  (volume_smooth.contDiffAt.sqrt (volume_pos x).ne').sub
    (volume_smooth.contDiffAt.mul (regularized_root_smooth s hs x))
private theorem correction_bound(s:ℝ)(hs:0≤ s)(x:physicalChart):
    0≤ correctionWeight s x.val ∧ correctionWeight s x.val≤ Real.sqrt (18*s) := by
  let v:=GaussNativeEnergy.volume x.val
  let u:=Real.sqrt v
  let p:=Real.sqrt (v+18*s)
  let h:=Real.sqrt (18*s)
  have hv:0<v:=volume_pos x
  have hu:0≤ u:=Real.sqrt_nonneg _
  have hp:0<p:=Real.sqrt_pos.mpr (by dsimp only [v];have hv:=volume_pos x;positivity)
  have hh:0≤ h:=Real.sqrt_nonneg _
  have hu2:u^2=v:=Real.sq_sqrt hv.le
  have hp2:p^2=v+18*s:=Real.sq_sqrt (by positivity)
  have hh2:h^2=18*s:=Real.sq_sqrt (by positivity)
  have hup:u≤ p:=Real.sqrt_le_sqrt (by linarith)
  have hsum:p≤ u+h:=by nlinarith [mul_nonneg hu hh]
  change 0≤ u-v/p ∧ u-v/p≤ h
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hup hu]
  · have he:u-v/p≤ p-u:=by
      apply (mul_le_mul_iff_right₀ hp).mp
      field_simp [hp.ne']
      nlinarith only [sq_nonneg (p-u),hu2]
    linarith
private theorem correction_core(s:ℝ)(hs:0≤ s)(f:QuantumTest):
    (A-regularizedConjugate s hs) f=
      multiply (correctionWeight s) (correction_smooth s hs) (U (D f)) := by
  apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · change (inverseRootVolume z:ℂ) • D f z-(regularizedRootWeight s z:ℂ) • D f z=
      (correctionWeight s z:ℂ) • ((reciprocalVolume z:ℂ) • D f z)
    rw [←sub_smul,smul_smul]
    congr 1
    have hv:GaussNativeEnergy.volume z≠0:=(volume_pos ⟨z,hz⟩).ne'
    have hr:Real.sqrt (GaussNativeEnergy.volume z)≠0:=(Real.sqrt_pos.mpr (volume_pos ⟨z,hz⟩)).ne'
    have hsq:Real.sqrt (GaussNativeEnergy.volume z)^2=GaussNativeEnergy.volume z:=Real.sq_sqrt (volume_pos ⟨z,hz⟩).le
    norm_cast
    unfold inverseRootVolume reciprocalVolume correctionWeight
    field_simp [hv,hr]
    nlinarith only [hsq]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem regularization_norm(s:ℝ)(hs:0≤ s)(f:QuantumTest):
    ‖embed ((A-regularizedConjugate s hs) f)‖^2≤ 18*s*‖embed (U (D f))‖^2 := by
  rw [correction_core]
  have hn:‖embed (multiply (correctionWeight s) (correction_smooth s hs) (U (D f)))‖≤
      Real.sqrt (18*s)*‖embed (U (D f))‖:=by
    apply GaussBoundedMultiplier.action_bound
      (fun z=>(correctionWeight s z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
      (fun x=>(Complex.ofRealCLM.contDiff.contDiffAt.comp x.val (correction_smooth s hs x)).smul contDiffAt_const)
    · intro x r
      exact (Commute.one_right (GaussFockWeights.weight r)).smul_right _
    · exact Real.sqrt_nonneg _
    · intro x v
      change ‖(correctionWeight s x.val:ℂ) • v‖≤ _
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (correction_bound s hs x).1]
      exact mul_le_mul_of_nonneg_right (correction_bound s hs x).2 (norm_nonneg _)
  have hh:=pow_le_pow_left₀ (norm_nonneg _) hn 2
  rwa [mul_pow,Real.sq_sqrt (by positivity)] at hh

open MeasureTheory GaussCoframeForm
private theorem number_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (number f)).re := by
  rw [sourcePair_integral]
  change 0 ≤ RCLike.re (∫ z,densityPair f (number f) z ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable f (number f))]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (number f) z).re
  by_cases hz : z∈physicalChart
  · rw [densityPair_sum]
    simp only [Complex.re_sum,GaussCoframeForm.number_apply]
    apply Finset.sum_nonneg
    intro word _
    have hd := (GaussDensityCore.density_pos word.card ⟨z,hz⟩).le
    have he : (GaussDensityCore.complexDensity word.card z*star (f z word)*
        ((word.card:ℂ)*f z word)).re=
        GaussDensityCore.density word.card z*(word.card:ℝ)*‖f z word‖^2 := by
      rw [GaussDensityCore.complexDensity]
      have hh : (star (f z word))*(f z word)=((‖f z word‖^2:ℝ):ℂ) := by
        simpa only [RCLike.inner_apply,mul_comm,starRingEnd_apply,Complex.ofReal_pow] using!
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f z word)
      calc
        _=(((GaussDensityCore.density word.card z:ℂ)*(word.card:ℂ))*
            (star (f z word)*f z word)).re := by congr 1;ring
        _=_ := by
          rw [hh]
          norm_cast
          rw [←Complex.ofReal_mul,Complex.ofReal_re]
    rw [he]
    positivity
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem dilation_gram(f:QuantumTest):‖embed (Dc f)‖^2 ≤ (2/3:ℝ)*coframeGram f := by
  have hcenter:Dc=(2/3:ℂ) • (∑b:Fin 3,centeredBlock b) := by
    unfold Dc
    rw [SourceCoframeDilation.dilation_operator]
    simp [centeredBlock,blockMomentum,blockDensity,blockIndices,eulerAction,GaussCoframeCore.momentum,Fin.sum_univ_succ]
    module
  have ht:=norm_sum_le (Finset.univ:Finset (Fin 3)) (fun b=>embed (centeredBlock b f))
  have ht2:=pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hs:=sq_sum_le_card_mul_sum_sq (s:=(Finset.univ:Finset (Fin 3))) (f:=fun b=>‖embed (centeredBlock b f)‖)
  norm_num only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hs
  have hn:‖embed (Dc f)‖^2 ≤ (4/3:ℝ)*(∑b:Fin 3,‖embed (centeredBlock b f)‖^2) := by
    rw [hcenter]
    simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,norm_smul,mul_pow]
    norm_num
    nlinarith only [ht2,hs]
  have hc:=original_coframe_three_block_hardy f
  have hnum:=number_nonnegative f
  nlinarith only [hn,hc,hnum,sq_nonneg ‖embed (number f)‖,sq_nonneg ‖embed f‖]
private theorem actual_D_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (3*n/8)*‖embed (U (D (normalizedState m ell F z hz g)))‖^2≤ 4*matchedPrice m ell F z hz g := by
  let w:=normalizedState m ell F z hz g
  have hj:=(actual_native_matched_source m ell F z hz g).2.2.1
  have hscalar:0≤ scalarForm (U w):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hshift:0≤ shiftedMoment40 w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hn:=lapse_pos
  have hfloor:(3*n/8)*‖embed (matchedColumn w)‖^2+(3*n/4)*coframeGram (U w)≤
      matchedPrice m ell F z hz g:=by
    change (3*n/8)*‖embed (matchedColumn w)‖^2+(5*n/2)*scalarForm (U w)+10*n*shiftedMoment40 w+
      (3*n/4)*coframeGram (U w)+18*n*‖embed w‖^2≤ matchedPrice m ell F z hz g at hj
    have hs0:0≤(5*n/2)*scalarForm (U w):=mul_nonneg (by positivity) hscalar
    have hr0:0≤ 10*n*shiftedMoment40 w:=mul_nonneg (by positivity) hshift
    have hw0:0≤ 18*n*‖embed w‖^2:=by positivity
    linarith only [hj,hs0,hr0,hw0]
  have hd:=dilation_gram (U w)
  have hsplit:embed (U (D w))=embed (matchedColumn w)-(3*Complex.I) • embed (Dc (U w)):=by
    simp only [matchedColumn,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,map_add,map_smul]
    module
  have ht:‖embed (U (D w))‖≤‖embed (matchedColumn w)‖+3*‖embed (Dc (U w))‖:=by
    rw [hsplit]
    have h:=norm_sub_le (embed (matchedColumn w)) ((3*Complex.I) • embed (Dc (U w)))
    norm_num [norm_smul,norm_mul,Complex.norm_I] at h
    exact h
  have ht2:=pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hquadratic:‖embed (U (D w))‖^2≤ 4*(‖embed (matchedColumn w)‖^2+3*‖embed (Dc (U w))‖^2):=by
    nlinarith only [ht2,sq_nonneg (‖embed (matchedColumn w)‖-‖embed (Dc (U w))‖)]
  change (3*n/8)*‖embed (U (D w))‖^2≤ _
  have hq:=mul_le_mul_of_nonneg_left hquadratic (show 0≤ 3*n/8 by positivity)
  have hdd:=mul_le_mul_of_nonneg_left hd (show 0≤(9*n/2) by positivity)
  nlinarith only [hq,hdd,hfloor]
private theorem actual_regularization_price(s:ℝ)(hs:0≤ s)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    ‖embed ((A-regularizedConjugate s hs) (normalizedState m ell F z hz g))‖^2≤
      (192*s/n)*matchedPrice m ell F z hz g := by
  have h1:=regularization_norm s hs (normalizedState m ell F z hz g)
  have h2:=actual_D_price m ell F z hz g
  have hn:=lapse_pos
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  have hp:=mul_le_mul_of_nonneg_right h1 hn.le
  have hq:=mul_le_mul_of_nonneg_left h2 (show 0≤ 48*s by positivity)
  nlinarith only [hp,hq]

private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(t:ℝ):
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem actual_regularization_common_payment(s:ℝ)(hs:0≤ s)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N≤ m → ∀ell,m≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,(∫⁻t:ℝ,ENNReal.ofReal
        (‖embed ((A-regularizedConjugate s hs)
          (normalizedState m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g))‖^2-
          (384*s/n)*matchedForcingWord m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g))≤
        ENNReal.ofReal ε := by
  intro ε hε
  let C:ℝ:=192*s/n
  have hC:0≤ C:=by dsimp only [C];have hn:=lapse_pos;positivity
  obtain ⟨N,hN⟩:=actual_native_matched_common_payment μ hμ g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  calc
    _≤∫⁻t:ℝ,ENNReal.ofReal C*ENNReal.ofReal
        (matchedPrice m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g-
          2*matchedForcingWord m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g):=by
      apply lintegral_mono
      intro t
      have hp:=actual_regularization_price s hs m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [C]
      linear_combination (norm:=ring) hp
      norm_num
    _=ENNReal.ofReal C*(∫⁻t:ℝ,ENNReal.ofReal
        (matchedPrice m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g-
          2*matchedForcingWord m ell F (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) g)):=by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)):=
      mul_le_mul_of_nonneg_left (hF advanced) (show 0≤ ENNReal.ofReal C from zero_le)
    _≤ ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hp:0<C+1:=by positivity
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hp).mpr
      nlinarith only [hε]

/-- The full cross-volume source noise keeps its two native half-weight legs, and reads the entire CF/defect covariance. -/
theorem original_matched_diffusion_covariance{ι:Type*}[Fintype ι](t:ℝ)(ht:0≤ t)
    (x:ι → physicalChart)(c:ι → ℂ):
    diffusionCurrent (1:End)=0 ∧
    diffusionCurrent SourceCoframeVolume.volumeAction=(18:ℂ) • (1:End) ∧
    0≤(∑i,∑j,star (c i)*((noiseKernel t (x i) (x j):ℝ):ℂ)*c j).re ∧
    (∀f g:QuantumTest,∀p q:physicalChart,
      HasDerivAt (fun s:ℝ=>(noiseKernel s p q:ℂ)*inner ℂ (D f p.val) (D g q.val))
        (2*inner ℂ (A f p.val) (A g q.val)) 0) ∧
    (∀F:Index,∀f:QuantumTest,
      (sourcePair f ((diffusionCurrent (H0*H0)-diffusionCurrent H0*H0-H0*diffusionCurrent H0) f)).re=
        2*‖embed (bracket A (compressionCore F) f+bracket A (defectAction F) f)‖^2) ∧
    (∀m ell:ℕ,∀F:Index,∀z:ℂ,∀hz:z.im≠0,∀g:diagonal.domain,
      ‖embed ((A-regularizedConjugate t ht) (normalizedState m ell F z hz g))‖^2≤
        (192*t/n)*matchedPrice m ell F z hz g) ∧
    (∀μ:ℝ,∀hμ:0<μ,∀g:diagonal.domain,∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N≤ m → ∀ell,m≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻r:ℝ,ENNReal.ofReal
          (‖embed ((A-regularizedConjugate t ht)
            (normalizedState m ell F (actualFrequency advanced μ r) (frequency_nonreal advanced μ hμ r) g))‖^2-
            (384*t/n)*matchedForcingWord m ell F (actualFrequency advanced μ r) (frequency_nonreal advanced μ hμ r) g))≤
          ENNReal.ofReal ε) :=
  ⟨diffusion_conservative,diffusion_volume,complex_kernel_nonnegative t ht x c,
    noise_source_zero_jet,actual_carre,actual_regularization_price t ht,actual_regularization_common_payment t ht⟩

def fixedEndpointWord(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  (((z^2)⁻¹)*(∑i:Fin 2,sourcePair (SourceClockPhiRenormalizedSecondGreen.fixedSecondTester m ell g i)
    (SourceClockPhiRenormalizedSecondGreen.fixedSecondResponse i F z hz g))-
    ((z.re:ℂ)*((z^2)⁻¹))*(∑i:Fin 2,sourcePair (SourceClockPhiRenormalizedSecondGreen.fixedFirstTester m ell g i)
      (SourceClockPhiRenormalizedSecondGreen.fixedSecondResponse i F z hz g))).re-
    (sourcePair (SourceClockPhiRenormalizedSecondGreen.fixedColumn m ell g)
      (H0 (SourceClockPhiRenormalizedSecondGreen.fixedColumn m ell g))).re*((z^2)⁻¹).re-
    2*z.re*z.im^2*‖embed (SourceClockPhiRenormalizedSecondGreen.fixedColumn m ell g)‖^2/(z.re^2+z.im^2)^2

/-- The same Q(H0) source retains all fields and defects, and its pole-renormalized endpoint now reads only the two original H0-squared inputs. -/
theorem actual_matched_diffusion_source(g:diagonal.domain):
    ∀ᶠ F in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      diffusionSourcePrice m ell F z hz g=matchedPrice m ell F z hz g ∧
      diffusionSourcePrice m ell F z hz g=electricForcingWord m ell F z hz g+
        6*z.im*(sourcePair (matchedColumn (normalizedState m ell F z hz g)) (normalizedState m ell F z hz g)).im ∧
      matchedForcingWord m ell F z hz g=fixedEndpointWord m ell F z hz g/z.im^2-
        (SourceClockPhiRenormalizedSecondGreen.secondCFWord m ell F z hz g-
          2*‖embed (SourceClockPhiRenormalizedSecondGreen.fixedColumn m ell g)‖^2*(z⁻¹).re)/(2*z.im^2)+
        diffusionRemainder m ell F z hz g := by
  filter_upwards [actual_green_source g,
    SourceClockPhiRenormalizedSecondGreen.actual_renormalized_fixed_source g] with F hF he
  intro m ell z hz
  refine ⟨actual_price_return m ell F z hz g,?_,?_⟩
  · rw [actual_complete_source,(actual_matched_electric_source m ell F z hz g).2.1]
  · have hr:SourceClockPhiRenormalizedSecondGreen.renormalizedEndpoint m ell F z hz g=
        fixedEndpointWord m ell F z hz g:=he m ell z hz
    rw [←hr]
    exact hF m ell z hz

end LowEnergy.SourceClockPhiMatchedDiffusionSource
