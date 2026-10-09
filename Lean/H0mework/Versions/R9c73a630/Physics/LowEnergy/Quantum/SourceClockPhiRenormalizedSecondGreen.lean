import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiNativeMatchedSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiWholeCFGreenSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderTimeTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRenormalizedSecondGreen
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource
open SourceClockPhiNativeJointPayment SourceClockYukawaCubicCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusSourceCurrent SourceScalarPairedTransport SourceScalarDoubleCurrent
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiNormalizedScalarBudget
open SourceScalarPositiveBulkWard SourceInverseJetEnergy SourceLocalizedInverseFormPayment
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev H0 : End := diagonalAction
private abbrev A : End := combinedConjugate
private abbrev Ad : End := -combinedGenerator*inverseRootAction
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev W (m ell : ℕ) (i : Fin 2) : End := phaseRow m ell i
private abbrev Two := Fin 2 → QuantumTest
private abbrev TwoEnd := Two →ₗ[ℂ] Two
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore state
  GaussAdjointHistory.coreStep

private theorem pair_add_l (f g h : QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (f g h : QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (f g h : QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (f g h : QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c : ℂ) (f g : QuantumTest) : sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r (c : ℂ) (f g : QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sum_l {ι : Type*} [Fintype ι] (v : ι → QuantumTest) (f : QuantumTest) :
    sourcePair (∑i,v i) f=∑i,sourcePair (v i) f := by
  simp only [sourcePair,map_sum,sum_inner]
private theorem pair_sum_r {ι : Type*} [Fintype ι] (f : QuantumTest) (v : ι → QuantumTest) :
    sourcePair f (∑i,v i)=∑i,sourcePair f (v i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_star (f g : QuantumTest) : star (sourcePair f g)=sourcePair g f := by
  simpa only [sourcePair,starRingEnd_apply] using (inner_conj_symm (𝕜:=ℂ) (embed g) (embed f))
private theorem pair_neg_l (f g : QuantumTest) : sourcePair (-f) g= -sourcePair f g := by
  simp only [sourcePair,map_neg,inner_neg_left]

private theorem flow_pair_generator (flow : ℝ → End) (G : End)
    (hzero : ∀f,flow 0 f=f)
    (hpair : ∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv : ∀f,HasDerivAt (fun t : ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g : QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t : ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=fun _=>inner ℂ (embed f) (embed g) :=
    funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq
private theorem phi_pair (f g : QuantumTest) : sourcePair f (SourceScalarAffineScaleTransport.generator g)=
    -sourcePair (SourceScalarAffineScaleTransport.generator f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow SourceScalarAffineScaleTransport.generator
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_pair (f g : QuantumTest) : sourcePair f (SourceGaugeScaleTransport.generator g)=
    -sourcePair (SourceGaugeScaleTransport.generator f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow SourceGaugeScaleTransport.generator
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
private theorem combined_pair (f g : QuantumTest) : sourcePair f (combinedGenerator g)=
    -sourcePair (combinedGenerator f) g := by
  simp only [combinedGenerator,LinearMap.sub_apply,pair_sub_l,pair_sub_r,phi_pair,gauge_pair]
  ring
private theorem root_pair (f g : QuantumTest) : sourcePair f (inverseRootAction g)=
    sourcePair (inverseRootAction f) g := multiply_pair _ _ f g
private theorem conjugate_pair (f g : QuantumTest) : sourcePair f (A g)=sourcePair (Ad f) g := by
  change sourcePair f (inverseRootAction (combinedGenerator g))=sourcePair (-combinedGenerator (inverseRootAction f)) g
  rw [root_pair,combined_pair,pair_neg_l]
private theorem adjoint_pair (f g : QuantumTest) : sourcePair f (Ad g)=sourcePair (A f) g := by
  have h:=congrArg (star : ℂ→ℂ) (conjugate_pair g f)
  simpa only [pair_star] using h.symm

private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)
private theorem pair_product {X Y : End} (hX : GaussCoframeForm.Paired X X)
    (hY : GaussCoframeForm.Paired Y Y) (hXY : Commute X Y) : GaussCoframeForm.Paired (X*Y) (X*Y) := by
  intro f g
  change sourcePair f (X (Y g))=sourcePair (X (Y f)) g
  rw [hX,hY]
  exact congrArg (fun v=>sourcePair v g) (LinearMap.congr_fun hXY.eq f).symm
private theorem pair_power {X : End} (hX : GaussCoframeForm.Paired X X) (k : ℕ) :
    GaussCoframeForm.Paired (X^k) (X^k) := by
  induction k with
  | zero=>intro f g;rfl
  | succ k ih=>rw [pow_succ];exact pair_product ih hX ((Commute.refl X).pow_left k)
private theorem inverse_pair (f g : QuantumTest) : sourcePair f (S g)=sourcePair (S f) g :=
  multiply_pair _ _ f g
private theorem theta_pair (m ell : ℕ) : GaussCoframeForm.Paired (T m ell) (T m ell) := by
  have hQ : GaussCoframeForm.Paired (1-S : End) (1-S) := by
    intro f g
    simp only [LinearMap.sub_apply,Module.End.one_apply,pair_sub_l,pair_sub_r]
    rw [inverse_pair]
  intro f g
  change sourcePair f (((1-S)^(m+1)) g-((1-S)^(ell+1)) g)=
    sourcePair (((1-S)^(m+1)) f-((1-S)^(ell+1)) f) g
  rw [pair_sub_l,pair_sub_r,pair_power hQ,pair_power hQ]
private theorem inverse_theta (m ell : ℕ) : Commute S (T m ell) :=
  (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (m+1)).sub_right
    (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (ell+1))
private theorem row_pair (m ell : ℕ) (i : Fin 2) : GaussCoframeForm.Paired (W m ell i) (W m ell i) := by
  fin_cases i
  · exact theta_pair m ell
  · intro f g
    have h:=pair_product (show GaussCoframeForm.Paired S S from multiply_pair _ _) (theta_pair m ell)
      (inverse_theta m ell) f g
    change sourcePair f (-((S*T m ell) g))=sourcePair (-((S*T m ell) f)) g
    simpa only [sourcePair,map_neg,inner_neg_left,inner_neg_right] using congrArg Neg.neg h

private def twoPair (f g : Two) : ℂ := ∑i,sourcePair (f i) (g i)
private def column (m ell : ℕ) : Two →ₗ[ℂ] QuantumTest where
  toFun f:=∑i,A (W m ell i (f i))
  map_add' f g:=by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c f:=by simp only [Pi.smul_apply,map_smul,Finset.smul_sum];rfl
private def columnAdjoint (m ell : ℕ) : QuantumTest →ₗ[ℂ] Two where
  toFun f i:=W m ell i (Ad f)
  map_add' f g:=by funext i;simp only [map_add,Pi.add_apply]
  map_smul' c f:=by funext i;simp only [map_smul,Pi.smul_apply];rfl
private def twoCompression (F : Index) : TwoEnd where
  toFun f i:=compressionCore F (f i)
  map_add' f g:=by funext i;simp only [map_add,Pi.add_apply]
  map_smul' c f:=by funext i;simp only [map_smul,Pi.smul_apply];rfl
private theorem column_pair (m ell : ℕ) (f : Two) (g : QuantumTest) :
    sourcePair (column m ell f) g=twoPair f (columnAdjoint m ell g) := by
  simp only [column,LinearMap.coe_mk,AddHom.coe_mk,pair_sum_l,twoPair,columnAdjoint]
  apply Finset.sum_congr rfl;intro i _
  rw [←adjoint_pair,←row_pair m ell i]
private theorem column_adj_pair (m ell : ℕ) (f : QuantumTest) (g : Two) :
    twoPair (columnAdjoint m ell f) g=sourcePair f (column m ell g) := by
  simp only [column,columnAdjoint,LinearMap.coe_mk,AddHom.coe_mk,pair_sum_r,twoPair]
  apply Finset.sum_congr rfl;intro i _
  rw [←row_pair m ell i,←conjugate_pair]

private theorem inverse_radius : S*r=(1 : End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z : ℂ) • ((phiRadius z : ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem row_zero (m ell : ℕ) (g : diagonal.domain) :
    column m ell (fun i=>coreEquiv.symm (inputSeed g i))=0 := by
  simp only [column,LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_two]
  change A (T m ell (coreEquiv.symm g))+A (-(S*T m ell) (coreEquiv.symm (phiRadiusSource g)))=0
  unfold phiRadiusSource
  rw [coreEquiv.symm_apply_apply]
  change A (T m ell (coreEquiv.symm g))+A (-(S*T m ell) (r (coreEquiv.symm g)))=0
  have hSr:S*T m ell*r=T m ell := by
    rw [(inverse_theta m ell).eq,mul_assoc,inverse_radius,mul_one]
  have he:=LinearMap.congr_fun hSr (coreEquiv.symm g)
  change S (T m ell (r (coreEquiv.symm g)))=T m ell (coreEquiv.symm g) at he
  simp only [Module.End.mul_apply,map_neg]
  rw [he]
  exact add_neg_cancel _

def fixedColumn (m ell : ℕ) (g : diagonal.domain) : QuantumTest :=
  column m ell (fun i=>coreEquiv.symm (GaussAdjointHistory.coreStep (inputSeed g i)))
def secondSourceColumn (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  column m ell (fun i=>state F z hz (GaussAdjointHistory.coreStep
    (GaussAdjointHistory.coreStep (inputSeed g i))))

/-- The full-H0 squared fixed seeds remove the moving second graph before any estimate. -/
theorem actual_two_step_column (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀m ell : ℕ,∀z : ℂ,∀hz : z.im≠0,
      z^2 • (A (normalizedState m ell F z hz g))=
        secondSourceColumn m ell F z hz g-fixedColumn m ell g := by
  filter_upwards [actual_source_step g,actual_source_step (phiRadiusSource g),
    actual_source_step (GaussAdjointHistory.coreStep g),
    actual_source_step (GaussAdjointHistory.coreStep (phiRadiusSource g))] with F h0 h1 h2 h3
  intro m ell z hz
  have hs(i : Fin 2):z • state F z hz (inputSeed g i)=
      state F z hz (GaussAdjointHistory.coreStep (inputSeed g i))-coreEquiv.symm (inputSeed g i) := by
    fin_cases i
    · exact h0 z hz
    · exact h1 z hz
  have ht(i : Fin 2):z • state F z hz (GaussAdjointHistory.coreStep (inputSeed g i))=
      state F z hz (GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i)))-
        coreEquiv.symm (GaussAdjointHistory.coreStep (inputSeed g i)) := by
    fin_cases i
    · exact h2 z hz
    · exact h3 z hz
  have he(i : Fin 2):z^2 • state F z hz (inputSeed g i)=
      state F z hz (GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i)))-
      coreEquiv.symm (GaussAdjointHistory.coreStep (inputSeed g i))-
      z • coreEquiv.symm (inputSeed g i) := by
    have h:=congrArg (fun x : QuantumTest=>z • x) (hs i)
    have ht0:=ht i
    simp only [smul_sub] at h
    have h1:z^2 • state F z hz (inputSeed g i)=
        z • state F z hz (GaussAdjointHistory.coreStep (inputSeed g i))-
        z • coreEquiv.symm (inputSeed g i) := by
      simpa only [pow_two,mul_smul] using h
    linear_combination (norm:=module) h1+ht0
  have h:=congrArg (column m ell) (funext he)
  change column m ell (z^2 • (fun i=>state F z hz (inputSeed g i)))=_ at h
  have hr:column m ell (fun i=>state F z hz (inputSeed g i))=A (normalizedState m ell F z hz g) := by
    simp only [column,LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_two]
    change A (T m ell (state F z hz g))+A (-(S*T m ell) (state F z hz (phiRadiusSource g)))=_
    have hr0:state F z hz g=resolventCore F z hz (coreEquiv.symm g) := by
      simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
    have hr1:state F z hz (phiRadiusSource g)=resolventCore F z hz (r (coreEquiv.symm g)) := by
      unfold resolventCore;rfl
    rw [hr0,hr1]
    change _=A (T m ell (resolventCore F z hz (coreEquiv.symm g))-
      S (T m ell (resolventCore F z hz (r (coreEquiv.symm g)))))
    simp only [Module.End.mul_apply,map_sub,map_neg]
    module
  change column m ell (z^2 • (fun i=>state F z hz (inputSeed g i)))=
    column m ell ((fun i=>state F z hz (GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i))))-
      (fun i=>coreEquiv.symm (GaussAdjointHistory.coreStep (inputSeed g i)))-
      z • (fun i=>coreEquiv.symm (inputSeed g i))) at h
  simp only [map_smul,map_sub,hr,row_zero,smul_zero,sub_zero] at h
  exact h

private theorem two_add_l (f g h : Two) : twoPair (f+g) h=twoPair f h+twoPair g h := by
  simp only [twoPair,Pi.add_apply,pair_add_l,Finset.sum_add_distrib]
private theorem two_add_r (f g h : Two) : twoPair f (g+h)=twoPair f g+twoPair f h := by
  simp only [twoPair,Pi.add_apply,pair_add_r,Finset.sum_add_distrib]
private theorem two_sub_l (f g h : Two) : twoPair (f-g) h=twoPair f h-twoPair g h := by
  simp only [twoPair,Pi.sub_apply,pair_sub_l,Finset.sum_sub_distrib]
private theorem two_sub_r (f g h : Two) : twoPair f (g-h)=twoPair f g-twoPair f h := by
  simp only [twoPair,Pi.sub_apply,pair_sub_r,Finset.sum_sub_distrib]
private theorem two_smul_l (c : ℂ) (f g : Two) : twoPair (c • f) g=star c*twoPair f g := by
  simp only [twoPair,Pi.smul_apply,pair_smul_l,Finset.mul_sum]
private theorem two_smul_r (c : ℂ) (f g : Two) : twoPair f (c • g)=c*twoPair f g := by
  simp only [twoPair,Pi.smul_apply,pair_smul_r,Finset.mul_sum]
private theorem two_zero_l (g : Two) : twoPair 0 g=0 := by
  simp only [twoPair,Pi.zero_apply,sourcePair,map_zero,inner_zero_left,Finset.sum_const_zero]
private theorem two_zero_r (g : Two) : twoPair g 0=0 := by
  simp only [twoPair,Pi.zero_apply,sourcePair,map_zero,inner_zero_right,Finset.sum_const_zero]
private theorem two_star (f g : Two) : star (twoPair f g)=twoPair g f := by
  simp only [twoPair,star_sum,pair_star]
private theorem compression_pair (F : Index) : GaussCoframeForm.Paired (compressionCore F) (compressionCore F) := by
  intro f g
  have he(q : QuantumTest):embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F _ _).symm
private theorem two_compression_pair (F : Index) (f g : Two) :
    twoPair f (twoCompression F g)=twoPair (twoCompression F f) g := by
  unfold twoPair
  apply Finset.sum_congr rfl;intro i _
  exact compression_pair F _ _
private def signedMiddle (t : ℝ) : End := H0-(t : ℂ) • 1
private theorem middle_pair (t : ℝ) : GaussCoframeForm.Paired (signedMiddle t) (signedMiddle t) := by
  intro f g
  change sourcePair f (H0 g-(t : ℂ) • g)=sourcePair (H0 f-(t : ℂ) • f) g
  rw [pair_sub_l,pair_sub_r,pair_smul_l,pair_smul_r]
  have ht:star (t : ℂ)=(t : ℂ) := Complex.conj_ofReal t
  rw [ht,diagonalAction_pair]

private def covariance (m ell : ℕ) (t : ℝ) : TwoEnd :=
  (columnAdjoint m ell).comp ((signedMiddle t).comp (column m ell))
private theorem covariance_pair (m ell : ℕ) (t : ℝ) (f g : Two) :
    twoPair f (covariance m ell t g)=twoPair (covariance m ell t f) g := by
  change twoPair f (columnAdjoint m ell (signedMiddle t (column m ell g)))=
    twoPair (columnAdjoint m ell (signedMiddle t (column m ell f))) g
  rw [←column_pair,column_adj_pair,middle_pair]
private def doubleCompression (F : Index) (X : TwoEnd) : TwoEnd :=
  twoCompression F*(twoCompression F*X-X*twoCompression F)-
    (twoCompression F*X-X*twoCompression F)*twoCompression F
private theorem second_green (C X : TwoEnd)
    (hC : ∀f g,twoPair f (C g)=twoPair (C f) g)
    (hX : ∀f g,twoPair f (X g)=twoPair (X f) g)
    (q g : Two) (z : ℂ) (hq : C q=g+z • q) (hXg : X g=0) :
    (twoPair q ((C*(C*X-X*C)-(C*X-X*C)*C) q)).re=
      2*(twoPair (C g) (X q)).re-4*z.im^2*(twoPair q (X q)).re := by
  have hg:twoPair g (X q)=0 := by rw [hX,hXg,two_zero_l]
  have hs:twoPair q (X (C g))=star (twoPair (C g) (X q)) := by rw [two_star,hX]
  have hd:z-star z=2*Complex.I*(z.im : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
    ring
  have he:twoPair q ((C*(C*X-X*C)-(C*X-X*C)*C) q)=
      twoPair (C g) (X q)+twoPair q (X (C g))+(z-star z)^2*twoPair q (X q) := by
    have hC2:C (C q)=C g+z • g+z^2 • q := by
      rw [hq,map_add,map_smul,hq,smul_add,pow_two,mul_smul]
      module
    have hxx:X (C q)=z • X q := by rw [hq,map_add,map_smul,hXg,zero_add]
    have hCxx:C (X (C q))=z • C (X q) := by rw [hxx,map_smul]
    have hXC2:X (C (C q))=X (C g)+z^2 • X q := by
      rw [hC2,map_add,map_add,map_smul,map_smul,hXg,smul_zero,add_zero]
    change twoPair q (C (C (X q)-X (C q))-(C (X (C q))-X (C (C q))))=_
    rw [map_sub,two_sub_r,two_sub_r,two_sub_r,hCxx,hXC2,two_add_r,
      two_smul_r,two_smul_r,hC,hC,hC]
    rw [hC2,two_add_l,two_add_l,two_smul_l,two_smul_l,hq,two_add_l,two_smul_l,hg]
    simp only [star_pow]
    ring
  rw [he,hs,hd]
  have hp:(2*Complex.I*(z.im : ℂ))^2=(-4*z.im^2 : ℝ) := by
    calc _=4*(Complex.I*Complex.I)*(z.im : ℂ)^2 := by ring
         _=_ := by rw [Complex.I_mul_I];push_cast;ring
  rw [hp]
  have hr(x y : ℂ)(s : ℝ):(x+star x+(s : ℂ)*y).re=2*x.re+s*y.re := by
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,Complex.star_def,Complex.conj_re]
    ring
  calc
    _=2*(twoPair (C g) (X q)).re+(-4*z.im^2)*(twoPair q (X q)).re := hr _ _ _
    _=_ := by ring

private def twoStates (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : Two :=
  fun i=>state F z hz (inputSeed g i)
private theorem column_states (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    column m ell (twoStates F z hz g)=A (normalizedState m ell F z hz g) := by
  simp only [column,twoStates,LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_two]
  change A (T m ell (state F z hz g))+A (-(S*T m ell) (state F z hz (phiRadiusSource g)))=_
  have hr0:state F z hz g=resolventCore F z hz (coreEquiv.symm g) := by
    simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
  have hr1:state F z hz (phiRadiusSource g)=resolventCore F z hz (r (coreEquiv.symm g)) := by
    unfold resolventCore;rfl
  rw [hr0,hr1]
  change _=A (T m ell (resolventCore F z hz (coreEquiv.symm g))-
    S (T m ell (resolventCore F z hz (r (coreEquiv.symm g)))))
  simp only [Module.End.mul_apply,map_sub,map_neg]
  module
private theorem resolvent_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have he(f : QuantumTest):embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr:embed (state F z hz g)=finiteResolvent F z (g : H) := by
    unfold state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hg:embed (coreEquiv.symm g)=(g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h:=congrArg (fun R : H →L[ℂ] H=>R (g : H))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z (g : H))=(g : H) at h
  apply embed_injective
  simp only [he,hr,hg,map_add,map_smul]
  simp only [sub_apply,smul_apply,one_apply_eq_self] at h
  linear_combination (norm:=module) h
private theorem source_core_step (g : diagonal.domain) :
    coreEquiv.symm (GaussAdjointHistory.coreStep g)=H0 (coreEquiv.symm g) := by
  unfold GaussAdjointHistory.coreStep
  exact coreEquiv.symm_apply_apply _
private theorem compression_fixed (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),compressionCore F (coreEquiv.symm g)=
      coreEquiv.symm (GaussAdjointHistory.coreStep g) := by
  filter_upwards [GaussGradedCompression.eventually_exact g] with F hF
  apply embed_injective
  have he(f : QuantumTest):embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hg:embed (coreEquiv.symm g)=(g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hstep:(GaussAdjointHistory.coreStep g : H)=(diagonal g : H) := by
    unfold GaussAdjointHistory.coreStep
    rfl
  have hs:embed (coreEquiv.symm (GaussAdjointHistory.coreStep g))=(GaussAdjointHistory.coreStep g : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  calc
    embed (compressionCore F (coreEquiv.symm g))=
        GaussGradedCompression.compression F (embed (coreEquiv.symm g)) := he _
    _=GaussGradedCompression.compression F (g : H) := congrArg (GaussGradedCompression.compression F) hg
    _=(diagonal g : H) := hF
    _=embed (coreEquiv.symm (GaussAdjointHistory.coreStep g)) := hstep.symm.trans hs.symm

def secondCFWord (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  (twoPair (twoStates F z hz g) (doubleCompression F (covariance m ell z.re)
    (twoStates F z hz g))).re
def renormalizedEndpoint (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  (sourcePair (fixedColumn m ell g) (signedMiddle z.re (A (normalizedState m ell F z hz g)))).re-
    ‖embed (fixedColumn m ell g)‖^2*(z⁻¹).re

/-- The same two-seed compression returns the full signed H0 middle and its mandatory pole subtraction. -/
theorem actual_renormalized_second_CF_source (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀m ell : ℕ,∀z : ℂ,∀hz : z.im≠0,
      secondCFWord m ell F z hz g-2*‖embed (fixedColumn m ell g)‖^2*(z⁻¹).re=
        2*renormalizedEndpoint m ell F z hz g-
          4*z.im^2*(sourcePair (A (normalizedState m ell F z hz g))
            (signedMiddle z.re (A (normalizedState m ell F z hz g)))).re := by
  filter_upwards [compression_fixed g,compression_fixed (phiRadiusSource g)] with F h0 h1
  intro m ell z hz
  let G : Two:=fun i=>coreEquiv.symm (inputSeed g i)
  have hq:twoCompression F (twoStates F z hz g)=G+z • twoStates F z hz g := by
    funext i
    exact resolvent_equation F z hz (inputSeed g i)
  have hn:covariance m ell z.re G=0 := by
    change columnAdjoint m ell (signedMiddle z.re (column m ell G))=0
    rw [show column m ell G=0 from row_zero m ell g,map_zero,map_zero]
  have he:=second_green (twoCompression F) (covariance m ell z.re)
    (two_compression_pair F) (covariance_pair m ell z.re) (twoStates F z hz g) G z hq hn
  have hg:column m ell (twoCompression F G)=fixedColumn m ell g := by
    apply congrArg (column m ell)
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hpair(x : Two):twoPair x (covariance m ell z.re (twoStates F z hz g))=
      sourcePair (column m ell x) (signedMiddle z.re (A (normalizedState m ell F z hz g))) := by
    change twoPair x (columnAdjoint m ell (signedMiddle z.re (column m ell (twoStates F z hz g))))=_
    rw [←column_pair,column_states]
  rw [hpair,hpair,hg,column_states] at he
  change secondCFWord m ell F z hz g=_ at he
  unfold renormalizedEndpoint
  linear_combination (norm:=ring) he

private theorem self_pair (f : QuantumTest) : sourcePair f f=((‖embed f‖^2 : ℝ) : ℂ) := by
  simpa only [sourcePair,Complex.ofReal_pow] using!
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)
private theorem energy_im_zero (f : QuantumTest) : (sourcePair f (H0 f)).im=0 := by
  have h:sourcePair f (H0 f)=star (sourcePair f (H0 f)) := by
    rw [pair_star,diagonalAction_pair]
  have hi:=congrArg Complex.im h
  simp only [Complex.star_def,Complex.conj_im] at hi
  linarith
private theorem middle_self (t : ℝ) (f : QuantumTest) :
    sourcePair (signedMiddle t f) f=
      (((sourcePair f (H0 f)).re-t*‖embed f‖^2 : ℝ) : ℂ) := by
  have hh:sourcePair (H0 f) f=sourcePair f (H0 f):=(diagonalAction_pair f f).symm
  change sourcePair (H0 f-(t : ℂ) • f) f=_
  have ht:star (t : ℂ)=(t : ℂ) := Complex.conj_ofReal t
  rw [pair_sub_l,pair_smul_l,ht,self_pair,hh]
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  · simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,add_zero,sub_zero,energy_im_zero]
private theorem pole_correction (z : ℂ) (hz : z.im≠0) :
    z.re*((z^2)⁻¹).re-(z⁻¹).re=
      -2*z.re*z.im^2/(z.re^2+z.im^2)^2 := by
  have hd:0<z.re^2+z.im^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hz)
  have hn:Complex.normSq z=z.re^2+z.im^2 := by
    simp only [Complex.normSq_apply]
    ring
  have hn2:Complex.normSq (z^2)=(z.re^2+z.im^2)^2 := by
    rw [pow_two,Complex.normSq_mul,hn]
    ring
  rw [Complex.inv_re,Complex.inv_re,hn,hn2]
  simp only [pow_two,Complex.mul_re]
  field_simp [(ne_of_gt hd)]
  ring

def fixedSecondTester (m ell : ℕ) (g : diagonal.domain) (i : Fin 2) : QuantumTest :=
  W m ell i (Ad (H0 (fixedColumn m ell g)))
def fixedFirstTester (m ell : ℕ) (g : diagonal.domain) (i : Fin 2) : QuantumTest :=
  W m ell i (Ad (fixedColumn m ell g))
def fixedSecondResponse (i : Fin 2) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  state F z hz (GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i)))

/-- The pole-renormalized endpoint reads only the original H0-squared seeds and fixed compact tests. -/
theorem actual_renormalized_fixed_source (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀m ell : ℕ,∀z : ℂ,∀hz : z.im≠0,
      renormalizedEndpoint m ell F z hz g=
        (((z^2)⁻¹)*(∑i : Fin 2,sourcePair (fixedSecondTester m ell g i)
          (fixedSecondResponse i F z hz g))-
          ((z.re : ℂ)*((z^2)⁻¹))*(∑i : Fin 2,sourcePair (fixedFirstTester m ell g i)
            (fixedSecondResponse i F z hz g))).re-
        (sourcePair (fixedColumn m ell g) (H0 (fixedColumn m ell g))).re*((z^2)⁻¹).re-
        2*z.re*z.im^2*‖embed (fixedColumn m ell g)‖^2/(z.re^2+z.im^2)^2 := by
  filter_upwards [actual_two_step_column g] with F hF
  intro m ell z hz
  let k:=fixedColumn m ell g
  let u:=A (normalizedState m ell F z hz g)
  let q:=secondSourceColumn m ell F z hz g
  have hz0:z≠0 := by intro he;exact hz (he ▸ rfl)
  have hu:u=(z^2)⁻¹ • (q-k) := by
    have h:=congrArg (fun f : QuantumTest=>(z^2)⁻¹ • f) (hF m ell z hz)
    change (z^2)⁻¹ • (z^2 • u)=(z^2)⁻¹ • (q-k) at h
    simpa only [←mul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hz0),one_smul] using h
  have hq(f : QuantumTest):sourcePair f q=
      ∑i : Fin 2,sourcePair (W m ell i (Ad f)) (fixedSecondResponse i F z hz g) := by
    change sourcePair f (column m ell (fun i=>fixedSecondResponse i F z hz g))=_
    rw [←column_adj_pair]
    rfl
  have he:sourcePair k (signedMiddle z.re u)=
      (z^2)⁻¹*(sourcePair (signedMiddle z.re k) q-sourcePair (signedMiddle z.re k) k) := by
    rw [middle_pair,hu,pair_smul_r,pair_sub_r]
  have hmain:sourcePair (signedMiddle z.re k) q=
      (∑i : Fin 2,sourcePair (fixedSecondTester m ell g i) (fixedSecondResponse i F z hz g))-
      (z.re : ℂ)*(∑i : Fin 2,sourcePair (fixedFirstTester m ell g i) (fixedSecondResponse i F z hz g)) := by
    change sourcePair (H0 k-(z.re : ℂ) • k) q=_
    rw [pair_sub_l,pair_smul_l,Complex.star_def,Complex.conj_ofReal,hq,hq]
    rfl
  unfold renormalizedEndpoint
  change (sourcePair k (signedMiddle z.re u)).re-‖embed k‖^2*(z⁻¹).re=_
  rw [he,hmain,middle_self,mul_sub]
  have hp:=pole_correction z hz
  have hreal(a b c : ℝ)(x : ℂ):
      (x*((a-b*c : ℝ) : ℂ)).re=x.re*a-b*c*x.re := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    ring
  rw [Complex.sub_re,hreal]
  simp only [mul_sub,mul_assoc]
  dsimp only [k]
  linear_combination (norm:=ring) (‖embed (fixedColumn m ell g)‖^2)*hp

end LowEnergy.SourceClockPhiRenormalizedSecondGreen
