import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeSourceLeg
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarGaugeForce
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarInverseInsertion
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarInverseLocalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseCompressionCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open GaussMatterCore GaussQuantumMultiplier SourceCoframeVolumeCurrent SourceDilationRemainder
open SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarGaugeForce SourceScalarDoubleCurrent
open SourceScalarInverseInsertion SourceScalarInverseLocalization SourceMixedNativeReturn
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def matterInsertion (sharp : Bool) (m ell : ℕ) : End :=
  bracket matterAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell)

def matterHamiltonianCurrent (sharp : Bool) (m ell : ℕ) : End :=
  bracket diagonalAction (matterInsertion sharp m ell)

attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic matterAction
  GaussCoframeForm.coframeAction deltaGauge matterInsertion matterHamiltonianCurrent
  sourceRead compressedOscillatorForce oscillatorForce doubleProjectionFlux
  SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction cutoffEuler scaleDoubleRemainder constantAction

private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  unfold deltaGauge
  change SourceGaugeRadialPair.gaugeEulerAction*(A*B)-(A*B)*SourceGaugeRadialPair.gaugeEulerAction=
    (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B+
      A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)
  noncomm_ring

private theorem gauge_bracket (A B : End) :
    deltaGauge (bracket A B)=bracket (deltaGauge A) B+bracket A (deltaGauge B) := by
  simp only [bracket,map_sub,gauge_product]
  noncomm_ring

private theorem real_local (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) :
    Commute (multiply c hc) (localMultiplier A hA) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (A z) (c z : ℂ) (f z)).symm

private theorem real_matter (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) matterAction := by
  unfold matterAction
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro b _
  exact real_local _ _ _ _

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem real_theta (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (m ell : ℕ) :
    Commute (multiply c hc) (SourceMixedNativeReturn.thetaAction m ell) := by
  unfold SourceMixedNativeReturn.thetaAction
  change Commute (multiply c hc) ((1-GaussRadialDomain.inverseAction)^(m+1)-
    (1-GaussRadialDomain.inverseAction)^(ell+1))
  rw [←SourceNativeCutoffContact.theta_action_polynomial]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)

private theorem real_matter_insertion (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (m ell : ℕ) :
    Commute (multiply c hc) (matterInsertion sharp m ell) := by
  have hi := (real_full c hc sharp).mul_right (real_theta c hc m ell)
  change Commute (multiply c hc) (SourceScalarDoubleCurrent.fullInsertion sharp m ell) at hi
  unfold matterInsertion bracket
  exact ((real_matter c hc).mul_right hi).sub_right (hi.mul_right (real_matter c hc))

/-- The entire signed spatial force vanishes against the actual local matter/Yukawa commutator. -/
private theorem original_spatial_force_zero (sharp : Bool) (m ell : ℕ) :
    bracket spatialAction (matterInsertion sharp m ell)=0 :=
  sub_eq_zero.mpr (real_matter_insertion _ _ sharp m ell).eq

private theorem gauge_theta (m ell : ℕ) : deltaGauge (SourceMixedNativeReturn.thetaAction m ell)=0 := by
  simpa only [SourceScalarInverseRetardedBudget.theta,SourceNativeCutoffContact.theta_action_polynomial,
    SourceMixedNativeReturn.thetaAction] using! original_theta_gauge m ell

private theorem gauge_insertion (sharp : Bool) (m ell : ℕ) :
    deltaGauge (SourceScalarDoubleCurrent.fullInsertion sharp m ell)=0 := by
  rw [SourceScalarDoubleCurrent.fullInsertion,gauge_product,original_full_gauge_jet,gauge_theta,
    zero_mul,mul_zero,add_zero]

private theorem gauge_matter_insertion (sharp : Bool) (m ell : ℕ) :
    deltaGauge (matterInsertion sharp m ell)=matterInsertion sharp m ell := by
  rw [matterInsertion,gauge_bracket,original_matter_gauge,gauge_insertion]
  simp only [bracket,mul_zero,zero_mul,sub_self,add_zero]

private theorem current_split (sharp : Bool) (m ell : ℕ) :
    matterHamiltonianCurrent sharp m ell=
      bracket (scalarKinetic+GaussCoframeForm.coframeAction) (matterInsertion sharp m ell)+
      bracket gaugeKinetic (matterInsertion sharp m ell)+bracket matterAction (matterInsertion sharp m ell) := by
  have hp := (real_matter_insertion potential potential_smooth sharp m ell).eq
  have hH : diagonalAction=scalarKinetic+gaugeKinetic+multiply potential potential_smooth+
      GaussCoframeForm.coframeAction+matterAction := by
    rw [diagonalAction,nativeAction]
  rw [matterHamiltonianCurrent,hH]
  unfold bracket
  linear_combination (norm := noncomm_ring) hp

private theorem bracket_weight (A B : End) (a b : ℂ)
    (ha : deltaGauge A=a • A) (hb : deltaGauge B=b • B) :
    deltaGauge (bracket A B)=(a+b) • bracket A B := by
  rw [gauge_bracket,ha,hb]
  simp only [bracket,smul_mul_assoc,mul_smul_comm]
  module

/-- The first H-current has gauge weights 1,-1,2; the original polynomial kills the other two source blocks. -/
theorem original_electric_matter_first_current (sharp : Bool) (m ell : ℕ) :
    electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)=
      (1/6 : ℂ) • (deltaGauge (deltaGauge (matterHamiltonianCurrent sharp m ell))-
        (3 : ℂ) • deltaGauge (matterHamiltonianCurrent sharp m ell)+
        (2 : ℂ) • matterHamiltonianCurrent sharp m ell) := by
  let W := matterInsertion sharp m ell
  have hW : deltaGauge W=(1 : ℂ) • W := by simp only [W,gauge_matter_insertion,one_smul]
  have hK : deltaGauge (scalarKinetic+GaussCoframeForm.coframeAction)=
      (0 : ℂ) • (scalarKinetic+GaussCoframeForm.coframeAction) := by
    rw [map_add,original_scalar_kinetic_gauge,original_coframe_gauge,add_zero,zero_smul]
  have hk := bracket_weight (scalarKinetic+GaussCoframeForm.coframeAction) W 0 1 hK hW
  have he := bracket_weight gaugeKinetic W (-2) 1 original_gauge_kinetic_gauge hW
  have hm := bracket_weight matterAction W 1 1 (by rw [original_matter_gauge,one_smul]) hW
  norm_num only [zero_add,show (-2 : ℂ)+1= -1 by norm_num,show (1 : ℂ)+1=2 by norm_num] at hk he hm
  rw [original_electric_matter_current,←matterInsertion,electricSpatial]
  change bracket (gaugeKinetic+spatialAction) W=_
  have hz : bracket spatialAction W=0 := original_spatial_force_zero sharp m ell
  have hs : bracket (gaugeKinetic+spatialAction) W=bracket gaugeKinetic W := by
    unfold bracket at hz ⊢
    linear_combination (norm := noncomm_ring) hz
  rw [hs,current_split]
  change bracket gaugeKinetic W=(1/6 : ℂ) •
    (deltaGauge (deltaGauge (bracket (scalarKinetic+GaussCoframeForm.coframeAction) W+
      bracket gaugeKinetic W+bracket matterAction W))-
      (3 : ℂ) • deltaGauge (bracket (scalarKinetic+GaussCoframeForm.coframeAction) W+
        bracket gaugeKinetic W+bracket matterAction W)+
      (2 : ℂ) • (bracket (scalarKinetic+GaussCoframeForm.coframeAction) W+
        bracket gaugeKinetic W+bracket matterAction W))
  simp only [map_add,map_smul,hk,he,hm]
  module

/-- The actual compressed oscillator force consumes the lower H-order source; every projection cross remains. -/
theorem actual_force_first_current (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    compressedOscillatorForce sharp m ell F g=
      sourceRead F g ((1/6 : ℂ) •
        (deltaGauge (deltaGauge (matterHamiltonianCurrent sharp m ell))-
          (3 : ℂ) • deltaGauge (matterHamiltonianCurrent sharp m ell)+
          (2 : ℂ) • matterHamiltonianCurrent sharp m ell)-
        (2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
        (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*SourceMixedNativeReturn.thetaAction m ell)-
        (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-doubleProjectionFlux sharp m ell F g := by
  simp only [compressedOscillatorForce,oscillatorForce,original_electric_matter_first_current sharp m ell]

private theorem theta_matter (m ell : ℕ) :
    Commute (SourceMixedNativeReturn.thetaAction m ell) matterAction := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact real_matter _ _

private theorem theta_full (sharp : Bool) (m ell : ℕ) :
    Commute (SourceMixedNativeReturn.thetaAction m ell) (SourceMixedNativeReturn.fullAction sharp) := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact real_full _ _ sharp

/-- The radial cutoff moves through the whole matter/Yukawa commutator, without producing derivative contacts. -/
theorem original_matter_insertion_radial (sharp : Bool) (m ell : ℕ) :
    matterInsertion sharp m ell=SourceMixedNativeReturn.thetaAction m ell*
      bracket matterAction (SourceMixedNativeReturn.fullAction sharp) := by
  have hm := (theta_matter m ell).eq
  have hy := (theta_full sharp m ell).eq
  rw [matterInsertion,SourceScalarDoubleCurrent.fullInsertion]
  unfold bracket
  calc
    _=matterAction*(SourceMixedNativeReturn.thetaAction m ell*SourceMixedNativeReturn.fullAction sharp)-
      SourceMixedNativeReturn.thetaAction m ell*(SourceMixedNativeReturn.fullAction sharp*matterAction) := by
        rw [←hy]
        noncomm_ring
    _=_ := by rw [←mul_assoc,←hm];noncomm_ring

/-- Each endpoint uses only its own fixed actual core input. -/
theorem original_matter_insertion_fixed_tail (sharp : Bool) (f : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ‖embed (matterInsertion sharp m ell f)‖ < ε := by
  have he (m ell : ℕ) : embed (matterInsertion sharp m ell f)=
      SourceRelativePowerTail.relativeTail m ell
        (embed (bracket matterAction (SourceMixedNativeReturn.fullAction sharp) f)) := by
    rw [original_matter_insertion_radial]
    change embed (SourceMixedNativeReturn.thetaAction m ell
      (bracket matterAction (SourceMixedNativeReturn.fullAction sharp) f))=_
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,
      SourceNativeCutoffContact.theta_core]
  simpa only [he] using! SourceHardyRetardedTail.original_relative_tail
    (embed (bracket matterAction (SourceMixedNativeReturn.fullAction sharp) f))

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.thetaAction m ell g)=
      sourcePair (SourceMixedNativeReturn.thetaAction m ell f) g := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact multiply_pair _ _ _ _

private theorem insertion_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (SourceScalarDoubleCurrent.fullInsertion sharp m ell g)=
      sourcePair (SourceScalarDoubleCurrent.fullInsertion (!sharp) m ell f) g := by
  change sourcePair f (SourceMixedNativeReturn.fullAction sharp (SourceMixedNativeReturn.thetaAction m ell g))=_
  rw [full_pair,theta_pair]
  exact congrArg (fun v => sourcePair v g) (LinearMap.congr_fun (theta_full (!sharp) m ell).eq f)

/-- The independent adjoint is the opposite branch with the commutator sign; no Hermitian W is assumed. -/
theorem original_matter_insertion_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (matterInsertion sharp m ell g)= -sourcePair (matterInsertion (!sharp) m ell f) g := by
  rw [matterInsertion,matterInsertion]
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  have hr (a b c : QuantumTest) : sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
    simp only [sourcePair,map_sub,inner_sub_right]
  have hl (a b c : QuantumTest) : sourcePair (a-b) c=sourcePair a c-sourcePair b c := by
    simp only [sourcePair,map_sub,inner_sub_left]
  rw [hr,hl,matter_pair,insertion_pair,insertion_pair,matter_pair]
  ring

open SourceScalarPairedTransport SourceScalarPositiveBulkWard FullYSourceResolventGraphSplice
open SourceResolventBandLimit SourceInverseSourceLeg
attribute [local irreducible] state sourcePair defectAction

private theorem pair_add_left (a b c : QuantumTest) : sourcePair (a+b) c=sourcePair a c+sourcePair b c := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_right (a b c : QuantumTest) : sourcePair a (b+c)=sourcePair a b+sourcePair a c := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_left (c : ℂ) (a b : QuantumTest) : sourcePair (c • a) b=star c*sourcePair a b := by
  simp only [sourcePair,map_smul,inner_smul_left,Complex.star_def]
private theorem pair_smul_right (c : ℂ) (a b : QuantumTest) : sourcePair a (c • b)=c*sourcePair a b := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sub_right (a b c : QuantumTest) : sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem actual_equation (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    diagonalAction (state F z hz g)=coreEquiv.symm g+z • state F z hz g+defectAction F (state F z hz g) := by
  simpa only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,zero_add]
    using! actual_raised_source F z hz g (1 : End)

/-- Two actual source frequencies retain conj(zl)-zr and both complete linear defects. -/
theorem actual_first_source_current (sharp : Bool) (m ell : ℕ) (F : Index)
    (zl zr : ℂ) (hl : zl.im ≠ 0) (hr : zr.im ≠ 0) (g k : diagonal.domain) :
    sourcePair (state F zl hl k) (matterHamiltonianCurrent sharp m ell (state F zr hr g))=
      sourcePair (coreEquiv.symm k) (matterInsertion sharp m ell (state F zr hr g))-
      sourcePair (state F zl hl k) (matterInsertion sharp m ell (coreEquiv.symm g))+
      (star zl-zr)*sourcePair (state F zl hl k) (matterInsertion sharp m ell (state F zr hr g))+
      sourcePair (defectAction F (state F zl hl k)) (matterInsertion sharp m ell (state F zr hr g))-
      sourcePair (state F zl hl k) (matterInsertion sharp m ell (defectAction F (state F zr hr g))) := by
  rw [matterHamiltonianCurrent]
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_right]
  rw [diagonalAction_pair,actual_equation,actual_equation]
  simp only [map_add,map_smul,pair_add_left,pair_add_right,pair_smul_left,pair_smul_right]
  ring

/-- The conjugate/nonconjugate weak response keeps the full defect difference joined to the first H-current. -/
def firstRetardedCurrent (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g k : diagonal.domain) : ℂ :=
  let hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  let p := state F (star z) hs k
  let q := state F z hz g
  sourcePair p (matterHamiltonianCurrent sharp m ell q)-
    sourcePair (defectAction F p) (matterInsertion sharp m ell q)+
    sourcePair p (matterInsertion sharp m ell (defectAction F q))

/-- Only the conjugate/nonconjugate choice cancels the frequency term. -/
theorem actual_first_retarded_endpoints (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im ≠ 0) (g k : diagonal.domain) :
    firstRetardedCurrent sharp m ell F z hz g k=
      -sourcePair (matterInsertion (!sharp) m ell (coreEquiv.symm k)) (state F z hz g)-
      sourcePair (state F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (matterInsertion sharp m ell (coreEquiv.symm g)) := by
  let hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have h := actual_first_source_current sharp m ell F (star z) z hs hz g k
  rw [star_star,sub_self,zero_mul,add_zero,
    original_matter_insertion_pair sharp m ell (coreEquiv.symm k) (state F z hz g)] at h
  rw [firstRetardedCurrent]
  linear_combination h

open MeasureTheory
open scoped ENNReal
attribute [local irreducible] firstRetardedCurrent

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem pair_bound (p q : QuantumTest) : ‖sourcePair p q‖ ≤ ‖embed p‖*‖embed q‖ := by
  unfold sourcePair
  exact norm_inner_le_norm _ _

private theorem minus_square (a b : ℂ) : ‖-a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (-a) b) 2
  rw [norm_neg] at h
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

private theorem current_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im ≠ 0) (g k : diagonal.domain) :
    ‖firstRetardedCurrent sharp m ell F z hz g k‖^2 ≤
      2*‖embed (matterInsertion (!sharp) m ell (coreEquiv.symm k))‖^2*‖finiteResolvent F z (g : H)‖^2+
      2*‖embed (matterInsertion sharp m ell (coreEquiv.symm g))‖^2*‖finiteResolvent F z (k : H)‖^2 := by
  let hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have ha := pow_le_pow_left₀ (norm_nonneg _)
    (pair_bound (matterInsertion (!sharp) m ell (coreEquiv.symm k)) (state F z hz g)) 2
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (pair_bound (state F (star z) hs k) (matterInsertion sharp m ell (coreEquiv.symm g))) 2
  simp only [mul_pow,state_embed,actual_conjugate_leg_norm F z hz] at ha hb
  rw [actual_first_retarded_endpoints]
  have ht := minus_square
    (sourcePair (matterInsertion (!sharp) m ell (coreEquiv.symm k)) (state F z hz g))
    (sourcePair (state F (star z) hs k) (matterInsertion sharp m ell (coreEquiv.symm g)))
  nlinarith only [ht,ha,hb]

/-- The complete linear defect correction is included before taking the whole-frequency energy. -/
theorem actual_first_retarded_energy (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖firstRetardedCurrent sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤
      ENNReal.ofReal ((2*Real.pi/μ)*
        (‖embed (matterInsertion (!sharp) m ell (coreEquiv.symm k))‖^2*‖(g : H)‖^2+
          ‖embed (matterInsertion sharp m ell (coreEquiv.symm g))‖^2*‖(k : H)‖^2)) := by
  let L := 2*‖embed (matterInsertion (!sharp) m ell (coreEquiv.symm k))‖^2
  let G := 2*‖embed (matterInsertion sharp m ell (coreEquiv.symm g))‖^2
  have hL : 0 ≤ L := by dsimp [L];positivity
  have hG : 0 ≤ G := by dsimp [G];positivity
  have he (u : H) : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) u‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖u‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ u
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal L*
      ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2)) := by
    exact measurable_const.mul
      ((((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal L*ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2)+
        ENNReal.ofReal G*ENNReal.ofReal (‖finiteResolvent F (line μ w) (k : H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hL,←ENNReal.ofReal_mul hG,
        ←ENNReal.ofReal_add (mul_nonneg hL (sq_nonneg _)) (mul_nonneg hG (sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (current_bound sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k)
    _=ENNReal.ofReal L*(∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2))+
        ENNReal.ofReal G*(∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (k : H)‖^2)) := by
      rw [lintegral_add_left hm,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _=_ := by
      have hx := congrArg₂ (fun a b : ℝ≥0∞ => ENNReal.ofReal L*a+ENNReal.ofReal G*b)
        (he (g : H)) (he (k : H))
      have hy := congrArg₂ (fun a b : ℝ≥0∞ => a+b)
        (ENNReal.ofReal_mul (p := L) (q := (Real.pi/μ)*‖(g : H)‖^2) hL).symm
        (ENNReal.ofReal_mul (p := G) (q := (Real.pi/μ)*‖(k : H)‖^2) hG).symm
      have hn : 0 ≤ L*((Real.pi/μ)*‖(g : H)‖^2) := by positivity
      have ho : 0 ≤ G*((Real.pi/μ)*‖(k : H)‖^2) := by positivity
      apply (hx.trans (hy.trans (ENNReal.ofReal_add hn ho).symm)).trans
      apply congrArg ENNReal.ofReal
      dsimp [L,G]
      ring

/-- One threshold pays the whole first-source current for every F and upper cutoff; projection defects stay joined. -/
theorem actual_first_retarded_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖firstRetardedCurrent sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := (2*Real.pi/μ)*(1+‖(g : H)‖^2+‖(k : H)‖^2)
  have hC : 0 < C := by dsimp [C];positivity
  let δ := Real.sqrt (ε/C)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (div_pos hε hC)
  have hδ2 : δ^2=ε/C := Real.sq_sqrt (div_pos hε hC).le
  obtain ⟨Ng,hg⟩ := original_matter_insertion_fixed_tail sharp (coreEquiv.symm g) δ hδ
  obtain ⟨Nk,hk⟩ := original_matter_insertion_fixed_tail (!sharp) (coreEquiv.symm k) δ hδ
  refine ⟨max Ng Nk,fun m hm ell hell F => (actual_first_retarded_energy sharp m ell F μ hμ g k).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hgs := pow_le_pow_left₀ (norm_nonneg _) (hg m ((le_max_left _ _).trans hm) ell hell).le 2
  have hks := pow_le_pow_left₀ (norm_nonneg _) (hk m ((le_max_right _ _).trans hm) ell hell).le 2
  calc
    _ ≤ (2*Real.pi/μ)*(δ^2*‖(g : H)‖^2+δ^2*‖(k : H)‖^2) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hks (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hgs (sq_nonneg _))) (by positivity)
    _ ≤ C*δ^2 := by dsimp [C];nlinarith [sq_nonneg δ,show 0 < 2*Real.pi/μ by positivity]
    _=ε := by rw [hδ2];exact mul_div_cancel₀ ε hC.ne'

end LowEnergy.SourceInverseCompressionCurrent
