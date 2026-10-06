import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeJet
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeDivergence
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaSpinJointForce

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaSpinNativeAbsorption
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourcePhysicalKineticSquare
open SourceClockYukawaSpinNativeBudget SourceClockYukawaSpinJointForce
open SourceClockReflectedForm SourceRelativePowerTail SourceEscapeSeedTail
open SourceLocalizedInverseFormPayment FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] jointState jointForcing spinWord

abbrev inputSource (g : diagonal.domain) := SourceClockYukawaRadialMixedBudget.radiusSource g

def nativeWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu => (-Complex.I) • ∑ a : ScalarIndex,
  GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth
    (rightNativeCoefficient sharp mu a m ell F z hz (inputSource g)))

def coefficientEnergy (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  ∑ mu : Fin 8,∑ a : ScalarIndex,‖embed (rightNativeCoefficient sharp mu a m ell F z hz (inputSource g))‖^2

def scalarColumn (q : Column) : ℝ := ∑ mu : Fin 8,scalarForm (inverseVolumeAction (q mu))

private theorem native_inverse (v : Ambient) : Commute (covariantMomentum v) inverseVolumeAction := by
  have h := SourceHamiltonianVolume.native_momentum_volume v
  have hVU : Commute inverseVolumeAction SourceCoframeVolume.volumeAction := by
    unfold inverseVolumeAction
    exact SourceHamiltonianVolume.real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (SourceCoframeVolume.volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem native_row_pair (a : ScalarIndex) (p f : QuantumTest) :
    sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth f))=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) (inverseVolumeAction p)) f := by
  rw [GaussNativeForm.adjoint_pair,weight_inverse,LinearMap.smul_apply]
  rw [show sourcePair (covariantMomentum (scalarDirection a) p) ((-(sourceTime 0:ℂ)) • inverseVolumeAction f)=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f) by
        simp only [sourcePair,map_smul,inner_smul_right]]
  have hp : sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f)=
      sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) p)) f := multiply_pair _ _ _ _
  have hc := LinearMap.congr_fun (native_inverse (scalarDirection a)).eq p
  change covariantMomentum (scalarDirection a) (inverseVolumeAction p)=
    inverseVolumeAction (covariantMomentum (scalarDirection a) p) at hc
  rw [hp,←hc]


private theorem native_pair (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (q : Column) :
    (∑ mu : Fin 8,sourcePair (q mu) (nativeWord sharp m ell F z hz g mu))=
      (Complex.I*(sourceTime 0:ℂ))*(∑ mu : Fin 8,∑ a : ScalarIndex,
        sourcePair (covariantMomentum (scalarDirection a) (inverseVolumeAction (q mu)))
          (rightNativeCoefficient sharp mu a m ell F z hz (inputSource g))) := by
  have h (mu : Fin 8) : sourcePair (q mu) (nativeWord sharp m ell F z hz g mu)=
      (Complex.I*(sourceTime 0:ℂ))*(∑ a : ScalarIndex,
        sourcePair (covariantMomentum (scalarDirection a) (inverseVolumeAction (q mu)))
          (rightNativeCoefficient sharp mu a m ell F z hz (inputSource g))) := by
    unfold nativeWord
    simp only [sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
    change (-Complex.I)*(∑ a : ScalarIndex,sourcePair (q mu)
      (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth
        (rightNativeCoefficient sharp mu a m ell F z hz (inputSource g)))))=_
    simp_rw [native_row_pair]
    rw [←Finset.mul_sum]
    simp only [sourcePair]
    ring
  simp only [h,←Finset.mul_sum]

private theorem gram_bound {ι : Type*} [Fintype ι] (p q : ι → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤ (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (𝕜 := ℂ) (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem native_square (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (q : Column) :
    ‖∑ mu : Fin 8,sourcePair (q mu) (nativeWord sharp m ell F z hz g mu)‖^2 ≤
      (sourceTime 0)^2*scalarColumn q*coefficientEnergy sharp m ell F z hz g := by
  rw [native_pair,norm_mul,mul_pow]
  have hn : ‖Complex.I*(sourceTime 0:ℂ)‖^2=(sourceTime 0)^2 := by
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [hn]
  have h := gram_bound (fun i : Fin 8×ScalarIndex =>
      covariantMomentum (scalarDirection i.2) (inverseVolumeAction (q i.1)))
    (fun i : Fin 8×ScalarIndex => rightNativeCoefficient sharp i.1 i.2 m ell F z hz (inputSource g))
  simp only [Fintype.sum_prod_type] at h
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by
    simp only [scalarColumn,scalarForm,coefficientEnergy,mul_assoc])

private theorem young_square (a p e η : ℝ) (hp : 0≤p) (he : 0≤e) (hη : 0<η)
    (hs : a^2≤p*e) : a≤η*p+e/(4*η) := by
  have hi : 4*(η*p)*(e/(4*η))=p*e := by field_simp [hη.ne']
  have hr : 0≤η*p+e/(4*η) := add_nonneg (mul_nonneg hη.le hp) (div_nonneg he (by positivity))
  nlinarith only [hs,hi,hr,sq_nonneg (η*p-e/(4*η))]

/-- The same eight coherent states pay the whole native divergence from their positive scalar slot. -/
theorem actual_joint_native_pair_price (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ‖∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu) (nativeWord sharp m ell F z hz g mu)‖ ≤
      η*((sourceTime 0)^2*scalarColumn (jointState sharp m ell F z hz g))+
        coefficientEnergy sharp m ell F z hz g/(4*η) := by
  have hp : 0 ≤ (sourceTime 0)^2*scalarColumn (jointState sharp m ell F z hz g) :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have he : 0 ≤ coefficientEnergy sharp m ell F z hz g :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact young_square _ _ _ η hp he hη (native_square sharp m ell F z hz g (jointState sharp m ell F z hz g))

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line_im] using hμ.ne'

def nativeBudget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : ENNReal := ∫⁻ w : ℝ,ENNReal.ofReal ((sourceTime 0)^2*
      scalarColumn (jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g))

/-- The whole native forcing is paid at one cutoff before both sharp branches on the original source filter. -/
theorem actual_joint_native_common_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal ‖∑ mu : Fin 8,sourcePair
          (jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)
          (nativeWord sharp m ell F (line μ w) (line_nonreal μ hμ w) g mu)‖) ≤
            ENNReal.ofReal ε+ENNReal.ofReal η*nativeBudget sharp m ell F μ hμ g := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_joint_native_coefficient_tail μ hμ (inputSource g) (4*η*ε) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro sharp
  let E := fun w : ℝ => coefficientEnergy sharp m ell F (line μ w) (line_nonreal μ hμ w) g
  let P := fun w : ℝ => (sourceTime 0)^2*scalarColumn
    (jointState sharp m ell F (line μ w) (line_nonreal μ hμ w) g)
  have he (w : ℝ) : 0 ≤ E w := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hp (w : ℝ) : 0 ≤ P w := mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hC : 0 ≤ 1/(4*η) := by positivity
  have me : Measurable (fun w : ℝ => ENNReal.ofReal (E w)) :=
    actual_joint_native_energy_measurable sharp m ell F μ hμ (inputSource g)
  have hb : (∫⁻ w : ℝ,ENNReal.ofReal (E w)) ≤ ENNReal.ofReal (4*η*ε) := hF sharp
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal η*ENNReal.ofReal (P w)+
        ENNReal.ofReal (1/(4*η))*ENNReal.ofReal (E w) := by
      apply lintegral_mono
      intro w
      have h := actual_joint_native_pair_price sharp m ell F (line μ w) (line_nonreal μ hμ w) g η hη
      apply (ENNReal.ofReal_le_ofReal h).trans
      change ENNReal.ofReal (η*P w+E w/(4*η)) ≤ _
      rw [show E w/(4*η)=(1/(4*η))*E w by ring,
        ENNReal.ofReal_add (mul_nonneg hη.le (hp w)) (mul_nonneg hC (he w)),
        ENNReal.ofReal_mul (q := P w) hη.le,ENNReal.ofReal_mul (q := E w) hC]
    _ = ENNReal.ofReal η*nativeBudget sharp m ell F μ hμ g+
        ENNReal.ofReal (1/(4*η))*(∫⁻ w : ℝ,ENNReal.ofReal (E w)) := by
      rw [lintegral_add_right _ (me.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ENNReal.ofReal η*nativeBudget sharp m ell F μ hμ g+
        ENNReal.ofReal (1/(4*η))*ENNReal.ofReal (4*η*ε) :=
      add_le_add le_rfl (mul_le_mul le_rfl hb zero_le zero_le)
    _ = _ := by
      rw [←ENNReal.ofReal_mul hC]
      have heq : 1/(4*η)*(4*η*ε)=ε := by field_simp [hη.ne']
      rw [heq,add_comm]


open SourceInverseNeutralScalarCurrent SourceClockYukawaSpinClosure SourceClockYukawaCubicCurrent
open SourceClockYukawaRadialCoefficient SourceClockYukawaSpinNativeDivergence GaussQuantumMultiplier

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore
  exact state_embed F z hz (coreEquiv f)

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem radial_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radialCore F z hz g)=SourceRadiusResponseDecay.response F z (g:H) := by
  rw [radialCore,state_embed]
  change finiteResolvent F z (embed (SourceRadiusResponseDecay.radialCurrent F (state F z hz g)))=_
  rw [SourceRadiusResponseDecay.original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←inverse_core,state_embed]
  simp only [SourceRadiusResponseDecay.response,mul_apply_eq_comp,sub_apply,map_sub]

private theorem root_embed (g : diagonal.domain) : embed (inputCore g)=(inputSource g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem radial_map_return (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    radialMap F z hz (inputCore g)=radialCore F z hz (inputSource g) := by
  apply embed_injective
  rw [radial_embed,SourceRadiusResponseDecay.actual_response_difference F z hz]
  simp only [radialMap,Module.End.mul_apply,LinearMap.sub_apply,map_sub,←inverse_core,resolvent_embed,root_embed]

attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq SourceQuantumConfigurationHilbert.Mode := LinearOrder.toDecidableEq

private theorem spin_at (f : QuantumTest) (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    spinPotential f z=spinKernel z (f z) := by
  have hs (a : Fin 7) (f : QuantumTest) :
      GaussCoframeSpin.current a f z=quantized (GaussCoframeSpin.full a) (f z) := rfl
  have hn (f : QuantumTest) : GaussCoframeForm.number f z=
      quantized (Matrix.diagonal (fun _ : SourceQuantumConfigurationHilbert.Mode => (1:ℂ))) (f z) := rfl
  simp only [spinPotential,spinKernel,GaussCoframeForm.spinSquare,GaussCoframeForm.numberShift,
    LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    smul_apply,sum_apply,add_apply,hs,hn,multiply_apply,map_smul,mul_apply_eq_comp]
  module

private theorem spin_theta (m ell : ℕ) : Commute spinPotential (SourceMixedNativeReturn.thetaAction m ell) := by
  have hS : Commute spinPotential inverseAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    have hi (f : QuantumTest) : inverseAction f z=(GaussRadialDomain.reciprocal z:ℂ) • f z := rfl
    change spinPotential (inverseAction f) z=inverseAction (spinPotential f) z
    rw [spin_at,hi,hi,spin_at]
    exact map_smul _ _ _
  exact (((Commute.one_right spinPotential).sub_right hS).pow_right _).sub_right
    (((Commute.one_right spinPotential).sub_right hS).pow_right _)

private theorem spin_cutoff (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    bracket spinPotential (cutoffCore sharp m ell mu)=
      bracket spinPotential (spinClosureCoefficient sharp mu)*SourceMixedNativeReturn.thetaAction m ell := by
  have h := (spin_theta m ell).eq
  unfold cutoffCore bracket
  linear_combination (norm := noncomm_ring) spinClosureCoefficient sharp mu*h

private theorem spin_word_return (sharp : Bool) (mu : Fin 8) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    bracket spinPotential (cutoffCore sharp m ell mu) (radialCore F z hz (inputSource g))=
      spinWord sharp m ell F z hz g mu := by
  rw [spin_cutoff]
  unfold spinWord windowState
  rw [radial_map_return]
  rfl

def nonScalarCurrent (sharp : Bool) (mu : Fin 8) (m ell : ℕ) : End :=
  bracket (diagonalAction-scalarKinetic-spinPotential) (cutoffCore sharp m ell mu)

def remainingWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  let rS := radialCore F z hz (inputSource g)
  let rA := SourceClockYukawaSpinNativeBudget.cutoffResponseCore sharp mu m ell F z hz (inputSource g)
  let q := state F z hz (inputSource g)
  scalarZeroOrderWord sharp mu m ell rS rA q+nonScalarCurrent sharp mu m ell rS-
    bracket (defectAction F) (cutoffCore sharp m ell mu) rS-
    bracket (defectAction F) inverseAction rA+
    bracket (bracket (defectAction F) inverseAction) (cutoffCore sharp m ell mu) q

attribute [local irreducible] nonScalarCurrent remainingWord currentCore curvatureCore cutoffCore
  diagonalAction scalarKinetic spinPotential compressionCore defectAction resolventCore

private theorem current_split (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index) :
    currentCore sharp m ell F mu=
      (jointScalarCurrent sharp mu m ell-bracket (defectAction F) (cutoffCore sharp m ell mu))+
        bracket spinPotential (cutoffCore sharp m ell mu)+nonScalarCurrent sharp mu m ell := by
  rw [←original_joint_scalar_source]
  unfold currentCore nonScalarCurrent bracket
  noncomm_ring

private theorem curvature_split (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index) :
    curvatureCore sharp m ell F mu=jointCross sharp mu m ell-
      bracket (bracket (defectAction F) inverseAction) (cutoffCore sharp m ell mu) := by
  unfold curvatureCore
  rw [original_joint_radial_cross]

private theorem core_source (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    resolventCore F z hz (coreEquiv.symm g)=state F z hz g := by
  unfold resolventCore
  change state F z hz (coreEquiv (coreEquiv.symm g))=_
  rw [coreEquiv.apply_symm_apply]

/-- The actual full forcing loses precisely its paid spin and scalar divergence;
all remaining coframe, matter, gamma, and compression terms keep their original signed word. -/
theorem actual_joint_native_forcing_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (mu : Fin 8) :
    jointForcing sharp m ell F z hz g mu=
      spinWord sharp m ell F z hz g mu+nativeWord sharp m ell F z hz g mu+
        remainingWord sharp m ell F z hz g mu := by
  let rS := radialCore F z hz (inputSource g)
  let rA := SourceClockYukawaSpinNativeBudget.cutoffResponseCore sharp mu m ell F z hz (inputSource g)
  let q := state F z hz (inputSource g)
  have h := actual_joint_scalar_forcing sharp mu m ell F rS rA q
  have hr : resolventCore F z hz (SourceRadiusResponseDecay.radialCurrent F
      (resolventCore F z hz (inputCore g)))=rS := by
    rw [inputCore,core_source]
    unfold rS radialCore resolventCore
    rfl
  have ha : resolventCore F z hz (currentCore sharp m ell F mu
      (resolventCore F z hz (inputCore g)))=rA := rfl
  have hq : resolventCore F z hz (inputCore g)=q := core_source F z hz (inputSource g)
  have hn : nativeDivergenceWord sharp mu m ell rS rA=nativeWord sharp m ell F z hz g mu := rfl
  unfold jointForcing
  change currentCore sharp m ell F mu (resolventCore F z hz (SourceRadiusResponseDecay.radialCurrent F
      (resolventCore F z hz (inputCore g))))+
    SourceRadiusResponseDecay.radialCurrent F (resolventCore F z hz (currentCore sharp m ell F mu
      (resolventCore F z hz (inputCore g))))-
    curvatureCore sharp m ell F mu (resolventCore F z hz (inputCore g))=_
  rw [hr,ha,hq,current_split,curvature_split]
  simp only [LinearMap.add_apply]
  have hs := spin_word_return sharp mu m ell F z hz g
  change bracket spinPotential (cutoffCore sharp m ell mu) rS=spinWord sharp m ell F z hz g mu at hs
  rw [hs]
  rw [hn] at h
  unfold remainingWord
  linear_combination (norm := module) h

end LowEnergy.SourceClockYukawaSpinNativeAbsorption
