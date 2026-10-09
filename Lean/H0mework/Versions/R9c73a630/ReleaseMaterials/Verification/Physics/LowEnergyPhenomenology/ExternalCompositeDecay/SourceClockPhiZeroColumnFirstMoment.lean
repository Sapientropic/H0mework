import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRenormalizedSecondGreenTail
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherChannelGap
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceBulkTwoTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiZeroColumnFirstMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceClockPhiNativeJointPayment
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceInverseNoetherChannelGap SourceInverseElectricMomentChannels
open SourceBulkTwoTime SourceResolventBandLimit SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceClockYukawaCubicCurrent
open SourceScalarPairedTransport SourceLocalizedInverseFormPayment SourceScalarPositiveBulkWard
open SourceInverseJetEnergy FullYSourceResolventGraphSplice
open MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev A : End := combinedConjugate
private abbrev H0 : End := diagonalAction
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
attribute [local irreducible] diagonalAction compressionCore defectAction state

private theorem pair_smul_l (c : ℂ) (f g : QuantumTest) :
    sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r (c : ℂ) (f g : QuantumTest) :
    sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sum_l {ι : Type*} [Fintype ι] (v : ι → QuantumTest) (f : QuantumTest) :
    sourcePair (∑i,v i) f=∑i,sourcePair (v i) f := by
  simp only [sourcePair,map_sum,sum_inner]
private theorem pair_sum_r {ι : Type*} [Fintype ι] (f : QuantumTest) (v : ι → QuantumTest) :
    sourcePair f (∑i,v i)=∑i,sourcePair f (v i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_zero_l (f : QuantumTest) : sourcePair 0 f=0 := by
  simp only [sourcePair,map_zero,inner_zero_left]
private theorem pair_zero_r (f : QuantumTest) : sourcePair f 0=0 := by
  simp only [sourcePair,map_zero,inner_zero_right]

private theorem channel_resolution (F : Index) (g : diagonal.domain) :
    (∑i : Channel F,channelTest F g i)=coreEquiv.symm g := by
  apply embed_injective
  have h:=actual_core_time F g 0
  simp only [coreTime,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul,
    SourceFiniteUnitary.time_zero,one_apply_eq_self] at h
  exact h.trans (congrArg Subtype.val (coreEquiv.apply_symm_apply g)).symm

private theorem inverse_theta (m ell : ℕ) : Commute S (T m ell) :=
  (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (m+1)).sub_right
    (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (ell+1))
private theorem inverse_radius : S*r=(1 : End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phiReciprocal z : ℂ) • ((phiRadius z : ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem original_zero_column (m ell : ℕ) (g : diagonal.domain) :
    (∑i : Fin 2,A (phaseRow m ell i (coreEquiv.symm (inputSeed g i))))=0 := by
  simp only [Fin.sum_univ_two]
  change A (T m ell (coreEquiv.symm g))+A (-(S*T m ell) (coreEquiv.symm (phiRadiusSource g)))=0
  unfold phiRadiusSource
  rw [coreEquiv.symm_apply_apply]
  change A (T m ell (coreEquiv.symm g))+A (-(S*T m ell) (r (coreEquiv.symm g)))=0
  have he:S*T m ell*r=T m ell := by
    rw [(inverse_theta m ell).eq,mul_assoc,inverse_radius,mul_one]
  have hf:=LinearMap.congr_fun he (coreEquiv.symm g)
  change S (T m ell (r (coreEquiv.symm g)))=T m ell (coreEquiv.symm g) at hf
  simp only [Module.End.mul_apply,map_neg]
  rw [hf]
  exact add_neg_cancel _

def columnChannel (m ell : ℕ) (F : Index) (g : diagonal.domain) (j : Channel F) : QuantumTest :=
  ∑i : Fin 2,A (phaseRow m ell i (channelTest F (inputSeed g i) j))

private theorem actual_column_zero (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    (∑j : Channel F,columnChannel m ell F g j)=0 := by
  unfold columnChannel
  rw [Finset.sum_comm]
  simp_rw [←map_sum,channel_resolution]
  simpa only [map_sum] using original_zero_column m ell g

private theorem original_state_seed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    state F z hz g=resolventCore F z hz (coreEquiv.symm g) := by
  simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
private theorem actual_column_state (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    A (normalizedState m ell F z hz g)=
      ∑j : Channel F,((channelValue F j : ℂ)-z)⁻¹ • columnChannel m ell F g j := by
  have hs:A (normalizedState m ell F z hz g)=
      ∑i : Fin 2,A (phaseRow m ell i (state F z hz (inputSeed g i))) := by
    simp only [Fin.sum_univ_two]
    change A (normalizedState m ell F z hz g)=
      A (T m ell (state F z hz g))+A (-(S*T m ell) (state F z hz (phiRadiusSource g)))
    rw [original_state_seed F z hz g,original_state_seed F z hz (phiRadiusSource g)]
    unfold phiRadiusSource
    rw [coreEquiv.symm_apply_apply]
    simp only [normalizedState,Module.End.mul_apply,map_sub,map_neg]
    change A (T m ell (resolventCore F z hz (coreEquiv.symm g)))-
      A (S (T m ell (resolventCore F z hz (r (coreEquiv.symm g)))))=
      A (T m ell (resolventCore F z hz (coreEquiv.symm g)))+
      -A (S (T m ell (resolventCore F z hz (r (coreEquiv.symm g)))))
    exact sub_eq_add_neg _ _
  rw [hs]
  simp_rw [actual_state_channels,map_sum,map_smul]
  rw [Finset.sum_comm]
  simp only [columnChannel,Finset.smul_sum]

private theorem nonreal_pole_ne (a : ℝ) (z : ℂ) (hz : z.im≠0) :
    (a : ℂ)-z≠0 := by
  intro h
  have hi:=congrArg Complex.im h
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
  exact hz hi

private theorem pole_first_moment (a b : ℝ) (z : ℂ) (hz : z.im≠0) :
    (z.re : ℂ)*(star (((a : ℂ)-z)⁻¹)*((b : ℂ)-z)⁻¹)=
      (((a+b)/2 : ℝ) : ℂ)*(star (((a : ℂ)-z)⁻¹)*((b : ℂ)-z)⁻¹)-
        (star (((a : ℂ)-z)⁻¹)+((b : ℂ)-z)⁻¹)/2 := by
  rw [star_inv₀]
  push_cast
  have ha:star ((a : ℂ)-z)≠0 := star_ne_zero.mpr (nonreal_pole_ne a z hz)
  field_simp [nonreal_pole_ne b z hz,ha]
  simp only [star_sub,Complex.star_def,Complex.conj_ofReal]
  apply Complex.ext <;> simp
  ring

private theorem pair_expansion {ι : Type*} [Fintype ι] (d : ι → QuantumTest) (R : ι → ℂ) (B : End) :
    sourcePair (∑i,R i • d i) (B (∑j,R j • d j))=
      ∑i,∑j,star (R i)*R j*sourcePair (d i) (B (d j)) := by
  simp only [map_sum,map_smul,pair_sum_l,pair_sum_r,pair_smul_l,pair_smul_r,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem zero_column_single_poles {ι : Type*} [Fintype ι]
    (d : ι → QuantumTest) (R : ι → ℂ) (hd : (∑i,d i)=0) :
    (∑i,∑j,((star (R i)+R j)/2)*sourcePair (d i) (d j))=0 := by
  have hl:(∑i,∑j,star (R i)*sourcePair (d i) (d j))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [←Finset.mul_sum,←pair_sum_r,hd,pair_zero_r,mul_zero]
  have hr:(∑i,∑j,R j*sourcePair (d i) (d j))=0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [←Finset.mul_sum,←pair_sum_l,hd,pair_zero_l,mul_zero]
  have he:(∑i,∑j,((star (R i)+R j)/2)*sourcePair (d i) (d j))=
      ((∑i,∑j,star (R i)*sourcePair (d i) (d j))+
        (∑i,∑j,R j*sourcePair (d i) (d j)))/2 := by
    simp only [←Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,hl,hr,zero_add,zero_div]

private theorem actual_middle_transition (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    sourcePair (A (normalizedState m ell F z hz g)) (H0 (A (normalizedState m ell F z hz g)))-
      (z.re : ℂ)*sourcePair (A (normalizedState m ell F z hz g)) (A (normalizedState m ell F z hz g))=
      ∑i : Channel F,∑j : Channel F,
        star (((channelValue F i : ℂ)-z)⁻¹)*((channelValue F j : ℂ)-z)⁻¹*
          (sourcePair (columnChannel m ell F g i) (H0 (columnChannel m ell F g j))-
            (((channelValue F i+channelValue F j)/2 : ℝ) : ℂ)*
              sourcePair (columnChannel m ell F g i) (columnChannel m ell F g j)) := by
  let d:=columnChannel m ell F g
  let R:=fun i : Channel F=>((channelValue F i : ℂ)-z)⁻¹
  have hu:=actual_column_state m ell F z hz g
  have hmass:=pair_expansion d R (1 : End)
  simp only [Module.End.one_apply] at hmass
  rw [hu,pair_expansion d R H0,hmass]
  have he:(∑i,∑j,star (R i)*R j*sourcePair (d i) (H0 (d j)))-
      (z.re : ℂ)*(∑i,∑j,star (R i)*R j*sourcePair (d i) (d j))=
      (∑i,∑j,star (R i)*R j*(sourcePair (d i) (H0 (d j))-
        (((channelValue F i+channelValue F j)/2 : ℝ) : ℂ)*sourcePair (d i) (d j)))+
      (∑i,∑j,((star (R i)+R j)/2)*sourcePair (d i) (d j)) := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hp:=pole_first_moment (channelValue F i) (channelValue F j) z hz
    change (z.re : ℂ)*(star (R i)*R j)=_ at hp
    linear_combination (norm:=ring) -sourcePair (d i) (d j)*hp
  rw [he,zero_column_single_poles d R (actual_column_zero m ell F g),add_zero]

def channelTransition (m ell : ℕ) (F : Index) (g : diagonal.domain) (i j : Channel F) : ℂ :=
  sourcePair (columnChannel m ell F g i) (H0 (columnChannel m ell F g j))-
    (((channelValue F i+channelValue F j)/2 : ℝ) : ℂ)*
      sourcePair (columnChannel m ell F g i) (columnChannel m ell F g j)

def fullMiddle (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℂ :=
  let u:=A (normalizedState m ell F z hz g)
  sourcePair u (H0 u-(z.re : ℂ) • u)

/-- The original two-seed zero column cancels single poles before the first frequency moment is integrated. -/
theorem actual_original_channel_first_moment (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    (∑i : Channel F,columnChannel m ell F g i)=0 ∧
    fullMiddle m ell F z hz g=
      ∑i : Channel F,∑j : Channel F,
        star (((channelValue F i : ℂ)-z)⁻¹)*((channelValue F j : ℂ)-z)⁻¹*
          channelTransition m ell F g i j := by
  refine ⟨actual_column_zero m ell F g,?_⟩
  have h:=actual_middle_transition m ell F z hz g
  simpa only [fullMiddle,channelTransition,sourcePair,map_sub,inner_sub_right,map_smul,
    inner_smul_right] using h

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

private def causalTwoPole (advanced : Bool) (μ a b : ℝ) : ℂ :=
  if advanced then star (twoPole μ a b) else twoPole μ a b
private def causalPolePair (advanced : Bool) (μ a b w : ℝ) : ℂ :=
  star (((a : ℂ)-actualFrequency advanced μ w)⁻¹)*
    ((b : ℂ)-actualFrequency advanced μ w)⁻¹

private theorem causal_pole_pair (μ a b w : ℝ) :
    causalPolePair false μ a b w=star (pole μ a w)*pole μ b w ∧
    causalPolePair true μ a b w=star (star (pole μ a w)*pole μ b w) := by
  constructor
  · rfl
  · simp only [causalPolePair,actualFrequency,ite_true,pole,
      star_mul,star_inv₀,star_sub,Complex.star_def,Complex.conj_ofReal]
    exact mul_comm _ _

private theorem causal_pair_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0<μ) :
    Integrable (fun w : ℝ=>causalPolePair advanced μ a b w) := by
  cases advanced
  · simpa only [(causal_pole_pair μ a b _).1] using two_pole_integrable μ a b hμ
  · have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (two_pole_integrable μ a b hμ)
    have hc:Integrable (fun w : ℝ=>star (star (pole μ a w)*pole μ b w)) := by
      convert h using 1
      funext w
      rfl
    simpa only [(causal_pole_pair μ a b _).2] using hc

private theorem causal_pair_integral (advanced : Bool) (μ a b : ℝ) :
    (∫w : ℝ,causalPolePair advanced μ a b w)=causalTwoPole advanced μ a b := by
  cases advanced
  · simp only [(causal_pole_pair μ a b _).1,causalTwoPole,Bool.false_eq_true,ite_false,twoPole]
  · simp only [(causal_pole_pair μ a b _).2,causalTwoPole,ite_true,
      Complex.star_def,integral_conj,twoPole]

def closedFirstMoment (advanced : Bool) (μ : ℝ) (m ell : ℕ) (F : Index) (g : diagonal.domain) : ℂ :=
  ∑i : Channel F,∑j : Channel F,
    (if advanced then star (2*(Real.pi : ℂ)/gap μ (channelValue F i) (channelValue F j))
      else 2*(Real.pi : ℂ)/gap μ (channelValue F i) (channelValue F j))*
      channelTransition m ell F g i j

private theorem transition_integrable (μ : ℝ) (hμ : 0<μ) (advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    Integrable (fun w : ℝ=>∑i : Channel F,∑j : Channel F,
      causalPolePair advanced μ (channelValue F i) (channelValue F j) w*
        channelTransition m ell F g i j) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (causal_pair_integrable advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _

/-- Both actual causal legs have a complete full-H0 first moment, retaining every finite and escape cross coefficient. -/
theorem actual_zero_column_frequency_moment (μ : ℝ) (hμ : 0<μ) (advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    Integrable (fun w : ℝ=>fullMiddle m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g) ∧
    (∫w : ℝ,fullMiddle m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)=closedFirstMoment advanced μ m ell F g := by
  have he (w : ℝ):fullMiddle m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g=
      ∑i : Channel F,∑j : Channel F,
        causalPolePair advanced μ (channelValue F i) (channelValue F j) w*
          channelTransition m ell F g i j :=
    (actual_original_channel_first_moment m ell F _ _ g).2
  refine ⟨?_,?_⟩
  · simpa only [he] using transition_integrable μ hμ advanced m ell F g
  · simp_rw [he]
    have hrow (i : Channel F):Integrable (fun w : ℝ=>∑j : Channel F,
        causalPolePair advanced μ (channelValue F i) (channelValue F j) w*
          channelTransition m ell F g i j) := by
      apply integrable_finsetSum
      intro j _
      exact (causal_pair_integrable advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _
    rw [integral_finsetSum _ (fun i _=>hrow i)]
    unfold closedFirstMoment
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _=>(causal_pair_integrable advanced μ
      (channelValue F i) (channelValue F j) hμ).mul_const _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const,causal_pair_integral]
    unfold causalTwoPole
    rw [two_pole_closed μ (channelValue F i) (channelValue F j) hμ]

def columnTime (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) : QuantumTest :=
  ∑i : Fin 2,A (phaseRow m ell i (coreTime F (inputSeed g i) t))
def columnClock (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) : QuantumTest :=
  ∑i : Fin 2,A (phaseRow m ell i (compressionCore F (coreTime F (inputSeed g i) t)))
def originalTimeDrift (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) : QuantumTest :=
  ∑i : Fin 2,(SourceScalarDoubleCurrent.bracket H0 (A*phaseRow m ell i)
      (coreTime F (inputSeed g i) t)+
    A (phaseRow m ell i (defectAction F (coreTime F (inputSeed g i) t))))
private theorem time_drift_return (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) :
    H0 (columnTime m ell F g t)-columnClock m ell F g t=originalTimeDrift m ell F g t := by
  unfold columnTime columnClock originalTimeDrift
  simp only [map_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold SourceScalarDoubleCurrent.bracket defectAction
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  module

def wholeTimeMiddle (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) : ℂ :=
  let y:=columnTime m ell F g t
  let c:=columnClock m ell F g t
  sourcePair y (H0 y)-(sourcePair c y+sourcePair y c)/2

private theorem time_channels (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) :
    columnTime m ell F g t=
      ∑j : Channel F,phase (channelValue F j) t • columnChannel m ell F g j := by
  unfold columnTime coreTime
  simp only [map_sum,map_smul]
  rw [Finset.sum_comm]
  simp only [columnChannel,Finset.smul_sum,phase]
private theorem clock_channels (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) :
    columnClock m ell F g t=
      ∑j : Channel F,((channelValue F j : ℂ)*phase (channelValue F j) t) •
        columnChannel m ell F g j := by
  unfold columnClock coreTime
  simp_rw [map_sum,map_smul,actual_channel_eigen,map_smul,smul_smul]
  rw [Finset.sum_comm]
  simp only [columnChannel,Finset.smul_sum,phase]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

private theorem pair_two_expansion {ι : Type*} [Fintype ι]
    (d : ι → QuantumTest) (R L : ι → ℂ) (B : End) :
    sourcePair (∑i,R i • d i) (B (∑j,L j • d j))=
      ∑i,∑j,star (R i)*L j*sourcePair (d i) (B (d j)) := by
  simp only [map_sum,map_smul,pair_sum_l,pair_sum_r,pair_smul_l,pair_smul_r,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem time_middle_channels (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) :
    wholeTimeMiddle m ell F g t=
      ∑i : Channel F,∑j : Channel F,
        star (phase (channelValue F i) t)*phase (channelValue F j) t*
          channelTransition m ell F g i j := by
  let d:=columnChannel m ell F g
  let R:=fun i : Channel F=>phase (channelValue F i) t
  let L:=fun i : Channel F=>(channelValue F i : ℂ)*R i
  have hl:=pair_two_expansion d L R (1 : End)
  have hr:=pair_two_expansion d R L (1 : End)
  simp only [Module.End.one_apply] at hl hr
  dsimp only [wholeTimeMiddle]
  rw [time_channels,clock_channels]
  change sourcePair (∑i,R i • d i) (H0 (∑j,R j • d j))-
    (sourcePair (∑i,L i • d i) (∑j,R j • d j)+
      sourcePair (∑i,R i • d i) (∑j,L j • d j))/2=_
  rw [pair_expansion d R H0,hl,hr]
  simp only [←Finset.sum_add_distrib,Finset.sum_div,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [R,L,channelTransition,d]
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

private def causalTime (advanced : Bool) (t : ℝ) : ℝ := if advanced then -t else t
private def causalGap (advanced : Bool) (μ a b : ℝ) : ℂ :=
  if advanced then star (gap μ a b) else gap μ a b
private def abelPhase (advanced : Bool) (μ a b t : ℝ) : ℂ :=
  Complex.exp (-(2*(μ : ℂ))*(t : ℂ))*
    star (phase a (causalTime advanced t))*phase b (causalTime advanced t)

private theorem star_complex_exp (z : ℂ) : star (Complex.exp z)=Complex.exp (star z) := by
  simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.star_exp z
private theorem abel_phase_exp (advanced : Bool) (μ a b t : ℝ) :
    abelPhase advanced μ a b t=Complex.exp ((-causalGap advanced μ a b)*(t : ℂ)) := by
  unfold abelPhase phase
  rw [star_complex_exp,←Complex.exp_add,←Complex.exp_add]
  congr 1
  cases advanced <;> simp [causalTime,causalGap,gap,star_mul,star_neg]
  all_goals ring
private theorem causal_gap_negative (advanced : Bool) (μ a b : ℝ) (hμ : 0<μ) :
    (-causalGap advanced μ a b).re<0 := by
  cases advanced <;> simp [causalGap,gap]
  all_goals linarith
private theorem abel_phase_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0<μ) :
    IntegrableOn (abelPhase advanced μ a b) (Set.Ioi 0) := by
  change IntegrableOn (fun t : ℝ=>abelPhase advanced μ a b t) (Set.Ioi 0)
  simp_rw [abel_phase_exp]
  exact integrableOn_exp_mul_complex_Ioi (causal_gap_negative advanced μ a b hμ) 0
private theorem abel_phase_integral (advanced : Bool) (μ a b : ℝ) (hμ : 0<μ) :
    (∫t : ℝ in Set.Ioi 0,abelPhase advanced μ a b t)=(causalGap advanced μ a b)⁻¹ := by
  simp_rw [abel_phase_exp]
  rw [integral_exp_mul_complex_Ioi (causal_gap_negative advanced μ a b hμ) 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,div_neg,neg_div,neg_neg,one_div]

def sourceAbelMiddle (advanced : Bool) (μ : ℝ) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (t : ℝ) : ℂ :=
  Complex.exp (-(2*(μ : ℂ))*(t : ℂ))*
    wholeTimeMiddle m ell F g (causalTime advanced t)
private theorem actual_abel_channels (advanced : Bool) (μ : ℝ) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (t : ℝ) :
    sourceAbelMiddle advanced μ m ell F g t=
      ∑i : Channel F,∑j : Channel F,
        abelPhase advanced μ (channelValue F i) (channelValue F j) t*
          channelTransition m ell F g i j := by
  rw [sourceAbelMiddle,time_middle_channels]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold abelPhase
  ring

private theorem original_time_middle_real (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) :
    (wholeTimeMiddle m ell F g t).re=
      (sourcePair (columnTime m ell F g t)
        (originalTimeDrift m ell F g t)).re := by
  rw [←time_drift_return]
  have h:sourcePair (columnClock m ell F g t) (columnTime m ell F g t)=
      star (sourcePair (columnTime m ell F g t) (columnClock m ell F g t)) := by
    exact (pair_conjugate _ _).symm
  dsimp only [wholeTimeMiddle]
  rw [h]
  simp only [sourcePair,map_sub,inner_sub_right,Complex.sub_re,Complex.div_ofNat_re,
    Complex.add_re,Complex.star_def,Complex.conj_re]
  ring

/-- The complete frequency middle is the Abel return of its own original CF core trajectories, with full H0 retained. -/
theorem actual_original_middle_abel_return (μ : ℝ) (hμ : 0<μ) (advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    IntegrableOn (sourceAbelMiddle advanced μ m ell F g) (Set.Ioi 0) ∧
    (∫w : ℝ,fullMiddle m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)=
      2*(Real.pi : ℂ)*(∫t : ℝ in Set.Ioi 0,sourceAbelMiddle advanced μ m ell F g t) ∧
    ∀t : ℝ,(sourceAbelMiddle advanced μ m ell F g t).re=
      Real.exp (-2*μ*t)*(sourcePair (columnTime m ell F g (causalTime advanced t))
        (originalTimeDrift m ell F g (causalTime advanced t))).re := by
  have hij (i j : Channel F):IntegrableOn (fun t : ℝ=>
      abelPhase advanced μ (channelValue F i) (channelValue F j) t*
        channelTransition m ell F g i j) (Set.Ioi 0) :=
    (abel_phase_integrable advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _
  have hrow (i : Channel F):IntegrableOn (fun t : ℝ=>∑j : Channel F,
      abelPhase advanced μ (channelValue F i) (channelValue F j) t*
        channelTransition m ell F g i j) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun j _=>hij i j)
  refine ⟨?_,?_,?_⟩
  · change Integrable (fun t : ℝ=>sourceAbelMiddle advanced μ m ell F g t) (volume.restrict (Set.Ioi 0))
    simpa only [actual_abel_channels] using integrable_finsetSum Finset.univ (fun i _=>hrow i)
  · rw [(actual_zero_column_frequency_moment μ hμ advanced m ell F g).2]
    simp_rw [actual_abel_channels]
    rw [integral_finsetSum _ (fun i _=>hrow i)]
    unfold closedFirstMoment
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _=>hij i j)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const,abel_phase_integral advanced μ _ _ hμ]
    cases advanced <;> simp [causalGap,div_eq_mul_inv,mul_assoc]
  · intro t
    unfold sourceAbelMiddle
    have he:-(2*(μ : ℂ))*(t : ℂ)=((-2*μ*t : ℝ) : ℂ) := by push_cast;ring
    rw [he,←Complex.ofReal_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      original_time_middle_real]

end LowEnergy.SourceClockPhiZeroColumnFirstMoment
