import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiZeroColumnFirstMoment
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceCoreFormParseval
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiMatchedDiffusionSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiWholeSignedWorkIntegrable
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiCombinedScalePressure SourceClockPhiRadiusNormalizedFluxBudget
open SourceClockPhiNativeMatchedSource SourceClockReflectedForm
open SourceClockYukawaQ8RadiusBudget SourceClockYukawaRadialGammaNativeBudget
open SourceScalarPairedTransport SourceScalarVirialBulk SourceScalarGaugeScale
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceHamiltonianVolume
open SourceScalarDoubleCurrent SourceScalarInverseNativeEnergy SourceClockSourceTail SourceScalarPositiveBulkWard FullYSourceResolventGraphSplice
open SourcePhysicalKineticSquare SourceLocalizedInverseFormPayment SourceMixedNativeReturn SourceFourPoleEnergyClosed SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
private abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev T (m ell:ℕ):End:=phiThetaAction m ell
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore sourcePair embed sourceRead finiteResolvent
open SourceInverseNoetherChannelGap SourceClockPhiNativeJointPayment SourceCoreFormParseval SourceJointResidualEnergy
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

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

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

private def stateColumn (m ell : ℕ) (F : Index) (g : diagonal.domain) (j : Channel F) : QuantumTest :=
  ∑i : Fin 2,phaseRow m ell i (channelTest F (inputSeed g i) j)
private theorem original_state_seed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    state F z hz g=resolventCore F z hz (coreEquiv.symm g) := by
  simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
private theorem actual_state_column (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    normalizedState m ell F z hz g=
      ∑j : Channel F,((channelValue F j : ℂ)-z)⁻¹ • stateColumn m ell F g j := by
  have hs:normalizedState m ell F z hz g=
      ∑i : Fin 2,phaseRow m ell i (state F z hz (inputSeed g i)) := by
    simp only [Fin.sum_univ_two]
    change normalizedState m ell F z hz g=
      T m ell (state F z hz g)+(-(S*T m ell) (state F z hz (phiRadiusSource g)))
    rw [original_state_seed F z hz g,original_state_seed F z hz (phiRadiusSource g)]
    unfold phiRadiusSource
    rw [coreEquiv.symm_apply_apply]
    simp only [normalizedState,Module.End.mul_apply]
    change T m ell (resolventCore F z hz (coreEquiv.symm g))-
      S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))=
      T m ell (resolventCore F z hz (coreEquiv.symm g))+
      -S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))
    exact sub_eq_add_neg _ _
  rw [hs]
  simp_rw [actual_state_channels,map_sum,map_smul]
  rw [Finset.sum_comm]
  simp only [stateColumn,Finset.smul_sum]

private theorem two_pair_expansion {ι : Type*} [Fintype ι] (d : ι→QuantumTest)
    (c : ι→ℂ) (L R : End) :
    sourcePair (L (∑i,c i • d i)) (R (∑j,c j • d j))=
      ∑i,∑j,star (c i)*c j*sourcePair (L (d i)) (R (d j)) := by
  simp only [map_sum,map_smul,pair_sum_l,pair_sum_r,pair_smul_l,pair_smul_r,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_normalized_pair_integrable (μ : ℝ) (hμ:0<μ) (advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) (L R : End) :
    Integrable (fun q : ℝ=>sourcePair
      (L (normalizedState m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g))
      (R (normalizedState m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g))) := by
  have h:Integrable (fun q : ℝ=>(∑i : Channel F,∑j : Channel F,
      causalPolePair advanced μ (channelValue F i) (channelValue F j) q*
        sourcePair (L (stateColumn m ell F g i)) (R (stateColumn m ell F g j)))) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (causal_pair_integrable advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _
  apply h.congr
  apply Eventually.of_forall
  intro q
  dsimp only
  rw [actual_state_column,two_pair_expansion]
  rfl

private theorem normalized_norm_integrable (μ : ℝ) (hμ:0<μ) (advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) (L : End) :
    Integrable (fun q : ℝ=>‖embed (L (normalizedState m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g))‖^2) := by
  have h:=(actual_normalized_pair_integrable μ hμ advanced m ell F g L L).re
  have he(f : QuantumTest):(sourcePair f f).re=‖embed f‖^2 := by
    simpa only [sourcePair] using! (norm_sq_eq_re_inner (𝕜:=ℂ) (embed f)).symm
  convert! h using 1
  funext q
  exact (he _).symm

private theorem field_integrable (μ : ℝ) (hμ:0<μ) (advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    Integrable (fun q : ℝ=>SourceClockPhiMatchedDiffusionSource.matchedField
      (normalizedState m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g)) := by
  let w:=fun q : ℝ=>normalizedState m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g
  have hP(L R : End):Integrable (fun q : ℝ=>sourcePair (L (w q)) (R (w q))) :=
    actual_normalized_pair_integrable μ hμ advanced m ell F g L R
  have hN(L : End):Integrable (fun q : ℝ=>‖embed (L (w q))‖^2) :=
    normalized_norm_integrable μ hμ advanced m ell F g L
  have hs:Integrable (fun q : ℝ=>spinForm (inverseVolumeAction (w q))) := by
    unfold spinForm
    apply integrable_finsetSum
    intro a _
    exact (hN (GaussCoframeSpin.current a*inverseVolumeAction)).const_mul _
  have hn:Integrable (fun q : ℝ=>densityForm (inverseVolumeAction (w q))) := by
    unfold densityForm numberForm
    exact (((hN (GaussCoframeForm.number*inverseVolumeAction)).const_mul _).add
      ((hP inverseVolumeAction (GaussCoframeForm.number*inverseVolumeAction)).re.const_mul _)).add
      ((hN inverseVolumeAction).const_mul _)
  have hg:Integrable (fun q : ℝ=>gaugeForm (inverseVolumeAction (w q))) := by
    unfold gaugeForm
    apply Integrable.const_mul
    apply Integrable.re (𝕜:=ℂ)
    apply integrable_finsetSum
    intro a _
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    simp only [←Module.End.mul_apply]
    exact hP _ _
  have hspace:Integrable (fun q : ℝ=>spatialForm (inverseVolumeAction (w q))) := by
    unfold spatialForm
    apply Integrable.re (𝕜:=ℂ)
    simp only [←Module.End.mul_apply]
    exact hP _ _
  unfold SourceClockPhiMatchedDiffusionSource.matchedField
  exact (((((hP 1 _).re.add (hs.const_mul _)).add (hn.const_mul _)).sub
    (hg.const_mul _)).sub (hspace.const_mul _))

def comparisonEnergy (w : QuantumTest) : ℝ :=
  ‖embed (SourceClockPhiMatchedDiffusionSource.driftClock w)‖^2+
    (1/2 : ℝ)*‖embed (inverseVolumeAction (combinedGenerator w))‖^2

def wholeSignedWork (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) : ℝ :=
  matchedForcingWord m ell F z hz g-(sourceTime 0/48)*comparisonEnergy (normalizedState m ell F z hz g)

/-- The original two-source complete signed work has genuine frequency integrability before its common upper price is estimated. -/
theorem actual_whole_signed_work_integrable (μ : ℝ) (hμ:0<μ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀m ell : ℕ,∀advanced : Bool,
      Integrable (fun q : ℝ=>wholeSignedWork m ell F (actualFrequency advanced μ q)
        (frequency_nonreal advanced μ hμ q) g) := by
  filter_upwards [SourceClockPhiMatchedDiffusionSource.actual_matched_diffusion_source g] with F hF
  intro m ell advanced
  let w:=fun q : ℝ=>normalizedState m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g
  have hP(L R : End):Integrable (fun q : ℝ=>sourcePair (L (w q)) (R (w q))) :=
    actual_normalized_pair_integrable μ hμ advanced m ell F g L R
  have hJ:Integrable (fun q : ℝ=>SourceClockPhiMatchedDiffusionSource.diffusionSourcePrice m ell F
      (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g) :=
    (hP 1 (SourceClockPhiMatchedDiffusionSource.completeCurrent diagonalAction)).re.add
      (field_integrable μ hμ advanced m ell F g)
  have hE:Integrable (fun q : ℝ=>comparisonEnergy (w q)) :=
    (normalized_norm_integrable μ hμ advanced m ell F g SourceClockPhiMatchedDiffusionSource.driftClock).add
      ((normalized_norm_integrable μ hμ advanced m ell F g (inverseVolumeAction*combinedGenerator)).const_mul _)
  have hσ(q : ℝ):(actualFrequency advanced μ q).im=(if advanced then -μ else μ) := by
    cases advanced <;> simp [actualFrequency,line]
  have hphase:Integrable (fun q : ℝ=>6*(actualFrequency advanced μ q).im*
      (sourcePair (matchedColumn (w q)) (w q)).im) := by
    simp_rw [hσ]
    exact ((hP matchedColumn 1).im).const_mul _
  have h:= (hJ.sub hphase).sub (hE.const_mul (sourceTime 0/48))
  apply h.congr
  apply Eventually.of_forall
  intro q
  dsimp only [wholeSignedWork]
  have hJ0:=(hF m ell (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q)).1
  have hr:=(actual_native_matched_source m ell F (actualFrequency advanced μ q)
    (frequency_nonreal advanced μ hμ q) g).2.1
  dsimp only [w,Pi.sub_apply] at ⊢
  linarith only [hJ0,hr]

end LowEnergy.SourceClockPhiWholeSignedWorkIntegrable
