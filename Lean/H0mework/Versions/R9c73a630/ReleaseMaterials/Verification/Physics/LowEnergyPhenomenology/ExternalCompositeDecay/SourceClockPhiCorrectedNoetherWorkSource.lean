import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianMeanSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedPhysicalWorkAbel
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedHamiltonianWorkGenerator
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiMatchedDiffusionSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiCorrectedNoetherWorkSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceLocalizedInverseFormPayment SourceResolventBandLimit FullYSourceResolventGraphSplice
open SourceClockPhiNormalizedScalarBudget ClockPhiHeatCorrectedCovarianceSource
open ClockPhiCorrectedGaussianMeanSource ClockPhiCorrectedHamiltonianWorkGenerator
open MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev T (m ell:ℕ):End:=phiThetaAction m ell
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ2:=γ.prod γ
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore

private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

private theorem theta_commute (m ell:ℕ) : Commute S (T m ell) :=by
  let Q:End:=(1:End)-S
  have hQ(f:QuantumTest):S (Q f)=Q (S f):=by
    change S (f-S f)=S f-S (S f)
    rw [map_sub]
  have hp(k:ℕ)(f:QuantumTest):S ((Q^k) f)=(Q^k) (S f):=by
    induction k with
    | zero => simp only [pow_zero,Module.End.one_apply]
    | succ k ih =>
      rw [pow_succ']
      change S (Q ((Q^k) f))=Q ((Q^k) (S f))
      rw [hQ,ih]
  change S*(Q^(m+1)-Q^(ell+1))=(Q^(m+1)-Q^(ell+1))*S
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub,hp]

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
    apply LinearMap.ext
    intro f
    have hc:=LinearMap.congr_fun (theta_commute m ell).eq (r f)
    have hr:=LinearMap.congr_fun inverse_radius f
    simp only [Module.End.mul_apply,Module.End.one_apply] at hc hr ⊢
    rw [hc,hr]

  have ht:=LinearMap.congr_fun htr (coreEquiv.symm g)
  unfold normalizedForcing normalizedState bracket
  change diagonalAction (T m ell q-(S*T m ell) h)=
    ((diagonalAction*(T m ell)-(T m ell)*diagonalAction) q-
      (diagonalAction*(S*T m ell)-(S*T m ell)*diagonalAction) h+
      T m ell (defectAction F q)-(S*T m ell) (defectAction F h))+z • (T m ell q-(S*T m ell) h)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hq,hh,map_add,map_smul] at ht ⊢
  linear_combination (norm:=module) -ht

def shiftedAction(freqShift:ℝ):End:=diagonalAction-(freqShift:ℂ) • (1:End)
def actualFluctuation(τ:ℝ)(hτ:0<τ)(x:ℝ×ℝ)(f:QuantumTest):QuantumTest:=
  correctedCompleteCore τ hτ x.1 x.2 f-f
def actualMeanIncrement(τ:ℝ)(hτ:0<τ)(f:QuantumTest):H:=
  (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2 f) ∂γ2)-embed f
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem integral_sub_pair {ι:Type*}[MeasurableSpace ι](μ:Measure ι){F G:ι→ℂ}
    (hF:Integrable F μ)(hG:Integrable G μ):
    (∫x,F x-G x ∂μ)=(∫x,F x ∂μ)-(∫x,G x ∂μ):=by
  convert! integral_sub hF hG using 1
private theorem shifted_pair(freqShift:ℝ)(f g:QuantumTest):
    sourcePair f (shiftedAction freqShift g)=sourcePair (shiftedAction freqShift f) g:=by
  simp only [shiftedAction,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    sourcePair,map_sub,map_smul,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  exact congrArg (fun x:ℂ=>x-(freqShift:ℂ)*sourcePair f g) (diagonalAction_pair f g)
private theorem fluctuation_split(freqShift:ℝ)(u w:QuantumTest):
    sourcePair u (shiftedAction freqShift u)-sourcePair w (shiftedAction freqShift w)=
      sourcePair (u-w) (shiftedAction freqShift (u-w))+
        sourcePair (u-w) (shiftedAction freqShift w)+sourcePair (shiftedAction freqShift w) (u-w):=by
  simp only [map_sub,pair_sub_l,pair_sub_r]
  rw [shifted_pair freqShift w u,shifted_pair freqShift w w]
  ring
private theorem complete_pair(τ:ℝ)(hτ:0<τ)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore τ hτ x.1 x.2 f) (correctedCompleteCore τ hτ x.1 x.2 g)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) g):=by
  change sourcePair
    (SourceClockPhiCoframeForwardCore.sourceForwardCore τ hτ.le
      (correctedProfileCore τ hτ x.1 x.2 (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)))
    (SourceClockPhiCoframeForwardCore.sourceForwardCore τ hτ.le
      (correctedProfileCore τ hτ x.1 x.2 (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) g)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact ClockPhiConservativeHeatSource.clockProfileAction_pair _ _ _ _ _ _
private theorem shifted_mean_integrable(τ:ℝ)(hτ:0<τ)(freqShift:ℝ)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore τ hτ x.1 x.2 f)
      (shiftedAction freqShift (correctedCompleteCore τ hτ x.1 x.2 f))) γ2:=by
  have hH:=(ClockPhiHeatCorrectedHamiltonianSource.actual_corrected_hamiltonian_gaussian τ hτ f f).1
  have hm:Integrable (fun _:ℝ×ℝ=>(freqShift:ℂ)*sourcePair
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)) γ2:=integrable_const _
  have he(x:ℝ×ℝ):sourcePair (correctedCompleteCore τ hτ x.1 x.2 f)
      (shiftedAction freqShift (correctedCompleteCore τ hτ x.1 x.2 f))=
      sourcePair (correctedCompleteCore τ hτ x.1 x.2 f)
        (diagonalAction (correctedCompleteCore τ hτ x.1 x.2 f))-
        (freqShift:ℂ)*sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)
          (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f):=by
    simp only [shiftedAction,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      pair_sub_r,pair_smul_r,complete_pair]
  simpa only [he,Pi.sub_apply] using! hH.sub hm

private theorem finite_mean_split(τ:ℝ)(hτ:0<τ)(freqShift:ℝ)(w:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (actualFluctuation τ hτ x w)
      (shiftedAction freqShift (actualFluctuation τ hτ x w))) γ2 ∧
    ((∫x:ℝ×ℝ,sourcePair (correctedCompleteCore τ hτ x.1 x.2 w)
      (shiftedAction freqShift (correctedCompleteCore τ hτ x.1 x.2 w)) ∂γ2)-sourcePair w (shiftedAction freqShift w))=
      (∫x:ℝ×ℝ,sourcePair (actualFluctuation τ hτ x w)
        (shiftedAction freqShift (actualFluctuation τ hτ x w)) ∂γ2)+
        inner ℂ (actualMeanIncrement τ hτ w) (embed (shiftedAction freqShift w))+
        inner ℂ (embed (shiftedAction freqShift w)) (actualMeanIncrement τ hτ w):=by
  have hK:=(actual_corrected_complete_mean_source τ hτ w).1
  have hD:Integrable (fun x:ℝ×ℝ=>embed (actualFluctuation τ hτ x w)) γ2:=by
    simpa only [actualFluctuation,map_sub,Pi.sub_apply] using! hK.sub (integrable_const (embed w))
  have hL:=hD.inner_const (𝕜:=ℂ) (embed (shiftedAction freqShift w))
  have hR:=hD.const_inner (𝕜:=ℂ) (embed (shiftedAction freqShift w))
  have hM:=shifted_mean_integrable τ hτ freqShift w
  have he(x:ℝ×ℝ):sourcePair (actualFluctuation τ hτ x w) (shiftedAction freqShift (actualFluctuation τ hτ x w))=
      sourcePair (correctedCompleteCore τ hτ x.1 x.2 w) (shiftedAction freqShift (correctedCompleteCore τ hτ x.1 x.2 w))-
        sourcePair w (shiftedAction freqShift w)-
        inner ℂ (embed (actualFluctuation τ hτ x w)) (embed (shiftedAction freqShift w))-
        inner ℂ (embed (shiftedAction freqShift w)) (embed (actualFluctuation τ hτ x w)):=by
    have h:=fluctuation_split freqShift (correctedCompleteCore τ hτ x.1 x.2 w) w
    dsimp only [actualFluctuation,sourcePair] at h ⊢
    linear_combination -h
  have hF:Integrable (fun x:ℝ×ℝ=>sourcePair (actualFluctuation τ hτ x w)
      (shiftedAction freqShift (actualFluctuation τ hτ x w))) γ2:=by
    simpa only [he,Pi.sub_apply] using! ((hM.sub (integrable_const _)).sub hL).sub hR
  have hDI:(∫x:ℝ×ℝ,embed (actualFluctuation τ hτ x w) ∂γ2)=actualMeanIncrement τ hτ w:=by
    simp only [actualFluctuation,map_sub]
    rw [integral_sub hK (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul,actualMeanIncrement]
  have hRI:(∫x:ℝ×ℝ,inner ℂ (embed (shiftedAction freqShift w)) (embed (actualFluctuation τ hτ x w)) ∂γ2)=
      inner ℂ (embed (shiftedAction freqShift w)) (actualMeanIncrement τ hτ w):=by
    rw [integral_inner (𝕜:=ℂ) hD,hDI]
  have hLI:(∫x:ℝ×ℝ,inner ℂ (embed (actualFluctuation τ hτ x w)) (embed (shiftedAction freqShift w)) ∂γ2)=
      inner ℂ (actualMeanIncrement τ hτ w) (embed (shiftedAction freqShift w)):=by
    calc
      _=∫x:ℝ×ℝ,star (inner ℂ (embed (shiftedAction freqShift w)) (embed (actualFluctuation τ hτ x w))) ∂γ2:=by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x=>(inner_conj_symm _ _).symm)
      _=star (∫x:ℝ×ℝ,inner ℂ (embed (shiftedAction freqShift w)) (embed (actualFluctuation τ hτ x w)) ∂γ2):=integral_conj
      _=_:=by rw [hRI];exact inner_conj_symm _ _
  refine ⟨hF,?_⟩
  have hI:=integral_congr_ae (μ:=γ2) (Eventually.of_forall he)
  have h0:Integrable (fun _:ℝ×ℝ=>sourcePair w (shiftedAction freqShift w)) γ2:=integrable_const _
  have hi1:=integral_sub_pair γ2 ((hM.sub h0).sub hL) hR
  have hi2:=integral_sub_pair γ2 (hM.sub h0) hL
  have hi3:=integral_sub_pair γ2 hM h0
  dsimp only [Pi.sub_apply] at hi1 hi2 hi3
  rw [hi1,hi2,hi3,hLI,hRI] at hI
  simp only [integral_const,probReal_univ,one_smul] at hI
  linear_combination -hI

theorem actual_corrected_noether_frequency_work(τ:ℝ)(hτ:0<τ)(m ell:ℕ)(F:Index)
    (z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    let w:=normalizedState m ell F z hz g
    Integrable (fun x:ℝ×ℝ=>sourcePair (actualFluctuation τ hτ x w)
      (shiftedAction z.re (actualFluctuation τ hτ x w))) γ2 ∧
    ((∫x:ℝ×ℝ,ClockPhiCorrectedPhysicalWorkAbel.correctedFrequencyMiddle τ hτ x.1 x.2 m ell F z hz g ∂γ2)-
      sourcePair w (shiftedAction z.re w)).re=
      (∫x:ℝ×ℝ,sourcePair (actualFluctuation τ hτ x w)
        (shiftedAction z.re (actualFluctuation τ hτ x w)) ∂γ2).re+
        2*(inner ℂ (actualMeanIncrement τ hτ w) (embed (normalizedForcing m ell F z hz g))).re-
        2*z.im*(inner ℂ (actualMeanIncrement τ hτ w) (embed w)).im:=by
  dsimp only
  let w:=normalizedState m ell F z hz g
  have h:=finite_mean_split τ hτ z.re w
  refine ⟨h.1,?_⟩
  have hs:shiftedAction z.re w=normalizedForcing m ell F z hz g+((z.im:ℂ)*Complex.I) • w:=by
    have hZ:z-(z.re:ℂ)=(z.im:ℂ)*Complex.I:=by apply Complex.ext <;> simp
    change diagonalAction w-(z.re:ℂ) • w=_
    rw [full_source,←hZ]
    module
  have hr:(inner ℂ (embed (shiftedAction z.re w)) (actualMeanIncrement τ hτ w)).re=
      (inner ℂ (actualMeanIncrement τ hτ w) (embed (shiftedAction z.re w))).re:=by
    rw [←inner_conj_symm]
    simp only [Complex.conj_re]
  change ((∫x:ℝ×ℝ,sourcePair (correctedCompleteCore τ hτ x.1 x.2 w)
    (shiftedAction z.re (correctedCompleteCore τ hτ x.1 x.2 w)) ∂γ2)-sourcePair w (shiftedAction z.re w)).re=_
  rw [h.2,Complex.add_re,Complex.add_re,hr,hs]
  simp only [map_add,map_smul,inner_add_right,inner_smul_right,Complex.add_re,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,add_zero,mul_one,sub_zero]
  ring


private theorem shifted_pair_return(freqShift:ℝ)(f:QuantumTest):
    sourcePair f (shiftedAction freqShift f)=sourcePair f (diagonalAction f)-(freqShift:ℂ)*sourcePair f f:=by
  simp only [shiftedAction,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,pair_sub_r,pair_smul_r]
private theorem shifted_mean_return(τ:ℝ)(hτ:0<τ)(freqShift:ℝ)(f:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore τ hτ x.1 x.2 f)
      (shiftedAction freqShift (correctedCompleteCore τ hτ x.1 x.2 f)) ∂γ2)=
      correctedHamiltonianPair τ hτ f f-(freqShift:ℂ)*sourcePair
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f):=by
  have hH:=(ClockPhiHeatCorrectedHamiltonianSource.actual_corrected_hamiltonian_gaussian τ hτ f f).1
  simp_rw [shifted_pair_return,complete_pair]
  rw [integral_sub_pair γ2 hH (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul,correctedHamiltonianPair]

theorem actual_corrected_noether_hamiltonian_work(τ:ℝ)(hτ:0<τ)(m ell:ℕ)(F:Index)
    (z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    let w:=normalizedState m ell F z hz g
    (correctedHamiltonianWork τ hτ w w).re=
      (∫x:ℝ×ℝ,sourcePair (actualFluctuation τ hτ x w)
        (shiftedAction z.re (actualFluctuation τ hτ x w)) ∂γ2).re+
        2*(inner ℂ (actualMeanIncrement τ hτ w) (embed (normalizedForcing m ell F z hz g))).re-
        2*z.im*(inner ℂ (actualMeanIncrement τ hτ w) (embed w)).im+
        z.re*(‖embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) w)‖^2-‖embed w‖^2):=by
  dsimp only
  let w:=normalizedState m ell F z hz g
  have h:=(actual_corrected_noether_frequency_work τ hτ m ell F z hz g).2
  change ((∫x:ℝ×ℝ,sourcePair (correctedCompleteCore τ hτ x.1 x.2 w)
    (shiftedAction z.re (correctedCompleteCore τ hτ x.1 x.2 w)) ∂γ2)-sourcePair w (shiftedAction z.re w)).re=_ at h
  rw [shifted_mean_return,shifted_pair_return] at h
  have hself(q:QuantumTest):(sourcePair q q).re=‖embed q‖^2:=inner_self_eq_norm_sq (𝕜:=ℂ) (embed q)
  change (correctedHamiltonianPair τ hτ w w-sourcePair w (diagonalAction w)).re=_
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hself] at h ⊢
  linear_combination h

open ClockPhiMatchedGainFrequencyPayment
private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ℝ):
    (actualFrequency advanced μ freq).im≠0:=by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'
private abbrev A:=SourceClockPhiCombinedScalePressure.combinedConjugate

theorem actual_corrected_noether_physical_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,∀τ:ℝ,∀hτ:0<τ,τ≤1→
      (∫⁻freq:ℝ,ENNReal.ofReal (τ*‖inner ℂ
        (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2
          (normalizedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)) ∂γ2)
        (embed ((A*A)
          (diagonalAction (normalizedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)-
            normalizedForcing m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)))‖-
        η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy
          (normalizedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)))≤ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_corrected_complete_mean_physical_common_payment μ hμ g η hη ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced τ hτ hτ1
  have he(freq:ℝ):
      diagonalAction (normalizedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)-
        normalizedForcing m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g=
      shiftedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g:=by
    rw [full_source,add_sub_cancel_left]
    exact (hS m ell _ (frequency_nonreal advanced μ hμ freq)).1
  simpa only [he] using hF advanced τ hτ hτ1

end LowEnergy.ClockPhiCorrectedNoetherWorkSource
