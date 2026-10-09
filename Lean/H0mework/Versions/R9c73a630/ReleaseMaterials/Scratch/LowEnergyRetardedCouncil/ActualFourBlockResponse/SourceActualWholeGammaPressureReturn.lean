import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSecondPressureMagneticPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCompensatedWardOperatorReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSecondPressurePositiveStorage
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarForceSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualWholeGammaPressureReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceNativeCutoffContact SourceRetardedGraph
open ActualMixedCovarianceTail ActualMixedWindowGram ActualScalarPhaseFrequencyReturn
open ActualScalarPhaseQuadraticMoment ActualShiftedQuadraticWardPayment ActualSecondPressureMagneticPayment
open ActualVectorJointCost ActualPhaseBulkSquare SourceClockPhiSecondBulk ActualSecondPressurePositiveStorage
open GaussNativeEnergy SourceCoframeVolume SourcePhysicalKineticSquare SourceCoframeVolumeCurrent SourceScalarInverseNativeEnergy
open SourceScalarNativeComparison SourceClockPhiRadiusSourceCurrent ScalarInputJointNoether
open FirstCurrentScalarForceAbsorption Lean Meta Elab Term
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair compressionCore resolventCore coreWindow thetaAction deltaGauge
  SourceGaugeScaleTransport.generator phaseHamiltonianSquare sourceTime

/-- The true compressed Gauge forcing, including every raw-P derivative. -/
def gaugeRetardedCore(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  resolventCore F z hz*deltaGauge (compressionCore F)*resolventCore F z hz

/-- The fixed-input return remains complex and ordered until its L1 price. -/
def fixedGaugeContact(S:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  sourcePair (thetaAction m ell (gaugeRetardedCore F z hz f))
    (coreWindow m ell F z hz (S h))+
  sourcePair (coreWindow m ell F z hz f)
    (thetaAction m ell (gaugeRetardedCore F z hz (S h)))

/-- The two moving pressure orders keep the actual theta/S positions. -/
def pressureGaugeCross(S:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  (0:ℂ)-sourcePair (thetaAction m ell (gaugeRetardedCore F z hz f))
    (thetaAction m ell (S (resolventCore F z hz h)))-
  sourcePair (coreWindow m ell F z hz f)
    (thetaAction m ell (S (gaugeRetardedCore F z hz h)))

private theorem pair_neg_right(f h:QuantumTest):sourcePair f (-h)= -sourcePair f h := by
  simp only [sourcePair,map_neg,inner_neg_right]

private theorem current_reduce(S:End)(F:Index)(z:ℂ)(hz:z.im≠0):
    resolventCore F z hz*(compressionCore F*S-S*compressionCore F)*resolventCore F z hz=
      S*resolventCore F z hz-resolventCore F z hz*S := by
  have h:=(paid_phase_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) S
    ((paid_phase_inverse% actual_inverse) F z hz).1
    ((paid_phase_inverse% actual_inverse) F z hz).2
  rw [(paid_phase_inverse% comm_spectral)] at h
  change S*resolventCore F z hz-resolventCore F z hz*S=
    -resolventCore F z hz*(S*compressionCore F-compressionCore F*S)*resolventCore F z hz at h
  linear_combination (norm := noncomm_ring) -h

/-- All four forcing orders cancel together, before either pressure order
or fixed contact is estimated. The original compressed operator is retained. -/
theorem actual_whole_gamma_pressure_return(S:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    fieldForcing S m ell F z hz f h=
      pressureGaugeCross S m ell F z hz f h+fixedGaugeContact S m ell F z hz f h := by
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let Gamma:=deltaGauge C
  let Z:=R*Gamma*R
  let T:=R*(C*S-S*C)*R
  have hT:T=S*R-R*S:=current_reduce S F z hz
  have hA:-(R*Gamma*T)-T*Gamma*R+R*(Gamma*S-S*Gamma)*R= -S*Z+Z*S := by
    rw [hT]
    dsimp only [Z]
    noncomm_ring
  have hp:=congrArg (fun A:End=>sourcePair (coreWindow m ell F z hz f)
    (thetaAction m ell (A h))) hA
  have ht:=congrArg (fun A:End=>sourcePair (thetaAction m ell (Z f))
    (thetaAction m ell (A h))) hT
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,map_add,map_sub,map_neg,
    (paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_sub_right),
    pair_neg_right] at hp
  simp only [LinearMap.sub_apply,map_sub,(paid_phase_frequency% pair_sub_right)] at ht
  unfold fieldForcing pressureGaugeCross fixedGaugeContact gaugeRetardedCore
  dsimp only
  dsimp only [R,C,Gamma,Z,T] at hp ht
  simp only [coreWindow,Module.End.mul_apply,LinearMap.neg_apply,map_neg,pair_neg_right] at hp ht ⊢
  linear_combination hp-ht

private theorem pair_sub_left(a b h:QuantumTest):sourcePair (a-b) h=sourcePair a h-sourcePair b h := by
  simp only [sourcePair,map_sub,inner_sub_left]

private theorem gauge_window_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    thetaAction m ell (gaugeRetardedCore F z hz f)=
      coreWindow m ell F z hz (Gauge f)-Gauge (coreWindow m ell F z hz f) := by
  have h:=LinearMap.congr_fun (actual_gauge_window_splice m ell F z hz) f
  simp only [Module.End.mul_apply,LinearMap.sub_apply] at h
  unfold gaugeRetardedCore
  simp only [Module.End.mul_apply]
  linear_combination (norm := module) h

/-- Both apparent moving Gamma contacts return to genuine fixed source
words. The two Gauge-on-RF terms cancel by the actual skew generator. -/
theorem actual_fixed_gauge_source_contact(S:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    fixedGaugeContact S m ell F z hz f h=
      sourcePair (coreWindow m ell F z hz (Gauge f)) (coreWindow m ell F z hz (S h))+
      sourcePair (coreWindow m ell F z hz f) (coreWindow m ell F z hz (Gauge (S h))) := by
  unfold fixedGaugeContact
  rw [gauge_window_return,gauge_window_return,pair_sub_left,
    (paid_phase_frequency% pair_sub_right),(paid_shifted_response% gauge_pair)]
  ring

private theorem causal_nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'

private theorem pair_window(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    sourcePair (coreWindow m ell F z hz f) (coreWindow m ell F z hz h)=
      inner ℂ (window m ell F z f) (window m ell F z h) := by
  simp only [coreWindow,Module.End.mul_apply,sourcePair,(paid_mixed_core% window_core)]

/-- One N precedes F and both causes. The whole complex contact is paid in
norm L1 using the original fixed Gauge and field inputs. -/
theorem actual_fixed_gauge_contact_tail(S:End)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal ‖fixedGaugeContact S m ell F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) f h‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N0,h0⟩:=(paid_phase_moment% window_pair_tail) μ hμ (Gauge f) (S h) (ε/2) (by positivity)
  obtain ⟨N1,h1⟩:=(paid_phase_moment% window_pair_tail) μ hμ f (Gauge (S h)) (ε/2) (by positivity)
  refine ⟨max N0 N1,fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (by omega) ell hml,h1 m (by omega) ell hml] with F hF0 hF1
  intro advanced
  let p(a b:QuantumTest)(w:ℝ):ℂ:=inner ℂ (window m ell F (causalFrequency advanced μ w) a)
    (window m ell F (causalFrequency advanced μ w) b)
  have hp(a b:QuantumTest):Measurable (fun w:ℝ=>ENNReal.ofReal ‖p a b w‖) :=
    ENNReal.measurable_ofReal.comp ((((paid_phase_moment% window_continuous) advanced μ hμ m ell F a).inner
      (𝕜:=ℂ) ((paid_phase_moment% window_continuous) advanced μ hμ m ell F b)).norm.measurable)
  simp_rw [actual_fixed_gauge_source_contact,pair_window]
  have hi:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (norm_add_le (p (Gauge f) (S h) w) (p f (Gauge (S h)) w)))
  apply hi.trans
  simp_rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  rw [lintegral_add_right _ (hp _ _)]
  have hb:=add_le_add (hF0 advanced) (hF1 advanced)
  apply hb.trans_eq
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- Direct payment of the original four-forcing remainder, rather than a
renamed flux-tail premise. Only the two moving pressure orders remain. -/
theorem actual_whole_gamma_fixed_return_tail(S:End)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      let v:=fun w:ℝ=>fieldForcing S m ell F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) f h-pressureGaugeCross S m ell F
        (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) f h
      Integrable v ∧ (∫⁻w:ℝ,ENNReal.ofReal ‖v w‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_fixed_gauge_contact_tail S μ hμ f h ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  dsimp only
  simp_rw [actual_whole_gamma_pressure_return,add_sub_cancel_left]
  refine ⟨⟨?_,?_⟩,hF advanced⟩
  · have hc(a b:QuantumTest):Continuous (fun w:ℝ=>inner ℂ
        (window m ell F (causalFrequency advanced μ w) a)
        (window m ell F (causalFrequency advanced μ w) b)) :=
      ((paid_phase_moment% window_continuous) advanced μ hμ m ell F a).inner (𝕜:=ℂ)
        ((paid_phase_moment% window_continuous) advanced μ hμ m ell F b)
    have he:(fun w:ℝ=>fixedGaugeContact S m ell F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) f h)=fun w:ℝ=>
        inner ℂ (window m ell F (causalFrequency advanced μ w) (Gauge f))
          (window m ell F (causalFrequency advanced μ w) (S h))+
        inner ℂ (window m ell F (causalFrequency advanced μ w) f)
          (window m ell F (causalFrequency advanced μ w) (Gauge (S h))) := by
      funext w
      rw [actual_fixed_gauge_source_contact,pair_window,pair_window]
    rw [he]
    exact ((hc _ _).add (hc _ _)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm]
    exact lt_of_le_of_lt (hF advanced) ENNReal.ofReal_lt_top


private theorem theta_pair(m ell:ℕ)(f h:QuantumTest):
    sourcePair f (thetaAction m ell h)=sourcePair (thetaAction m ell f) h := by
  unfold thetaAction
  exact GaussNativeForm.multiply_pair _ _ _ _
private theorem pair_real_symm(f h:QuantumTest):(sourcePair f h).re=(sourcePair h f).re := by
  unfold sourcePair
  exact inner_re_symm (𝕜:=ℂ) (embed f) (embed h)

/-- Actual source symmetry gives a Jordan insertion, preserving both theta
orders. Source symmetry alone does not remove its radial cross. -/
theorem actual_source_pressure_jordan_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    (pressureGaugeCross (secondJet phaseHamiltonianSquare) m ell F z hz g g).re=
      -(sourcePair (gaugeRetardedCore F z hz g)
        (((thetaAction m ell*thetaAction m ell*secondJet phaseHamiltonianSquare+
          secondJet phaseHamiltonianSquare*thetaAction m ell*thetaAction m ell))
          (resolventCore F z hz g))).re := by
  let q:=resolventCore F z hz g
  let Z:=gaugeRetardedCore F z hz g
  let T:=thetaAction m ell
  let S:=secondJet phaseHamiltonianSquare
  have ha:sourcePair (T Z) (T (S q))=sourcePair Z (T (T (S q))):=
    (theta_pair m ell Z (T (S q))).symm
  have hb:(sourcePair (T q) (T (S Z))).re=(sourcePair Z (S (T (T q)))).re := by
    rw [theta_pair m ell (T q) (S Z)]
    rw [actual_second_source_pair (T (T q)) Z]
    exact pair_real_symm _ _
  unfold pressureGaugeCross
  simp only [coreWindow,Module.End.mul_apply]
  change (0-sourcePair (T Z) (T (S q))-sourcePair (T q) (T (S Z))).re=
    -(sourcePair Z ((T*T*S+S*T*T) q)).re
  simp only [LinearMap.add_apply,Module.End.mul_apply,
    (paid_phase_frequency% pair_add_right),Complex.add_re,Complex.sub_re,zero_sub]
  rw [ha,hb]
  simp only [Complex.neg_re]
  ring

/-- The exact mixed IMS cross is retained with the two moving source legs. -/
theorem actual_source_pressure_double_commutator_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let T:=thetaAction m ell
    let S:=secondJet phaseHamiltonianSquare
    let q:=resolventCore F z hz g
    let Z:=gaugeRetardedCore F z hz g
    (pressureGaugeCross S m ell F z hz g g).re=
      -2*(sourcePair (T Z) (S (T q))).re-
      (sourcePair Z ((T*(T*S-S*T)-(T*S-S*T)*T) q)).re := by
  dsimp only
  rw [actual_source_pressure_jordan_return]
  let T:=thetaAction m ell
  let S:=secondJet phaseHamiltonianSquare
  have ha:T*T*S+S*T*T=(2:ℂ) • (T*S*T)+(T*(T*S-S*T)-(T*S-S*T)*T) := by
    simp only [two_smul]
    noncomm_ring
  rw [ha]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,
    (paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_smul_right),Complex.add_re,
    Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [theta_pair]
  ring

elab "paid_radius_input%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarForceSource 0) "LowEnergy") "FirstCurrentScalarForceAbsorption"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

/-- The completed square's actual input returns to the seventy native rows;
the source volume and inverse-volume cancel before any estimate. -/
theorem actual_reader_native_inventory(k:QuantumTest):
    inverseNativeEnergy (volumeAction k)=nativeScalarEnergy k := by
  rw [←original_inverse_native_return,(paid_radius_input% inverse_volume)]

/-- The original affine Hardy source and vacuum give a strict input gain.
There is no radius-after-R operator estimate or supplied reader budget. -/
theorem actual_inverse_radius_reader_price(k:QuantumTest):
    (7*sourceTime 0/96)*‖embed (phiInverseAction k)‖^2 ≤
      (sourceTime 0/256)*nativeScalarEnergy k := by
  have h:=actual_affine_inverse_native_hardy (volumeAction k)
  rw [(paid_radius_input% inverse_volume)] at h
  have hn:0<sourceTime 0:=(paid_radius_input% n_pos)
  have he:0 ≤ inverseNativeEnergy (volumeAction k):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hc:(7/96:ℝ)*(16*affineHardyCost/59^2) ≤ (1/256:ℝ) := by
    have hcost:=actual_affine_hardy_source_cost
    norm_num at hcost ⊢
    nlinarith only [hcost]
  have hcoef:(7*sourceTime 0/96)*(16*affineHardyCost/59^2) ≤ sourceTime 0/256 := by
    calc
      _ = sourceTime 0*((7/96:ℝ)*(16*affineHardyCost/59^2)):=by ring
      _ ≤ sourceTime 0*(1/256):=mul_le_mul_of_nonneg_left hc hn.le
      _=_:=by ring
  have hh:=mul_le_mul_of_nonneg_left h (show 0 ≤ 7*sourceTime 0/96 by positivity)
  rw [←mul_assoc] at hh
  have hb:=hh.trans (mul_le_mul_of_nonneg_right hcoef he)
  rw [actual_reader_native_inventory] at hb
  exact hb

end LowEnergy.ActualWholeGammaPressureReturn
