import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiJointScaleNoether
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiCombinedScaleGammaBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiJointScaleGammaBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget
open SourceClockPhiJointScaleNoether SourceClockPhiCombinedScaleGammaBudget
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockYukawaQ8RadiusBudget SourceClockYukawaRadialGammaNativeBudget
open SourceClockReflectedForm SourceMixedNativeReturn SourceScalarPositiveBulkWard
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceLocalizedInverseFormPayment SourceFourPoleEnergyClosed
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev S:End:=phiInverseAction
private abbrev T (m ell:ℕ):End:=phiThetaAction m ell
private abbrev r:End:=phiRadiusAction
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction compressionCore defectAction resolventCore finiteResolvent sourceRead

private theorem frequency_nonreal(μ:ℝ)(hμ:0<μ)(t:ℝ):(line μ t).im≠0 := by
  simpa only [line_im] using hμ.ne'

/-- The untouched complete same-compression CF, defect, forcing, matter, vacuum and PP word. -/
def wholeJointBudget(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):ENNReal:=
  ∫⁻t:ℝ,ENNReal.ofReal (wholeForcingWord m ell F (line μ t) (frequency_nonreal μ hμ t) g)
private def jointPhase(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  4*z.im*(sourcePair (U (D (normalizedState m ell F z hz g)))
    (normalizedState m ell F z hz g)).im
private def phaseError(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  |jointPhase m ell F z hz g|-(1/2:ℝ)*jointPrice m ell F z hz g
private def phaseErrorBudget(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):ENNReal:=
  ∫⁻t:ℝ,ENNReal.ofReal (phaseError m ell F (line μ t) (frequency_nonreal μ hμ t) g)

private theorem pressure_joint_word(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    combinedPressure (normalizedState m ell F z hz g) ≤
      4*wholeForcingWord m ell F z hz g+4*phaseError m ell F z hz g := by
  have h:=actual_joint_scale_source m ell F z hz g
  have he:=h.1
  have hp:=h.2.2
  change jointPrice m ell F z hz g=wholeForcingWord m ell F z hz g+jointPhase m ell F z hz g at he
  unfold phaseError
  have ha:=le_abs_self (jointPhase m ell F z hz g)
  linarith only [he,hp,ha]

private theorem source_action_read(A:End)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    embed (A (resolventCore F z hz (coreEquiv.symm g)))=
      sourceRead F g A (finiteResolvent F z (g:H)) := by
  simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply,
    SourceScalarPositiveBulkWard.state] using! (source_read_resolvent F g A z hz).symm
private theorem source_action_continuous(A:End)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>embed (A (resolventCore F (line μ t) (frequency_nonreal μ hμ t) (coreEquiv.symm g)))) := by
  simp_rw [source_action_read]
  exact (sourceRead F g A).continuous.comp
    ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const)
private theorem normalized_action_continuous(A:End)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>embed (A (normalizedState m ell F (line μ t) (frequency_nonreal μ hμ t) g))) := by
  have hh:r (coreEquiv.symm g)=coreEquiv.symm (phiRadiusSource g):=
    (coreEquiv.symm_apply_apply _).symm
  unfold normalizedState
  simp only [map_sub,hh]
  exact (source_action_continuous (A*T m ell) F μ hμ g).sub
    (source_action_continuous (A*(S*T m ell)) F μ hμ (phiRadiusSource g))
private theorem response_action_continuous(A:End)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>embed (A (phiResponseCore m ell F (line μ t) (frequency_nonreal μ hμ t) g))) := by
  have hh:r (coreEquiv.symm g)=coreEquiv.symm (phiRadiusSource g):=
    (coreEquiv.symm_apply_apply _).symm
  unfold phiResponseCore bracket
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hh]
  exact (source_action_continuous (A*T m ell*r) F μ hμ g).sub
    (source_action_continuous (A*T m ell) F μ hμ (phiRadiusSource g))
private theorem response_pair_continuous(A B:End)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>sourcePair (A (phiResponseCore m ell F (line μ t) (frequency_nonreal μ hμ t) g))
      (B (phiResponseCore m ell F (line μ t) (frequency_nonreal μ hμ t) g))) := by
  unfold sourcePair
  exact (response_action_continuous A m ell F μ hμ g).inner (𝕜:=ℂ)
    (response_action_continuous B m ell F μ hμ g)
private theorem positive_price_continuous(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>phiPositivePrice m ell F (line μ t) (frequency_nonreal μ hμ t) g) := by
  simp_rw [actual_phi_positive_source,←original_reflected_coframe_gram]
  have hc:Continuous (fun t:ℝ=>reflectedForm (U (phiResponseCore m ell F (line μ t) (frequency_nonreal μ hμ t) g))) := by
    unfold reflectedForm
    apply Complex.continuous_re.comp
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    simp only [←Module.End.mul_apply]
    exact response_pair_continuous _ _ m ell F μ hμ g
  have hs:Continuous (fun t:ℝ=>scalarForm (U (phiResponseCore m ell F (line μ t) (frequency_nonreal μ hμ t) g))) := by
    unfold scalarForm
    apply continuous_finsetSum
    intro i _
    exact (response_action_continuous (GaussCoreDifferential.covariantMomentum (scalarDirection i)*U)
      m ell F μ hμ g).norm.pow 2
  have hr:Continuous (fun t:ℝ=>radiusForm (phiResponseCore m ell F (line μ t) (frequency_nonreal μ hμ t) g)) := by
    unfold radiusForm
    exact Complex.continuous_re.comp (response_pair_continuous 1 _ m ell F μ hμ g)
  exact ((continuous_const.mul hc).add (continuous_const.mul hs)).add (continuous_const.mul hr)
private theorem normalized_pair_continuous(A B:End)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Continuous (fun t:ℝ=>sourcePair (A (normalizedState m ell F (line μ t) (frequency_nonreal μ hμ t) g))
      (B (normalizedState m ell F (line μ t) (frequency_nonreal μ hμ t) g))) := by
  unfold sourcePair
  exact (normalized_action_continuous A m ell F μ hμ g).inner (𝕜:=ℂ)
    (normalized_action_continuous B m ell F μ hμ g)
private theorem phase_error_measurable(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    Measurable (fun t:ℝ=>ENNReal.ofReal (phaseError m ell F (line μ t) (frequency_nonreal μ hμ t) g)) := by
  have hp:Continuous (fun t:ℝ=>combinedPressure (normalizedState m ell F (line μ t) (frequency_nonreal μ hμ t) g)) := by
    unfold combinedPressure
    exact Complex.continuous_re.comp (normalized_pair_continuous 1 combinedPressureOperator m ell F μ hμ g)
  have hc:Continuous (fun t:ℝ=>coframeContact m ell F (line μ t) (frequency_nonreal μ hμ t) g) := by
    unfold coframeContact
    exact continuous_const.mul (Complex.continuous_im.comp (normalized_pair_continuous (U*D) (SourceCoframeVolumeCurrent.dilation*U) m ell F μ hμ g))
  have hj:Continuous (fun t:ℝ=>jointPrice m ell F (line μ t) (frequency_nonreal μ hμ t) g) := by
    unfold jointPrice
    exact (hp.add ((continuous_const.mul (positive_price_continuous m ell F μ hμ g)).div_const n)).sub
      (continuous_const.mul hc)
  have hphase:Continuous (fun t:ℝ=>jointPhase m ell F (line μ t) (frequency_nonreal μ hμ t) g) := by
    unfold jointPhase
    simp only [line_im]
    exact continuous_const.mul (Complex.continuous_im.comp (normalized_pair_continuous (U*D) 1 m ell F μ hμ g))
  exact (hphase.abs.sub (continuous_const.mul hj)).measurable.ennreal_ofReal

private theorem integrated_joint_word(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    combinedPressureBudget m ell F μ hμ g false ≤
      4*wholeJointBudget m ell F μ hμ g+4*phaseErrorBudget m ell F μ hμ g := by
  unfold combinedPressureBudget wholeJointBudget phaseErrorBudget
  change (∫⁻t:ℝ,ENNReal.ofReal (combinedPressure (normalizedState m ell F (line μ t) _ g))) ≤ _
  calc
    _ ≤ ∫⁻t:ℝ,(4:ENNReal)*ENNReal.ofReal (wholeForcingWord m ell F (line μ t) _ g)+
        4*ENNReal.ofReal (phaseError m ell F (line μ t) _ g) := by
      apply lintegral_mono
      intro t
      have h:=ENNReal.ofReal_le_ofReal (pressure_joint_word m ell F (line μ t) (frequency_nonreal μ hμ t) g)
      exact h.trans (ENNReal.ofReal_add_le.trans (add_le_add
        (by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)];norm_num)
        (by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)];norm_num)))
    _=_ := by
      rw [lintegral_add_right _ ((phase_error_measurable m ell F μ hμ g).const_mul 4),
        lintegral_const_mul' _ _ (by norm_num : (4:ENNReal)≠⊤),
        lintegral_const_mul' _ _ (by norm_num : (4:ENNReal)≠⊤)]

/-- The original pressure consumes the complete joint source word; its half-phase error is paid internally. -/
theorem actual_combined_pressure_joint_common_budget(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),
      combinedPressureBudget m ell F μ hμ g false ≤ ENNReal.ofReal ε+4*wholeJointBudget m ell F μ hμ g := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_joint_scale_phase_common_tail μ hμ g (1/2) (by norm_num) (ε/4) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  have ht:=hF false
  change phaseErrorBudget m ell F μ hμ g ≤ ENNReal.ofReal (ε/4) at ht
  have hb:=(integrated_joint_word m ell F μ hμ g).trans
    (add_le_add le_rfl (mul_le_mul le_rfl ht zero_le zero_le))
  have he:(4:ENNReal)*ENNReal.ofReal (ε/4)=ENNReal.ofReal ε := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,
      ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    congr 1
    ring
  exact hb.trans_eq (by rw [he,add_comm])

/-- Every original sharp Gamma sink directly consumes the untouched complete joint word at one common N and F. -/
theorem actual_original_joint_scale_Gamma_budget(μ:ℝ)(hμ:0<μ)(g k:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),∀sharp:Bool,
      ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤ ENNReal.ofReal ε+
        ENNReal.ofReal (96*sourceMuFactor μ k*radiusPrice*(μ/(16*n)))*wholeJointBudget m ell F μ hμ g := by
  intro ε hε
  let C:=24*sourceMuFactor μ k*radiusPrice*(μ/(16*n))
  have hn:0<n := by change 0<sourceTime 0;rw [source_time_generated];exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hC:0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;positivity
  let δ:=ε/(2*(C+1))
  have hd:0<δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩:=actual_original_combined_pressure_Gamma_budget μ hμ g k (ε/2) (by positivity)
  obtain ⟨N2,h2⟩:=actual_combined_pressure_joint_common_budget μ hμ g δ hd
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hg hp
  intro sharp
  have hb:=(hg sharp).trans (add_le_add le_rfl (mul_le_mul le_rfl hp zero_le zero_le))
  have halloc:ε/2+C*δ ≤ ε := by
    have hs:C*δ ≤ ε/2 := by
      dsimp only [δ]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<2*(C+1))).mpr
      nlinarith only [hε]
    linarith only [hs]
  have hcoef:ENNReal.ofReal C*4=ENNReal.ofReal (96*sourceMuFactor μ k*radiusPrice*(μ/(16*n))) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,←ENNReal.ofReal_mul hC]
    congr 1
    dsimp only [C]
    ring
  change _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal δ+4*wholeJointBudget m ell F μ hμ g) at hb
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal δ+4*wholeJointBudget m ell F μ hμ g) := hb
    _=ENNReal.ofReal (ε/2+C*δ)+
        ENNReal.ofReal (96*sourceMuFactor μ k*radiusPrice*(μ/(16*n)))*wholeJointBudget m ell F μ hμ g := by
      rw [mul_add,←mul_assoc,hcoef,←ENNReal.ofReal_mul hC,←add_assoc,
        ←ENNReal.ofReal_add (by positivity) (mul_nonneg hC hd.le)]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal halloc) le_rfl

end LowEnergy.SourceClockPhiJointScaleGammaBudget
