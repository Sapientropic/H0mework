import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockRadiusAffineCutoff
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusSourceCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockFixedInputSeed
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusResponsePositiveSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceCoframeDilation
open SourceClockAcceleration SourceClockReflectedForm SourceScalarPairedTransport
open SourceMixedNativeReturn SourceClockPhiRadiusSourceCurrent SourceClockYukawaQ8RadiusBudget SourceClockYukawaCubicCurrent
open SourceScalarPositiveBulkWard SourceActualResolventEnergy SourceScalarDoubleCurrent
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore defectAction resolventCore diagonalAction

private theorem clock_current_real (f : QuantumTest) : (sourcePair f (clockCurrent f)).im=0 := by
  have hc := GaussNativeForm.pair_conjugate f (clockCurrent f)
  rw [←SourceClockFixedInputSeed.original_clock_current_pair] at hc
  have h := congrArg Complex.im hc
  simp only [Complex.conj_im] at h
  linarith only [h]

private theorem inverse_real (f : QuantumTest) : (sourcePair f (inverseVolumeAction f)).im=0 := by
  have hc := GaussNativeForm.pair_conjugate f (inverseVolumeAction f)
  have hp : sourcePair f (inverseVolumeAction f)=sourcePair (inverseVolumeAction f) f := multiply_pair _ _ _ _
  rw [←hp] at hc
  have h := congrArg Complex.im hc
  simp only [Complex.conj_im] at h
  linarith only [h]

private theorem completed_pair_source (f : QuantumTest) :
    (sourcePair f (completedAcceleration f)).re=
      2*(sourcePair (diagonalAction f) (clockCurrent f)).im+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) (diagonalAction f)).re := by
  have hJ := SourceClockFixedInputSeed.original_clock_current_pair f (diagonalAction f)
  have hH := diagonalAction_pair f (clockCurrent f)
  have hV : sourcePair f (inverseVolumeAction (diagonalAction f))=
      sourcePair (inverseVolumeAction f) (diagonalAction f) := multiply_pair _ _ _ _
  have hVH := diagonalAction_pair f (inverseVolumeAction f)
  have hconj := GaussNativeForm.pair_conjugate (diagonalAction f) (clockCurrent f)
  have hconjV := GaussNativeForm.pair_conjugate (inverseVolumeAction f) (diagonalAction f)
  unfold completedAcceleration clockAcceleration
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right]
  change (((-Complex.I)*(sourcePair f (diagonalAction (clockCurrent f))-
    sourcePair f (clockCurrent (diagonalAction f))))+
    ((sourceTime 0:ℂ)/4)*(sourcePair f (inverseVolumeAction (diagonalAction f))+
      sourcePair f (diagonalAction (inverseVolumeAction f)))).re=_
  rw [hJ,hH,hV,hVH,←hconj,←hconjV]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re]
  norm_num
  simp only [sourcePair]
  ring

private def positiveSourcePrice (z : ℂ) (f u : QuantumTest) : ℝ :=
  2*(sourcePair u (clockCurrent f)).im-2*z.im*(sourcePair f (clockCurrent f)).re+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u).re+
    (sourceTime 0/2)*z.re*(sourcePair f (inverseVolumeAction f)).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction f)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction f)-
    sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f)

private theorem positive_price_source (z : ℂ) (f u : QuantumTest)
    (he : diagonalAction f=u+z • f) :
    positiveSourcePrice z f u=
      (sourceTime 0)^2/4*coframeGram (inverseVolumeAction f)+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f)+
      2*(sourceTime 0)^2*radiusForm f := by
  have hb := completed_pair_source f
  rw [he] at hb
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,inner_add_right,inner_smul_right] at hb
  change (sourcePair f (completedAcceleration f)).re=
    2*(sourcePair u (clockCurrent f)+(starRingEnd ℂ z)*sourcePair f (clockCurrent f)).im+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u+z*sourcePair (inverseVolumeAction f) f).re at hb
  have hv : sourcePair (inverseVolumeAction f) f=sourcePair f (inverseVolumeAction f) := (multiply_pair _ _ _ _).symm
  rw [hv] at hb
  simp only [Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    clock_current_real,inverse_real,mul_zero,sub_zero] at hb
  have hs := original_completed_square_form f
  unfold positiveSourcePrice
  linarith only [hb,hs]

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) : 0 ≤ (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · have h := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
      (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
    exact (sq_nonneg _).trans_eq h.symm
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem radius_floor (f : QuantumTest) : 3*‖embed f‖^2 ≤ radiusForm f := by
  let c : SourceCoordinateSlice → ℝ := fun z => 4*(GaussYukawaCoefficient.radius z)^2-1
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul (GaussYukawaCoefficient.radius_smooth.pow 2)).sub contDiff_const
  let A : End := multiply c (fun _ => hc.contDiffAt)
  have hr : radiusForm f=(sourcePair f (A f)).re := rfl
  have hpair : (sourcePair f (A f)).re=∫ z : SourceCoordinateSlice,(densityPair f (A f) z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f (A f))).symm
  rw [hr,hpair,GaussBoundedMultiplier.norm_square_integral,←integral_const_mul]
  apply integral_mono ((densityPair_integrable f f).re.const_mul 3) (densityPair_integrable f (A f)).re
  intro z
  change 3*(densityPair f f z).re ≤ (densityPair f (A f) z).re
  have he : densityPair f (A f) z=(c z:ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hr := GaussRadialDomain.one_le_radius z
  have hc3 : 3 ≤ c z := by dsimp only [c];nlinarith only [hr]
  exact mul_le_mul_of_nonneg_right hc3 (density_nonnegative f z)


open FullYSourceResolventGraphSplice SourceResolventBandLimit

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem core_inverse (F : Index) (z : ℂ) (hz : z.im≠0) :
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 := by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    map_sub,map_smul,compression_embed,resolvent_embed]
  have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] using h

private theorem generated_window_source (T : End) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    diagonalAction (T (bracket phiRadiusAction (resolventCore F z hz) (coreEquiv.symm g)))=
      bracket diagonalAction T (bracket phiRadiusAction (resolventCore F z hz) (coreEquiv.symm g))+
      T (phiRadiusCurrent (resolventCore F z hz (coreEquiv.symm g)))+
      T ((phiRadiusAction*defectAction F*resolventCore F z hz-defectAction F*resolventCore F z hz*phiRadiusAction)
        (coreEquiv.symm g))+
      z • T (bracket phiRadiusAction (resolventCore F z hz) (coreEquiv.symm g)) := by
  have hm (H D A B R : End) (h : (H-D-z • (1:End))*R=1) :
      H*A*bracket B R=bracket H A*bracket B R+A*bracket H B*R+
        A*(B*D*R-D*R*B)+z • (A*bracket B R) := by
    unfold bracket
    linear_combination (norm := noncomm_ring) A*B*h-A*h*B
    all_goals module
  have he : diagonalAction-defectAction F=compressionCore F := by unfold defectAction;abel
  have h := LinearMap.congr_fun
    (hm diagonalAction (defectAction F) T phiRadiusAction (resolventCore F z hz)
      (by rw [he];exact core_inverse F z hz)) (coreEquiv.symm g)
  rw [original_phi_radius_hamiltonian_current] at h
  exact h

private theorem source_positive_slots (z : ℂ) (f u : QuantumTest)
    (he : diagonalAction f=u+z • f) :
    (sourceTime 0)^2/4*coframeGram (inverseVolumeAction f)+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f)+
      6*(sourceTime 0)^2*‖embed f‖^2 ≤ positiveSourcePrice z f u := by
  rw [positive_price_source z f u he]
  have hr := mul_le_mul_of_nonneg_left (radius_floor f)
    (by positivity : 0 ≤ 2*(sourceTime 0)^2)
  nlinarith only [hr]

open SourceClockRadiusAffineCutoff SourceClockYukawaRadialGammaNativeBudget SourceFourPoleEnergyClosed

private theorem lapse_pos : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- The same homogeneous response keeps its entire original compressed source word. -/
def phiResponseSource (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  bracket diagonalAction (phiThetaAction m ell)
      (bracket phiRadiusAction (resolventCore F z hz) (coreEquiv.symm g))+
    phiThetaAction m ell (phiRadiusCurrent (resolventCore F z hz (coreEquiv.symm g)))+
    phiThetaAction m ell ((phiRadiusAction*defectAction F*resolventCore F z hz-
      defectAction F*resolventCore F z hz*phiRadiusAction) (coreEquiv.symm g))

theorem actual_phi_response_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    diagonalAction (phiResponseCore m ell F z hz g)=
      phiResponseSource m ell F z hz g+z • phiResponseCore m ell F z hz g := by
  exact generated_window_source (phiThetaAction m ell) F z hz g

/-- Completion consumes the actual response forcing before any field is estimated. -/
def phiPositivePrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  positiveSourcePrice z (phiResponseCore m ell F z hz g) (phiResponseSource m ell F z hz g)

theorem actual_phi_positive_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    phiPositivePrice m ell F z hz g=
      (sourceTime 0)^2/4*coframeGram (inverseVolumeAction (phiResponseCore m ell F z hz g))+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction (phiResponseCore m ell F z hz g))+
      2*(sourceTime 0)^2*radiusForm (phiResponseCore m ell F z hz g) :=
  positive_price_source z _ _ (actual_phi_response_source m ell F z hz g)

/-- Both moving weighted derivative slots and the strong response are generated by one price. -/
theorem actual_phi_positive_slots (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (sourceTime 0)^2/4*coframeGram (inverseVolumeAction (phiResponseCore m ell F z hz g))+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction (phiResponseCore m ell F z hz g))+
      6*(sourceTime 0)^2*‖embed (phiResponseCore m ell F z hz g)‖^2 ≤
        phiPositivePrice m ell F z hz g :=
  source_positive_slots z _ _ (actual_phi_response_source m ell F z hz g)

private theorem actual_phi_norm_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    6*(sourceTime 0)^2*‖embed (phiResponseCore m ell F z hz g)‖^2 ≤ phiPositivePrice m ell F z hz g := by
  have h := actual_phi_positive_slots m ell F z hz g
  have hc := original_coframe_gram_nonnegative (inverseVolumeAction (phiResponseCore m ell F z hz g))
  have hs : 0 ≤ scalarForm (inverseVolumeAction (phiResponseCore m ell F z hz g)) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc' := mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/4) hc
  have hs' := mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/2) hs
  linarith only [h,hc',hs']

def phiPositiveBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ, ENNReal.ofReal (phiPositivePrice m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)

/-- The original retarded frequency measure consumes the same positive response source. -/
theorem actual_phi_positive_budget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    phiResponseBudget m ell F μ hμ g ≤
      ENNReal.ofReal (μ/(6*(sourceTime 0)^2))*phiPositiveBudget m ell F μ hμ g := by
  have hn : sourceTime 0≠0 := lapse_pos.ne'
  have hC : 0 ≤ μ/(6*(sourceTime 0)^2) := by positivity
  unfold phiResponseBudget phiPositiveBudget
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal (μ/(6*(sourceTime 0)^2))*
        ENNReal.ofReal (phiPositivePrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left
        (actual_phi_norm_price m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g) hC
      have he : (μ/(6*(sourceTime 0)^2))*(6*(sourceTime 0)^2*
          ‖embed (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2)=
          μ*‖embed (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2 := by
        field_simp [hn]
      exact he ▸ h
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The original Gamma returns through the paid center and cutoff bridges to this single source price. -/
theorem actual_original_phi_positive_Gamma_budget (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+
            ENNReal.ofReal (4*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2)*
              phiPositiveBudget m ell F μ hμ g := by
  intro ε hε
  let C := 6*sourceMuFactor μ k*radiusPrice
  have hC : 0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;positivity
  let δ := ε/(2*(C+1))
  have hδ : 0 < δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩ := actual_original_Q8_radius_response_budget μ hμ g k (ε/2) (by positivity)
  obtain ⟨N2,h2⟩ := actual_original_radius_homogeneous_budget μ hμ g δ hδ
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hg hr
  intro sharp
  have hφ := actual_phi_positive_budget m ell F μ hμ g
  have h := (hg sharp).trans (add_le_add le_rfl (mul_le_mul le_rfl
    (hr.trans (add_le_add le_rfl (mul_le_mul le_rfl hφ zero_le zero_le))) zero_le zero_le))
  have hA : 0 ≤ C*δ := mul_nonneg hC hδ.le
  have halloc : ε/2+C*δ ≤ ε := by
    have hsmall : C*δ ≤ ε/2 := by
      dsimp only [δ]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2*(C+1))).mpr
      nlinarith only [hε]
    linarith only [hsmall]
  have hcoef : C*4*(μ/(6*(sourceTime 0)^2))=4*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2 := by
    dsimp only [C]
    ring
  have hδE : ENNReal.ofReal C*ENNReal.ofReal δ=ENNReal.ofReal (C*δ) := (ENNReal.ofReal_mul hC).symm
  have hfactor : ENNReal.ofReal C*4*ENNReal.ofReal (μ/(6*(sourceTime 0)^2))=
      ENNReal.ofReal (4*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,
      ←ENNReal.ofReal_mul hC,←ENNReal.ofReal_mul (mul_nonneg hC (by norm_num : (0:ℝ) ≤ 4)),hcoef]
  change _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*
    (ENNReal.ofReal δ+4*(ENNReal.ofReal (μ/(6*(sourceTime 0)^2))*phiPositiveBudget m ell F μ hμ g)) at h
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*
        (ENNReal.ofReal δ+4*(ENNReal.ofReal (μ/(6*(sourceTime 0)^2))*phiPositiveBudget m ell F μ hμ g)) := h
    _ = ENNReal.ofReal (ε/2+C*δ)+
        ENNReal.ofReal (4*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2)*phiPositiveBudget m ell F μ hμ g := by
      rw [mul_add,←mul_assoc,←mul_assoc,hδE,hfactor,←add_assoc,
        ←ENNReal.ofReal_add (by positivity) hA]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal halloc) le_rfl

end LowEnergy.SourceClockPhiRadiusResponsePositiveSource
