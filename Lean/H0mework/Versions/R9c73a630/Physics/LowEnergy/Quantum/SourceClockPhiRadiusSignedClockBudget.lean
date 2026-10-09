import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiResponseDampingSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusSignedClockBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceClockAcceleration SourceClockReflectedForm SourceScalarPairedTransport SourceScalarDoubleCurrent
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponsePositiveSource
open SourceClockPhiResponseDampingSource SourceClockYukawaQ8RadiusBudget SourceClockYukawaCubicCurrent
open SourceClockYukawaRadialGammaNativeBudget SourceFourPoleEnergyClosed SourceScalarPositiveBulkWard
open SourceActualResolventEnergy FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
attribute [local irreducible] resolventCore finiteResolvent

/-- One signed source word keeps both forcing pairings and all nonpositive field contributions. -/
def signedClockPrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let v := phiResponseCore m ell F z hz g
  let f := phiResponseSource m ell F z hz g
  2*(sourcePair f (clockCurrent v)).im+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction v) f).re+
    (sourceTime 0/2)*z.re*(sourcePair v (inverseVolumeAction v)).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction v)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction v)-
    sourceTime 0*gaugeForm (inverseVolumeAction v)-sourceTime 0*spatialForm (inverseVolumeAction v)

def signedClockBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (signedClockPrice m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)

private theorem price_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    phiPositivePrice m ell F z hz g=signedClockPrice m ell F z hz g-
      2*z.im*(sourcePair (phiResponseCore m ell F z hz g)
        (clockCurrent (phiResponseCore m ell F z hz g))).re := by
  unfold phiPositivePrice signedClockPrice
  change 2*(sourcePair (phiResponseSource m ell F z hz g)
      (clockCurrent (phiResponseCore m ell F z hz g))).im-
      2*z.im*(sourcePair (phiResponseCore m ell F z hz g)
        (clockCurrent (phiResponseCore m ell F z hz g))).re+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction (phiResponseCore m ell F z hz g))
        (phiResponseSource m ell F z hz g)).re+
      (sourceTime 0/2)*z.re*(sourcePair (phiResponseCore m ell F z hz g)
        (inverseVolumeAction (phiResponseCore m ell F z hz g))).re+
      (sourceTime 0)^2*spinForm (inverseVolumeAction (phiResponseCore m ell F z hz g))+
      (sourceTime 0)^2*densityForm (inverseVolumeAction (phiResponseCore m ell F z hz g))-
      sourceTime 0*gaugeForm (inverseVolumeAction (phiResponseCore m ell F z hz g))-
      sourceTime 0*spatialForm (inverseVolumeAction (phiResponseCore m ell F z hz g))=_
  ring

/-- Half of the actual positive price absorbs damping before any positive-part operation. -/
theorem actual_phi_signed_clock_price (m ell : ℕ) (hml : m ≤ ell) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    phiPositivePrice m ell F z hz g ≤ 2*signedClockPrice m ell F z hz g+
      2*dampingError z.im (1/2) m*
        (‖embed (resolventCore F z hz (coreEquiv.symm g))‖^2+
          ‖embed (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))‖^2) := by
  have hd := actual_phi_damping_source z.im (1/2) (by norm_num) m ell hml F z hz g
  have hs := price_source m ell F z hz g
  let t := (sourcePair (phiResponseCore m ell F z hz g)
    (clockCurrent (phiResponseCore m ell F z hz g))).re
  have ht : -(2*z.im*t) ≤ 2*|z.im| * |t| := by
    calc
      _ ≤ |2*z.im*t| := neg_le_abs _
      _ = _ := by rw [abs_mul,abs_mul];norm_num
  dsimp only [t] at ht
  linarith only [hd,hs,ht]

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private def errorPrice (μ : ℝ) : ℝ :=
  24*μ^2*(scalePrice+12*μ^2/(sourceTime 0)^2)^4

private theorem error_source (μ : ℝ) (m : ℕ) :
    2*dampingError μ (1/2) m=errorPrice μ/(m+2:ℝ) := by
  change 2*(2*(3*μ^2/(1/2))*
    (scalePrice+(3*μ^2/(1/2))/((1/2)*(sourceTime 0)^2))^4/(m+2:ℝ))=_
  unfold errorPrice
  ring

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem original_input_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

private theorem phi_input_embed (g : diagonal.domain) :
    embed (phiRadiusAction (coreEquiv.symm g))=(phiRadiusSource g:H) := rfl

private theorem actual_square (μ : ℝ) (hμ : 0<μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖g‖^2) := by
  simpa only [line,mul_comm (μ:ℂ) Complex.I] using SourceActualResolventEnergy.actual_square_lintegral F μ hμ g

private theorem integrated_price (m ell : ℕ) (hml : m ≤ ell) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    phiPositiveBudget m ell F μ hμ g ≤ 2*signedClockBudget m ell F μ hμ g+
      ENNReal.ofReal (errorPrice μ/(m+2:ℝ)*(Real.pi/μ*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2))) := by
  have hE : 0 ≤ errorPrice μ/(m+2:ℝ) := by unfold errorPrice;positivity
  have hR := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have mg : Measurable (fun w : ℝ => ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2)) :=
    ((hR.clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal
  have mh : Measurable (fun w : ℝ => ENNReal.ofReal (‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2)) :=
    ((hR.clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal
  have me : Measurable (fun w : ℝ => ENNReal.ofReal (errorPrice μ/(m+2:ℝ))*
      (ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2)+
        ENNReal.ofReal (‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2))) :=
    (mg.add mh).const_mul _
  unfold phiPositiveBudget signedClockBudget
  calc
    _ ≤ ∫⁻ w : ℝ,(2:ENNReal)*ENNReal.ofReal (signedClockPrice m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)+ENNReal.ofReal (errorPrice μ/(m+2:ℝ))*
        (ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2)+
          ENNReal.ofReal (‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      have hp := actual_phi_signed_clock_price m ell hml F (line μ w)
        (by simpa only [line_im] using hμ.ne') g
      simp only [line_im] at hp
      rw [error_source,resolvent_embed,resolvent_embed,original_input_embed,phi_input_embed] at hp
      apply (ENNReal.ofReal_le_ofReal hp).trans
      calc
        _ ≤ ENNReal.ofReal (2*signedClockPrice m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g)+
            ENNReal.ofReal (errorPrice μ/(m+2:ℝ)*
              (‖finiteResolvent F (line μ w) (g:H)‖^2+‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2)) :=
          ENNReal.ofReal_add_le
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_mul hE,
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)];norm_num
    _ = _ := by
      rw [lintegral_add_right _ me,lintegral_const_mul' _ _ (by norm_num : (2:ENNReal)≠⊤),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ mh,
        actual_square μ hμ F (g:H),actual_square μ hμ F (phiRadiusSource g:H),
        ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul hE]
      congr 2
      ring

/-- The damping remainder is paid by the masses of the two original fixed inputs for every F. -/
theorem actual_phi_signed_clock_common_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      phiPositiveBudget m ell F μ hμ g ≤ ENNReal.ofReal ε+2*signedClockBudget m ell F μ hμ g := by
  intro ε hε
  let C := errorPrice μ*(Real.pi/μ*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2))
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F => ?_⟩
  have hN' : C/ε < (m+2:ℝ) := by
    have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hN,hm']
  have he : errorPrice μ/(m+2:ℝ)*(Real.pi/μ*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2))=C/(m+2:ℝ) := by
    dsimp only [C]
    ring
  have hs : C/(m+2:ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < m+2)).mpr
    have h := (div_lt_iff₀ hε).mp hN'
    nlinarith only [h]
  have hp := integrated_price m ell hml F μ hμ g
  rw [he] at hp
  exact (hp.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hs))).trans_eq (add_comm _ _)

/-- The original Gamma directly consumes the complete signed clock word with damping already absorbed. -/
theorem actual_original_phi_signed_clock_Gamma_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤ ENNReal.ofReal ε+
          ENNReal.ofReal (8*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2)*signedClockBudget m ell F μ hμ g := by
  intro ε hε
  let C := 4*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2
  have hC : 0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;positivity
  let δ := ε/(2*(C+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  obtain ⟨N1,h1⟩ := actual_original_phi_positive_Gamma_budget μ hμ g k (ε/2) (by positivity)
  obtain ⟨N2,h2⟩ := actual_phi_signed_clock_common_budget μ hμ g δ hδ
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (by omega) ell hml] with F hF
  intro sharp
  have hp := h2 m (by omega) ell hml F
  have h := (hF sharp).trans (add_le_add le_rfl (mul_le_mul le_rfl hp zero_le zero_le))
  have hs : C*δ ≤ ε/2 := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(C+1))).mpr
    nlinarith only [hε]
  have hc : ENNReal.ofReal C*2=ENNReal.ofReal (8*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2) := by
    rw [show (2:ENNReal)=ENNReal.ofReal (2:ℝ) by norm_num,←ENNReal.ofReal_mul hC]
    congr 1
    dsimp only [C]
    ring
  change _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal δ+2*signedClockBudget m ell F μ hμ g) at h
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal δ+2*signedClockBudget m ell F μ hμ g) := h
    _ = ENNReal.ofReal (ε/2+C*δ)+
        ENNReal.ofReal (8*μ*sourceMuFactor μ k*radiusPrice/(sourceTime 0)^2)*signedClockBudget m ell F μ hμ g := by
      rw [mul_add,←mul_assoc,hc,←ENNReal.ofReal_mul hC,←add_assoc,
        ←ENNReal.ofReal_add (by positivity) (mul_nonneg hC hδ.le)]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal (by linarith only [hs])) le_rfl

end LowEnergy.SourceClockPhiRadiusSignedClockBudget
