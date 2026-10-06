import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaJointRadialZeroBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaJointSpinRemainingBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaJointDefectForce
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaGammaPrincipalForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaJointDualFieldBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaSpinJointForce
open SourceClockYukawaJointSpinRemainingBudget SourceClockYukawaSpinNativeAbsorption
open SourceClockYukawaJointCoframeForce
open SourceClockYukawaCubicCurrent
open SourceClockYukawaRadialMixedClock SourceClockYukawaRadialGammaNativeBudget SourceClockYukawaSpinClosure
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialMixedBudget
open SourceRelativePowerTail SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceFourPoleEnergyClosed MeasureTheory Filter
open scoped InnerProductSpace Topology
attribute [local irreducible] jointState jointForcing spinWord nativeWord remainingWord
  sourceMuFactor mixedState mixedPrice SourceClockYukawaRadialMixedGamma.mixedResponse

open SourceClockYukawaJointRadialZero SourceClockYukawaJointDefectForce SourceClockYukawaGammaPrincipalForm
open SourceClockYukawaJointRadialZeroBudget

/-- Both branches use the same original windowState and its retained weighted gamma error. -/
def dualFieldImag (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  (sourceTime 0/4)*(sourcePair (windowState m ell F z hz g)
    (weightedGammaPrincipalCore (windowState m ell F z hz g))).im-
    (gammaWeightedError m ell F z hz g).im+
    (∑ sharp : Bool,∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (matterWord sharp m ell F z hz g mu+coherentDefectWord sharp m ell F z hz g mu)).im

def dualFieldPrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain)
    (η ξ ζ τ : ℝ) : ℝ :=
  (η+ζ+τ)*(sourceTime 0)^2*(∑ sharp : Bool,jointCoframe (jointState sharp m ell F z hz g))+
    ξ*(sourceTime 0)^2*(∑ sharp : Bool,scalarColumn (jointState sharp m ell F z hz g))-
    dualFieldImag m ell F z hz g

def dualFieldBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η ξ ζ τ : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (dualFieldPrice m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η ξ ζ τ)

def dualMuEnergy (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (μ*(∑ sharp : Bool,columnNorm (jointState sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)))

private theorem bool_pair_sum (f : Bool → ℂ) : (∑ sharp : Bool,f sharp)=f false+f true := by
  simp only [Fintype.sum_bool]
  ring

/-- The full dual field word returns before any clipping, with its exact gamma endpoint and coherent defect. -/
theorem actual_dual_field_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ sharp : Bool,∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (fieldRemainingWord sharp m ell F z hz g mu)).im=dualFieldImag m ell F z hz g := by
  have hfalse := actual_joint_field_defect_source false m ell F z hz g
  have htrue := actual_joint_field_defect_source true m ell F z hz g
  have hgamma := actual_joint_gamma_word_form m ell F z hz g
  rw [bool_pair_sum]
  simp only [Complex.add_im]
  rw [hfalse,htrue]
  unfold dualFieldImag
  rw [bool_pair_sum]
  simp only [sourcePair,map_add,inner_add_right,Finset.sum_add_distrib,Complex.add_im] at *
  linarith only [hgamma]

private theorem full_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    jointForcing sharp m ell F z hz g mu=
      spinWord sharp m ell F z hz g mu+nativeWord sharp m ell F z hz g mu+
      coframeWord sharp m ell F z hz g mu+paidRadialWord sharp m ell F z hz g mu+
      fieldRemainingWord sharp m ell F z hz g mu := by
  rw [actual_joint_native_forcing_source,actual_joint_coframe_forcing_source,actual_joint_radial_zero_source]
  abel

private theorem joint_spin_price_nonnegative : 0 ≤ jointPrice := by unfold jointPrice;positivity
private theorem coframe_price_nonnegative : 0 ≤ coframePrice := by
  change 0≤(∑ t : Fin 8×Fin 8×Fin 3,‖coframeMatrix t.2.2 t.1 t.2.1‖^2)*
    SourceClockYukawaCoframeRotationRows.rotationPrice/4
  unfold SourceClockYukawaCoframeRotationRows.rotationPrice
  positivity

private def fixedCoefficient (η ζ : ℝ) : ℝ := jointPrice/η+coframePrice/ζ
private def branchError (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η ξ ζ τ : ℝ) : ℝ :=
  fixedCoefficient η ζ*columnNorm (errorColumn sharp m ell F z hz g)+
    (1/(4*ξ))*coefficientEnergy sharp m ell F z hz g+
    (1/(100*τ))*radialEnergy sharp m ell F z hz g
private def dualError (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain)
    (η ξ ζ τ : ℝ) : ℝ := ∑ sharp : Bool,branchError sharp m ell F z hz g η ξ ζ τ

private theorem branch_point (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η ξ ζ τ : ℝ) (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    z.im*columnNorm (jointState sharp m ell F z hz g) ≤
      (η+ζ+τ)*(sourceTime 0)^2*jointCoframe (jointState sharp m ell F z hz g)+
      ξ*(sourceTime 0)^2*scalarColumn (jointState sharp m ell F z hz g)-
      (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
        (fieldRemainingWord sharp m ell F z hz g mu)).im+
      branchError sharp m ell F z hz g η ξ ζ τ := by
  have hs := original_joint_spin_pair_price sharp (windowState m ell F z hz g)
    (errorColumn sharp m ell F z hz g) η hη
  have hs' : |(∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (spinWord sharp m ell F z hz g mu)).im| ≤
    η*(sourceTime 0)^2*jointCoframe (jointState sharp m ell F z hz g)+
      jointPrice/η*columnNorm (errorColumn sharp m ell F z hz g) := by
    simpa only [jointState,spinWord] using hs
  have hc := original_joint_coframe_pair_price sharp (windowState m ell F z hz g)
    (errorColumn sharp m ell F z hz g) ζ hζ
  have hc' : |(∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (coframeWord sharp m ell F z hz g mu)).im| ≤
    ζ*(sourceTime 0)^2*jointCoframe (jointState sharp m ell F z hz g)+
      coframePrice/ζ*columnNorm (errorColumn sharp m ell F z hz g) := by
    simpa only [jointState,coherentColumn,coframeWord] using hc
  have hn := actual_joint_native_pair_price sharp m ell F z hz g ξ hξ
  have hr := actual_joint_radial_zero_pair_price sharp m ell F z hz g τ hτ
  have hnegS := neg_le_abs (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
    (spinWord sharp m ell F z hz g mu)).im
  have hnegC := neg_le_abs (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
    (coframeWord sharp m ell F z hz g mu)).im
  have hnegN := (neg_le_abs (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
    (nativeWord sharp m ell F z hz g mu)).im).trans (Complex.abs_im_le_norm _)
  have hnegR := (neg_le_abs (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
    (paidRadialWord sharp m ell F z hz g mu)).im).trans (Complex.abs_im_le_norm _)
  rw [actual_joint_mu_ward]
  simp_rw [full_source]
  simp only [sourcePair,map_add,inner_add_right,Finset.sum_add_distrib,Complex.add_im]
  unfold branchError fixedCoefficient
  simp only [sourcePair,div_eq_mul_inv] at hs' hc' hn hr hnegS hnegC hnegN hnegR ⊢
  linarith only [hs',hc',hn,hr,hnegS,hnegC,hnegN,hnegR]

private theorem dual_point (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain)
    (η ξ ζ τ : ℝ) (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    z.im*(∑ sharp : Bool,columnNorm (jointState sharp m ell F z hz g)) ≤
      dualFieldPrice m ell F z hz g η ξ ζ τ+dualError m ell F z hz g η ξ ζ τ := by
  have hp := add_le_add (branch_point false m ell F z hz g η ξ ζ τ hη hξ hζ hτ)
    (branch_point true m ell F z hz g η ξ ζ τ hη hξ hζ hτ)
  have hf := actual_dual_field_source m ell F z hz g
  rw [bool_pair_sum] at hf
  simp only [Complex.add_im] at hf
  unfold dualFieldPrice dualError
  simp only [Fintype.sum_bool]
  linarith only [hp,hf]

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line_im] using hμ.ne'
private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem error_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    embed (errorColumn sharp m ell F z hz g mu)=
      inverseRadius (finiteResolvent F z (relativeTail m ell (embed (spinClosureCoefficient sharp mu (inputCore g)))))-
      finiteResolvent F z (inverseRadius (relativeTail m ell (embed (spinClosureCoefficient sharp mu (inputCore g))))) := by
  simp only [errorColumn,radialMap,LinearMap.sub_apply,Module.End.mul_apply,map_sub,
    ←inverse_core,resolvent_embed,←SourceMixedNativeReturn.theta_core]
private theorem error_energy_measurable (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : Measurable (fun w : ℝ => ENNReal.ofReal
      (columnNorm (errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g))) := by
  have hc : Continuous (fun w : ℝ => columnNorm (errorColumn sharp m ell F (line μ w) (line_nonreal μ hμ w) g)) := by
    unfold columnNorm
    apply continuous_finsetSum
    intro mu _
    simp_rw [error_embed]
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    exact (((inverseRadius.continuous.comp (hr.clm_apply continuous_const)).sub
      (hr.clm_apply continuous_const)).norm.pow 2)
  exact hc.measurable.ennreal_ofReal

private theorem error_nonnegative (q : Column) : 0 ≤ columnNorm q :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
private theorem coefficient_nonnegative (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) : 0 ≤ coefficientEnergy sharp m ell F z hz g := by
  unfold coefficientEnergy
  positivity
private theorem radial_nonnegative (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) : 0 ≤ radialEnergy sharp m ell F z hz g := by
  unfold radialEnergy
  exact error_nonnegative _
private theorem fixed_nonnegative (η ζ : ℝ) (hη : 0<η) (hζ : 0<ζ) : 0 ≤ fixedCoefficient η ζ :=
  add_nonneg (div_nonneg joint_spin_price_nonnegative hη.le) (div_nonneg coframe_price_nonnegative hζ.le)
private theorem branch_error_nonnegative (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (η ξ ζ τ : ℝ)
    (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) : 0 ≤ branchError sharp m ell F z hz g η ξ ζ τ := by
  unfold branchError
  exact add_nonneg (add_nonneg (mul_nonneg (fixed_nonnegative η ζ hη hζ) (error_nonnegative _))
    (mul_nonneg (by positivity) (coefficient_nonnegative _ _ _ _ _ _ _)))
    (mul_nonneg (by positivity) (radial_nonnegative _ _ _ _ _ _ _))

private theorem branch_error_ofReal (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (η ξ ζ τ : ℝ)
    (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    ENNReal.ofReal (branchError sharp m ell F z hz g η ξ ζ τ)=
      ENNReal.ofReal (fixedCoefficient η ζ)*ENNReal.ofReal (columnNorm (errorColumn sharp m ell F z hz g))+
      ENNReal.ofReal (1/(4*ξ))*ENNReal.ofReal (coefficientEnergy sharp m ell F z hz g)+
      ENNReal.ofReal (1/(100*τ))*ENNReal.ofReal (radialEnergy sharp m ell F z hz g) := by
  have hE := mul_nonneg (fixed_nonnegative η ζ hη hζ) (error_nonnegative (errorColumn sharp m ell F z hz g))
  have hG := mul_nonneg (show 0≤1/(4*ξ) by positivity) (coefficient_nonnegative sharp m ell F z hz g)
  have hR := mul_nonneg (show 0≤1/(100*τ) by positivity) (radial_nonnegative sharp m ell F z hz g)
  unfold branchError
  rw [ENNReal.ofReal_add (add_nonneg hE hG) hR,ENNReal.ofReal_add hE hG,
    ENNReal.ofReal_mul (fixed_nonnegative η ζ hη hζ),ENNReal.ofReal_mul (by positivity : 0≤1/(4*ξ)),
    ENNReal.ofReal_mul (by positivity : 0≤1/(100*τ))]

private theorem branch_error_measurable (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η ξ ζ τ : ℝ)
    (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    Measurable (fun w : ℝ => ENNReal.ofReal (branchError sharp m ell F (line μ w)
      (line_nonreal μ hμ w) g η ξ ζ τ)) := by
  simp_rw [branch_error_ofReal sharp m ell F _ _ g η ξ ζ τ hη hξ hζ hτ]
  have hE := error_energy_measurable sharp m ell F μ hμ g
  have hG := SourceClockYukawaSpinNativeBudget.actual_joint_native_energy_measurable sharp m ell F μ hμ (inputSource g)
  have hR := actual_joint_radial_energy_measurable sharp m ell hml F μ hμ g
  exact ((hE.const_mul _).add (hG.const_mul _)).add (hR.const_mul _)

private theorem dual_error_measurable (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η ξ ζ τ : ℝ)
    (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    Measurable (fun w : ℝ => ENNReal.ofReal (dualError m ell F (line μ w)
      (line_nonreal μ hμ w) g η ξ ζ τ)) := by
  simp_rw [dualError,ENNReal.ofReal_sum_of_nonneg (fun sharp _ =>
    branch_error_nonnegative sharp m ell F _ _ g η ξ ζ τ hη hξ hζ hτ)]
  exact Finset.measurable_sum _ (fun sharp _ => branch_error_measurable sharp m ell hml F μ hμ g η ξ ζ τ hη hξ hζ hτ)

private theorem dual_error_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η ξ ζ τ : ℝ) (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (dualError m ell F (line μ w) (line_nonreal μ hμ w) g η ξ ζ τ)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := fixedCoefficient η ζ+1/(4*ξ)+1/(100*τ)
  have hC : 0 ≤ C := by dsimp [C];exact add_nonneg (add_nonneg (fixed_nonnegative η ζ hη hζ) (by positivity)) (by positivity)
  let δ := ε/(2*(C+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨NE,hE⟩ := actual_joint_error_common_tail μ hμ g δ hδ
  obtain ⟨NG,hG⟩ := SourceClockYukawaSpinNativeBudget.actual_joint_native_coefficient_tail μ hμ (inputSource g) δ hδ
  obtain ⟨NR,hR⟩ := actual_joint_radial_energy_common_tail μ hμ g δ hδ
  refine ⟨max NE (max NG NR),fun m hm ell hml => ?_⟩
  filter_upwards [hG m (by omega) ell hml] with F hg
  have he := hE m (by omega) ell hml F
  have hr := hR m (by omega) ell hml F
  have hb (sharp : Bool) :
      (∫⁻ w : ℝ,ENNReal.ofReal (branchError sharp m ell F (line μ w) (line_nonreal μ hμ w) g η ξ ζ τ)) ≤
        ENNReal.ofReal (C*δ) := by
    simp_rw [branch_error_ofReal sharp m ell F _ _ g η ξ ζ τ hη hξ hζ hτ]
    have mG : Measurable (fun w : ℝ => ENNReal.ofReal
        (coefficientEnergy sharp m ell F (line μ w) (line_nonreal μ hμ w) g)) :=
      SourceClockYukawaSpinNativeBudget.actual_joint_native_energy_measurable sharp m ell F μ hμ (inputSource g)
    have mR := actual_joint_radial_energy_measurable sharp m ell hml F μ hμ g
    rw [lintegral_add_right _ (mR.const_mul _),lintegral_add_right _ (mG.const_mul _)]
    simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ENNReal.ofReal (fixedCoefficient η ζ)*ENNReal.ofReal δ+
          ENNReal.ofReal (1/(4*ξ))*ENNReal.ofReal δ+ENNReal.ofReal (1/(100*τ))*ENNReal.ofReal δ := by
        exact add_le_add (add_le_add (mul_le_mul le_rfl (he sharp) zero_le zero_le)
          (mul_le_mul le_rfl (hg sharp) zero_le zero_le)) (mul_le_mul le_rfl (hr sharp) zero_le zero_le)
      _ = _ := by
        rw [←ENNReal.ofReal_mul (fixed_nonnegative η ζ hη hζ),←ENNReal.ofReal_mul (by positivity : 0≤1/(4*ξ)),
          ←ENNReal.ofReal_mul (by positivity : 0≤1/(100*τ)),
          ←ENNReal.ofReal_add (mul_nonneg (fixed_nonnegative η ζ hη hζ) hδ.le) (by positivity),
          ←ENNReal.ofReal_add (add_nonneg (mul_nonneg (fixed_nonnegative η ζ hη hζ) hδ.le) (by positivity)) (by positivity)]
        congr 1
        dsimp [C]
        ring
  simp_rw [dualError,ENNReal.ofReal_sum_of_nonneg (fun sharp _ =>
    branch_error_nonnegative sharp m ell F _ _ g η ξ ζ τ hη hξ hζ hτ)]
  rw [lintegral_finsetSum Finset.univ (fun sharp _ => branch_error_measurable sharp m ell hml F μ hμ g η ξ ζ τ hη hξ hζ hτ)]
  calc
    _ ≤ ∑ _ : Bool,ENNReal.ofReal (C*δ) := Finset.sum_le_sum (fun sharp _ => hb sharp)
    _ = ENNReal.ofReal (2*(C*δ)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg hC hδ.le)]
      congr 1
      simp
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      have hd : δ*(2*(C+1))=ε := by dsimp [δ];field_simp
      nlinarith only [hd,hδ]

private theorem dual_integral (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η ξ ζ τ : ℝ)
    (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    dualMuEnergy m ell F μ hμ g ≤ dualFieldBudget m ell F μ hμ g η ξ ζ τ+
      (∫⁻ w : ℝ,ENNReal.ofReal (dualError m ell F (line μ w) (line_nonreal μ hμ w) g η ξ ζ τ)) := by
  unfold dualMuEnergy dualFieldBudget
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (dualFieldPrice m ell F (line μ w) (line_nonreal μ hμ w) g η ξ ζ τ)+
        ENNReal.ofReal (dualError m ell F (line μ w) (line_nonreal μ hμ w) g η ξ ζ τ) := by
      apply lintegral_mono
      intro w
      have hp := dual_point m ell F (line μ w) (line_nonreal μ hμ w) g η ξ ζ τ hη hξ hζ hτ
      rw [line_im] at hp
      exact (ENNReal.ofReal_le_ofReal hp).trans ENNReal.ofReal_add_le
    _ = _ := by rw [lintegral_add_right _ (dual_error_measurable m ell hml F μ hμ g η ξ ζ τ hη hξ hζ hτ)]

/-- Sixteen positive mu components are combined before the first ofReal; every paid source tail is internal. -/
theorem actual_joint_dual_mu_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η ξ ζ τ : ℝ)
    (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        dualMuEnergy m ell F μ hμ g ≤ ENNReal.ofReal ε+dualFieldBudget m ell F μ hμ g η ξ ζ τ := by
  intro ε hε
  obtain ⟨N,hN⟩ := dual_error_common_tail μ hμ g η ξ ζ τ hη hξ hζ hτ ε hε
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  exact ((dual_integral m ell hml F μ hμ g η ξ ζ τ hη hξ hζ hτ).trans
    (add_le_add le_rfl hF)).trans_eq (add_comm _ _)

private theorem actual_mixed_amplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    mixedAmplitude sharp m ell F z g k=
      inner ℂ (k:H) (finiteResolvent F z (embed (jointState sharp m ell F z hz g 0))) := by
  rw [actual_joint_zero_state]
  unfold mixedAmplitude SourceClockYukawaRadialMixedClock.mixedState
  have he : embed (coreEquiv.symm (radiusSource g))=(radiusSource g:H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [←he,actual_mixed_response_source sharp m ell F z hz]

private theorem amplitude_joint_mu_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖mixedAmplitude sharp m ell F (line μ w) g k‖^2 ≤ sourceMuFactor μ k*
      (μ*columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
  let z := line μ w
  have hz : z.im≠0 := by simpa only [z,line_im] using hμ.ne'
  let f := jointState sharp m ell F z hz g 0
  have hR : ‖finiteResolvent F z‖ ≤ 1/μ := by
    simpa only [z,line_im,abs_of_pos hμ] using finite_resolvent_norm F z hz
  have hi := (norm_inner_le_norm (𝕜 := ℂ) (k:H) (finiteResolvent F z (embed f))).trans
    (mul_le_mul_of_nonneg_left (((finiteResolvent F z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) (norm_nonneg (k:H)))
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have hs : ‖embed f‖^2 ≤ columnNorm (jointState sharp m ell F z hz g) :=
    Finset.single_le_sum (fun mu _ => sq_nonneg ‖embed (jointState sharp m ell F z hz g mu)‖)
      (Finset.mem_univ (0:Fin 8))
  have hc : 0 ≤ sourceMuFactor μ k := by unfold sourceMuFactor;positivity
  have he : (‖(k:H)‖*((1/μ)*‖embed f‖))^2=sourceMuFactor μ k*(μ*‖embed f‖^2) := by
    unfold sourceMuFactor
    field_simp
  rw [he] at hi2
  rw [actual_mixed_amplitude sharp m ell F _ hz]
  exact hi2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hμ.le) hc)

private theorem real_member_le_sum (f : Bool → ℝ) (hf : ∀ s,0 ≤ f s) (sharp : Bool) :
    f sharp ≤ ∑ s,f s :=
  Finset.single_le_sum (fun s _ => hf s) (Finset.mem_univ sharp)

private theorem actual_dual_mu_cost (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    mixedResponseCost sharp m ell F μ hμ g k ≤ ENNReal.ofReal (sourceMuFactor μ k)*dualMuEnergy m ell F μ hμ g := by
  have hc : 0 ≤ sourceMuFactor μ k := by unfold sourceMuFactor;positivity
  unfold mixedResponseCost dualMuEnergy
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (sourceMuFactor μ k)*ENNReal.ofReal
      (μ*(∑ s : Bool,columnNorm (jointState s m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      have hs : columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g) ≤
          ∑ s : Bool,columnNorm (jointState s m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g) :=
        real_member_le_sum
          (fun s : Bool => columnNorm (jointState s m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))
          (fun s : Bool => error_nonnegative (jointState s m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) sharp
      exact (amplitude_joint_mu_bound sharp m ell F μ hμ g k w).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hμ.le) hc)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Original Gamma directly consumes the same-source joint word after the complete dual source payment. -/
theorem actual_original_joint_dual_field_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (η ξ ζ τ : ℝ) (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3*sourceMuFactor μ k)*dualFieldBudget m ell F μ hμ g η ξ ζ τ := by
  intro ε hε
  let κ := 3*sourceMuFactor μ k
  have hκ : 0 ≤ κ := by dsimp [κ];unfold sourceMuFactor;positivity
  let δ := ε/(2*(κ+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N₀,h₀⟩ := actual_original_mixed_response_budget false μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := actual_original_mixed_response_budget true μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_joint_dual_mu_budget μ hμ g η ξ ζ τ hη hξ hζ hτ δ hδ
  refine ⟨max N₀ (max N₁ N₂),fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml,h₂ m (by omega) ell hml] with F hf ht hdual sharp
  have hg : ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
      ENNReal.ofReal (ε/2)+ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k := by
    cases sharp <;> assumption
  have hc := mul_le_mul (le_refl (ENNReal.ofReal (3:ℝ))) (actual_dual_mu_cost sharp m ell F μ hμ g k) zero_le zero_le
  rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)] at hc
  have hp : ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hκ,←ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd : δ*(2*(κ+1))=ε := by dsimp [δ];field_simp
    nlinarith only [hd,hδ]
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*dualMuEnergy m ell F μ hμ g := hg.trans (add_le_add (le_refl _) hc)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*(ENNReal.ofReal δ+dualFieldBudget m ell F μ hμ g η ξ ζ τ) :=
      add_le_add (le_refl _) (mul_le_mul le_rfl hdual zero_le zero_le)
    _ = (ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ)+
        ENNReal.ofReal κ*dualFieldBudget m ell F μ hμ g η ξ ζ τ := by rw [mul_add,add_assoc]
    _ ≤ _ := add_le_add hp le_rfl

end LowEnergy.SourceClockYukawaJointDualFieldBudget
