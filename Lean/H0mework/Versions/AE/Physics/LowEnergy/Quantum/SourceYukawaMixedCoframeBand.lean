import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceYukawaMixedCoframeBand
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourcePhysicalKineticSquare SourceCoframeVolumeCurrent
open SourceClockReflectedForm SourceClockWindowTime SourceRadiusHalfWindow SourceRadiusBandGradient
open FullYSourceResolventGraphSplice SourceScalarPairedTransport MeasureTheory
open SourceScalarPositiveBulkWard
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem band_nonnegative (m ell : ℕ) (z : SourceCoordinateSlice) :
    0≤coefficient m ell z := by
  unfold coefficient SourceRadiusBandPolynomial.band
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg
    (sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))) _)

private theorem theta_band (m ell : ℕ) (hml : m≤ell) (z : SourceCoordinateSlice) :
    SourceNativeCutoffContact.theta m ell z=coefficient m ell z/radius z := by
  have he : SourceRadiusBandPolynomial.band m ell (1-reciprocal z)=
      ∑ j∈Finset.Ico (m+1) (ell+1),(1-reciprocal z)^j :=
    Finset.sum_Ico_add' (fun j => (1-reciprocal z)^j) m ell 1
  have h := geom_sum_Ico_mul_neg (1-reciprocal z)
    (show m+1≤ell+1 by omega)
  rw [←he] at h
  simpa only [sub_sub_cancel,SourceNativeCutoffContact.theta,coefficient,reciprocal,
    div_eq_mul_inv] using h.symm

private theorem band_upper (m ell : ℕ) (hml : m≤ell) (z : SourceCoordinateSlice) :
    coefficient m ell z≤radius z := by
  have hq : 0≤1-reciprocal z := sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))
  have hq1 : 1-reciprocal z≤1 := by have h := (inv_pos.mpr (radius_pos z)).le;change 1-(radius z)⁻¹≤1;linarith
  have ht : SourceNativeCutoffContact.theta m ell z≤1 := by
    exact (sub_le_self _ (pow_nonneg hq _)).trans (pow_le_one₀ hq hq1)
  rw [theta_band m ell hml z] at ht
  exact (div_le_iff₀ (radius_pos z)).mp ht |>.trans_eq (one_mul _)

private def bandFactor (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (Real.sqrt (1+coefficient m ell z)+1)/radius z

private theorem factor_smooth (m ell : ℕ) : ContDiff ℝ ∞ (bandFactor m ell) := by
  have hr : ContDiff ℝ ∞ (fun z => Real.sqrt (1+coefficient m ell z)) :=
    (contDiff_const.add (coefficient_smooth m ell)).sqrt (fun z => by
      have h := band_nonnegative m ell z;linarith)
  exact (hr.add contDiff_const).div radius_smooth (fun z => (radius_pos z).ne')

private theorem factor_bound (m ell : ℕ) (hml : m≤ell) (z : SourceCoordinateSlice) :
    |bandFactor m ell z|≤3 := by
  have hr := one_le_radius z
  have hA := band_upper m ell hml z
  have hs : Real.sqrt (1+coefficient m ell z)≤2*radius z := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hA,hr,sq_nonneg (radius z-1)]
  have hb : 0≤bandFactor m ell z := by unfold bandFactor;positivity
  rw [abs_of_nonneg hb]
  apply (div_le_iff₀ (radius_pos z)).mpr
  nlinarith only [hs,hr]

private def factorAction (m ell : ℕ) : End :=
  multiply (bandFactor m ell) (fun _ => (factor_smooth m ell).contDiffAt)

private theorem factor_half (m ell : ℕ) (hml : m≤ell) :
    SourceMixedNativeReturn.thetaAction m ell=factorAction m ell*halfAction m ell := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  change (SourceNativeCutoffContact.theta m ell z:ℂ) • f z=
    (bandFactor m ell z:ℂ) • ((halfCoefficient m ell z:ℂ) • f z)
  rw [smul_smul]
  congr 1
  have hs := Real.sq_sqrt (show 0≤1+coefficient m ell z by have h := band_nonnegative m ell z;linarith)
  have he : bandFactor m ell z*halfCoefficient m ell z=SourceNativeCutoffContact.theta m ell z := by
    rw [theta_band m ell hml z]
    unfold bandFactor halfCoefficient
    field_simp [(radius_pos z).ne']
    nlinarith only [hs]
  exact_mod_cast he.symm

private theorem real_factor (m ell : ℕ) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c hc) (factorAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (bandFactor m ell z:ℂ) (f z)

private theorem local_factor (m ell : ℕ) (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) :
    Commute (localMultiplier A hA) (factorAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (bandFactor m ell z:ℂ) (f z)

private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 0) (hz : γ 0=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) : fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 0 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem factor_shift (m ell : ℕ) (z : SourceCoordinateSlice) (i : Fin 6) (r : ℝ) :
    bandFactor m ell (z+r • GaussCoframeCore.coframeDirection i)=bandFactor m ell z := by
  simp only [bandFactor,coefficient,SourceRadiusBandPolynomial.band,reciprocal,radius,
    GaussCoframeCore.coframeDirection,Prod.smul_mk,Prod.snd_add,smul_zero,add_zero]

private theorem coframe_factor (m ell : ℕ) (i : Fin 6) :
    Commute (SourceCoframeCovariantAction.covariantMomentum i) (factorAction m ell) := by
  have hd : Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i))
      (factorAction m ell) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    let e := GaussCoframeCore.coframeDirection i
    let A := ((bandFactor m ell z:ℂ) • ContinuousLinearMap.id ℂ FockFiber).restrictScalars ℝ
    have hg : HasDerivAt (fun r : ℝ => z+r • e) e 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add z
    have he := invariant_derivative A f (factorAction m ell f) (fun r : ℝ => z+r • e) z e hg
      (by simp) ((f.contDiff.differentiable (by simp)) z)
      (((factorAction m ell f).contDiff.differentiable (by simp)) z) (fun r => by
        change (bandFactor m ell (z+r • e):ℂ) • f (z+r • e)=
          (bandFactor m ell z:ℂ) • f (z+r • e)
        rw [factor_shift])
    change GaussCoframeCore.derivative e (factorAction m ell f) z=
      factorAction m ell (GaussCoframeCore.derivative e f) z
    rw [GaussCoframeCore.derivative_apply]
    change fderiv ℝ (factorAction m ell f) z e=
      (bandFactor m ell z:ℂ) • (GaussCoframeCore.derivative e f z)
    rw [GaussCoframeCore.derivative_apply]
    exact he
  exact (hd.smul_left (-Complex.I)).add_left (local_factor m ell _ _)

private theorem factor_norm (m ell : ℕ) (hml : m≤ell) (f : QuantumTest) :
    ‖embed (factorAction m ell f)‖≤3*‖embed f‖ := by
  apply GaussBoundedMultiplier.action_bound
    (fun z => (bandFactor m ell z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun z => (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
      (factor_smooth m ell).contDiffAt).smul contDiffAt_const)
    (fun _ w => (Commute.one_right (GaussFockWeights.weight w)).smul_right _) 3 (by norm_num) _ f
  intro z x
  change ‖(bandFactor m ell z.val:ℂ) • x‖≤3*‖x‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (factor_bound m ell hml z.val) (norm_nonneg x)

private def gramRow (j : Fin 6) : End :=
  ![SourceCoframeVolumeCurrent.coordinateAction 0*SourceCoframeCovariantAction.covariantMomentum 0,
    SourceCoframeVolumeCurrent.coordinateAction 1*SourceCoframeCovariantAction.covariantMomentum 1+
      SourceCoframeVolumeCurrent.coordinateAction 2*SourceCoframeCovariantAction.covariantMomentum 2,
    SourceCoframeVolumeCurrent.coordinateAction 3*SourceCoframeCovariantAction.covariantMomentum 3+
      SourceCoframeVolumeCurrent.coordinateAction 4*SourceCoframeCovariantAction.covariantMomentum 4+
      SourceCoframeVolumeCurrent.coordinateAction 5*SourceCoframeCovariantAction.covariantMomentum 5,
    SourceCoframeVolumeCurrent.coordinateAction 0*SourceCoframeCovariantAction.covariantMomentum 1,
    SourceCoframeVolumeCurrent.coordinateAction 0*SourceCoframeCovariantAction.covariantMomentum 3,
    SourceCoframeVolumeCurrent.coordinateAction 1*SourceCoframeCovariantAction.covariantMomentum 3+
      SourceCoframeVolumeCurrent.coordinateAction 2*SourceCoframeCovariantAction.covariantMomentum 4] j

private def rowWeight (j : Fin 6) : ℝ := if j.val<3 then 2 else 4

private theorem row_factor (m ell : ℕ) (j : Fin 6) : Commute (gramRow j) (factorAction m ell) := by
  have h (i k : Fin 6) : Commute (coordinateAction i*SourceCoframeCovariantAction.covariantMomentum k)
      (factorAction m ell) := (real_factor m ell _ _).mul_left (coframe_factor m ell k)
  fin_cases j
  · exact h 0 0
  · exact (h 1 1).add_left (h 2 2)
  · exact ((h 3 3).add_left (h 4 4)).add_left (h 5 5)
  · exact h 0 1
  · exact h 0 3
  · exact (h 1 3).add_left (h 2 4)

private def densityRoot (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  GaussFockWeights.weight (fun N => (Real.sqrt (GaussDensityCore.density N z):ℂ))

private theorem real_fock_smul (c : ℝ) (v : FockFiber) : c • v=(c:ℂ) • v := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem root_real_smul (z : SourceCoordinateSlice) (c : ℝ) (v : FockFiber) :
    densityRoot z (c • v)=c • densityRoot z v := by
  rw [real_fock_smul,map_smul,←real_fock_smul]

private theorem density_root_square (f : QuantumTest) (z : SourceCoordinateSlice) :
    ‖densityRoot z (f z)‖^2=(densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · exact (GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
      (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)).symm
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp [hf,densityPair]

private theorem square_integral (f : QuantumTest) :
    Integrable (fun z => ‖densityRoot z (f z)‖^2) GaussHistoryHilbert.configurationMeasure ∧
      (∫ z,‖densityRoot z (f z)‖^2 ∂GaussHistoryHilbert.configurationMeasure)=‖embed f‖^2 := by
  simp_rw [density_root_square]
  exact ⟨(densityPair_integrable f f).re,(GaussBoundedMultiplier.norm_square_integral f).symm⟩

private theorem gram_point (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceCoframeClockGram.clockGram z.1
      (fun i => densityRoot z ((SourceCoframeCovariantAction.covariantMomentum i f) z))=
      ∑ j : Fin 6,rowWeight j*‖densityRoot z (gramRow j f z)‖^2 := by
  have he (i : Fin 6) (q : QuantumTest) : coordinateAction i q z=z.1 i • q z := by
    simp only [real_fock_smul]
    rfl
  simp [SourceCoframeClockGram.clockGram,gramRow,rowWeight,Fin.sum_univ_succ,
    LinearMap.add_apply,Module.End.mul_apply,he,map_add]
  abel

private theorem gram_rows (f : QuantumTest) :
    coframeGram f=∑ j : Fin 6,rowWeight j*‖embed (gramRow j f)‖^2 := by
  change (∫ z,SourceCoframeClockGram.clockGram z.1
    (fun i => densityRoot z ((SourceCoframeCovariantAction.covariantMomentum i f) z))
    ∂GaussHistoryHilbert.configurationMeasure)=_
  simp_rw [gram_point]
  rw [integral_finsetSum _ (fun j _ => ((square_integral (gramRow j f)).1).const_mul _)]
  simp_rw [integral_const_mul,(square_integral _).2]

private theorem factor_gram (m ell : ℕ) (hml : m≤ell) (f : QuantumTest) :
    coframeGram (factorAction m ell f)≤9*coframeGram f := by
  rw [gram_rows,gram_rows,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have he := LinearMap.congr_fun (row_factor m ell j).eq f
  have hn := factor_norm m ell hml (gramRow j f)
  have hw : 0≤rowWeight j := by unfold rowWeight;split_ifs <;> norm_num
  change gramRow j (factorAction m ell f)=factorAction m ell (gramRow j f) at he
  rw [he]
  have hs : ‖embed (factorAction m ell (gramRow j f))‖^2≤9*‖embed (gramRow j f)‖^2 := by
    nlinarith only [hn,norm_nonneg (embed (factorAction m ell (gramRow j f))),norm_nonneg (embed (gramRow j f))]
  exact (mul_le_mul_of_nonneg_left hs hw).trans_eq (by ring)

/-- The full Number-weighted coframe Gram carries the same theta window into the paid half window. -/
theorem original_theta_coframe_half (m ell : ℕ) (hml : m≤ell) (f : QuantumTest) :
    coframeGram (inverseVolumeAction (SourceMixedNativeReturn.thetaAction m ell f))≤
      9*coframeGram (inverseVolumeAction (halfAction m ell f)) := by
  have hv : Commute inverseVolumeAction (factorAction m ell) := real_factor m ell _ _
  rw [factor_half m ell hml]
  change coframeGram (inverseVolumeAction (factorAction m ell (halfAction m ell f)))≤_
  have he := LinearMap.congr_fun hv.eq (halfAction m ell f)
  change inverseVolumeAction (factorAction m ell (halfAction m ell f))=
    factorAction m ell (inverseVolumeAction (halfAction m ell f)) at he
  rw [he]
  exact factor_gram m ell hml (inverseVolumeAction (halfAction m ell f))

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) : 0≤(densityPair f f z).re := by
  rw [←density_root_square]
  positivity

private theorem radius_nonnegative (f : QuantumTest) : 0≤radiusForm f := by
  let c : SourceCoordinateSlice → ℝ := fun z => 4*radius z^2-1
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul (GaussYukawaCoefficient.radius_smooth.pow 2)).sub contDiff_const
  let A : End := multiply c (fun _ => hc.contDiffAt)
  have hpair : radiusForm f=∫ z : SourceCoordinateSlice,(densityPair f (A f) z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
    change (sourcePair f (A f)).re=_
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f _)).symm
  rw [hpair]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (A f) z).re
  have he : densityPair f (A f) z=(c z:ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  apply mul_nonneg _ (density_nonnegative f z)
  change 0≤4*radius z^2-1
  have hr := one_le_radius z
  nlinarith only [hr,sq_nonneg (radius z-1)]

/-- The original resolvent theta coframe cost is paid directly by the existing actual clock source price. -/
theorem original_theta_coframe_source_price (F : Index) (m ell : ℕ) (hml : m≤ell)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (sourceTime 0)^2*coframeGram
      (inverseVolumeAction (SourceMixedNativeReturn.thetaAction m ell (state F z hz g)))≤
      36*sourcePrice F m ell z hz g := by
  have hb := mul_le_mul_of_nonneg_left (original_theta_coframe_half m ell hml (state F z hz g))
    (sq_nonneg (sourceTime 0))
  rw [actual_clock_source_price]
  have hs : 0 ≤ scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g))) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hr := radius_nonnegative (halfAction m ell (state F z hz g))
  have hs' := mul_nonneg (show 0≤(sourceTime 0)^2/2 by positivity) hs
  have hr' := mul_nonneg (show 0≤2*(sourceTime 0)^2 by positivity) hr
  nlinarith only [hb,hs',hr']

end LowEnergy.SourceYukawaMixedCoframeBand
