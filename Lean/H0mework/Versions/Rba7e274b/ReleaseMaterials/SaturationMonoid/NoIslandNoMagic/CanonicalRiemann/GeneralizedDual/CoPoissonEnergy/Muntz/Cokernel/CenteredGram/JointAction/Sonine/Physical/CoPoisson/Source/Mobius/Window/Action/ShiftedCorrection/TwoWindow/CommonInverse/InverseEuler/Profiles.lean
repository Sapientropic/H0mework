import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Raw
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "S" => burnolMeanZeroTruncatedFourier
local instance quarterFinite : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem state_integrable (state : BurnolQuarterMeanZeroCarrier) :
    Integrable (state:BurnolQuarterIntervalL2) μq :=
  (Lp.memLp (state:BurnolQuarterIntervalL2)).integrable (by norm_num)
private theorem state_moment (state : BurnolQuarterMeanZeroCarrier) :
    Integrable (fun x:ℝ=>‖x‖*‖(state:BurnolQuarterIntervalL2) x‖) μq := by
  have majorant:=(state_integrable state).norm.const_mul q
  apply majorant.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg _))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [symmetricInterval,mem_Icc,Real.norm_eq_abs,abs_le] using inside
private theorem state_clm_moment (state : BurnolQuarterMeanZeroCarrier) :
    Integrable (VectorFourier.fourierSMulRight (innerSL ℝ)
      (state:BurnolQuarterIntervalL2)) μq := by
  have majorant:=(state_moment state).const_mul (2*Real.pi*‖innerSL (E:=ℝ) ℝ‖)
  apply majorant.mono'
  · exact (Lp.memLp (state:BurnolQuarterIntervalL2)).aestronglyMeasurable.fourierSMulRight
  · filter_upwards with x
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le
      (innerSL (E:=ℝ) ℝ) (state:BurnolQuarterIntervalL2) x

theorem state_fourier_hasDerivAt (state : BurnolQuarterMeanZeroCarrier) (x : ℝ) :
    HasDerivAt (Constructor.fourierRaw (state:BurnolQuarterIntervalL2))
      (Constructor.fourierDerivative (state:BurnolQuarterIntervalL2) x) x := by
  have generated:=VectorFourier.hasFDerivAt_fourierIntegral (innerSL ℝ)
    (state_integrable state) (state_moment state) x
  unfold Constructor.fourierRaw Constructor.fourierDerivative
  have bilinear : (innerₗ ℝ)=(innerSL ℝ).toLinearMap₁₂ := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    simp only [innerₗ_apply_apply,ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      innerSL_apply_apply]
  rw [bilinear]
  exact generated.hasDerivAt

theorem state_derivative_continuous (state : BurnolQuarterMeanZeroCarrier) :
    Continuous (Constructor.fourierDerivative (state:BurnolQuarterIntervalL2)) := by
  unfold Constructor.fourierDerivative
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,innerSL_apply_apply]
      using (continuous_inner : Continuous (fun p:ℝ×ℝ=>inner ℝ p.1 p.2)))
    (state_clm_moment state)).clm_apply continuous_const

theorem meanZeroRaw_hasDerivAt (state : BurnolQuarterMeanZeroCarrier) (x : ℝ) :
    HasDerivAt (burnolMeanZeroFourierRaw state)
      (Constructor.fourierDerivative (state:BurnolQuarterIntervalL2) x) x :=
  (state_fourier_hasDerivAt state x).sub_const _
theorem meanZeroRaw_continuous (state : BurnolQuarterMeanZeroCarrier) :
    Continuous (burnolMeanZeroFourierRaw state) :=
  continuous_iff_continuousAt.mpr fun x=>(meanZeroRaw_hasDerivAt state x).continuousAt

def xProfile (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : (ℝ→ℂ)×(ℝ→ℂ) :=
  (fun x=>bCotestRaw coordinate h (-h/2) (h/2) x+
      burnolMeanZeroFourierRaw (inversePartner coordinate h).1 x,
   fun x=>bCotestRaw coordinate h (h/2) (-h/2) x+
      burnolMeanZeroFourierRaw (inversePartner coordinate h).2 x)
def yProfile (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : (ℝ→ℂ)×(ℝ→ℂ) :=
  (fun x=>burnolMeanZeroFourierRaw (inverseCotest coordinate h).1 x-
      pCotestRaw coordinate h (-h/2) (h/2) x,
   fun x=>burnolMeanZeroFourierRaw (inverseCotest coordinate h).2 x-
      pCotestRaw coordinate h (h/2) (-h/2) x)
def xDerivative (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : (ℝ→ℂ)×(ℝ→ℂ) :=
  (fun x=>evenBandDerivative h (-h/2) (bLeg coordinate (h/2)) x+
      Constructor.fourierDerivative ((inversePartner coordinate h).1:BurnolQuarterIntervalL2) x,
   fun x=>evenBandDerivative h (h/2) (bLeg coordinate (-h/2)) x+
      Constructor.fourierDerivative ((inversePartner coordinate h).2:BurnolQuarterIntervalL2) x)
def yDerivative (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : (ℝ→ℂ)×(ℝ→ℂ) :=
  (fun x=>Constructor.fourierDerivative ((inverseCotest coordinate h).1:BurnolQuarterIntervalL2) x-
      evenBandDerivative h (-h/2) (pLeg coordinate (h/2)) x,
   fun x=>Constructor.fourierDerivative ((inverseCotest coordinate h).2:BurnolQuarterIntervalL2) x-
      evenBandDerivative h (h/2) (pLeg coordinate (-h/2)) x)

theorem xProfile_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    HasDerivAt (xProfile coordinate h).1 ((xDerivative coordinate h).1 x) x ∧
    HasDerivAt (xProfile coordinate h).2 ((xDerivative coordinate h).2 x) x :=
  ⟨(bCotestRaw_hasDerivAt coordinate h (-h/2) (h/2) x).add (meanZeroRaw_hasDerivAt _ x),
   (bCotestRaw_hasDerivAt coordinate h (h/2) (-h/2) x).add (meanZeroRaw_hasDerivAt _ x)⟩
theorem yProfile_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    HasDerivAt (yProfile coordinate h).1 ((yDerivative coordinate h).1 x) x ∧
    HasDerivAt (yProfile coordinate h).2 ((yDerivative coordinate h).2 x) x :=
  ⟨(meanZeroRaw_hasDerivAt _ x).sub (pCotestRaw_hasDerivAt coordinate h (-h/2) (h/2) x),
   (meanZeroRaw_hasDerivAt _ x).sub (pCotestRaw_hasDerivAt coordinate h (h/2) (-h/2) x)⟩
theorem xProfile_continuous (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    Continuous (xProfile coordinate h).1 ∧ Continuous (xProfile coordinate h).2 :=
  ⟨continuous_iff_continuousAt.mpr fun x=>(xProfile_hasDerivAt coordinate h x).1.continuousAt,
   continuous_iff_continuousAt.mpr fun x=>(xProfile_hasDerivAt coordinate h x).2.continuousAt⟩
theorem yProfile_continuous (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    Continuous (yProfile coordinate h).1 ∧ Continuous (yProfile coordinate h).2 :=
  ⟨continuous_iff_continuousAt.mpr fun x=>(yProfile_hasDerivAt coordinate h x).1.continuousAt,
   continuous_iff_continuousAt.mpr fun x=>(yProfile_hasDerivAt coordinate h x).2.continuousAt⟩

private theorem profileX_read (X Y Cb : BurnolQuarterMeanZeroCarrier) (raw : ℝ→ℂ)
    (equation : X-S Y=Cb)
    (read : (Cb:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    (X:BurnolQuarterIntervalL2)=ᵐ[μq] fun x=>raw x+burnolMeanZeroFourierRaw Y x := by
  have state : (X:BurnolQuarterIntervalL2)=(Cb:BurnolQuarterIntervalL2)+(S Y:BurnolQuarterIntervalL2) :=
    congrArg Subtype.val (eq_add_of_sub_eq equation)
  rw [state]
  filter_upwards [Lp.coeFn_add (Cb:BurnolQuarterIntervalL2) (S Y:BurnolQuarterIntervalL2),
    read,burnolMeanZeroFourier_ae_raw Y] with x addition original fourier
  rw [addition]
  change (Cb:BurnolQuarterIntervalL2) x+(S Y:BurnolQuarterIntervalL2) x=_
  rw [original,fourier]
private theorem profileY_read (X Y Cp : BurnolQuarterMeanZeroCarrier) (raw : ℝ→ℂ)
    (equation : Y-S X=-Cp)
    (read : (Cp:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    (Y:BurnolQuarterIntervalL2)=ᵐ[μq] fun x=>burnolMeanZeroFourierRaw X x-raw x := by
  have carrier : Y=S X-Cp := by rw [sub_eq_add_neg]; exact eq_add_of_sub_eq' equation
  have state : (Y:BurnolQuarterIntervalL2)=(S X:BurnolQuarterIntervalL2)-(Cp:BurnolQuarterIntervalL2) :=
    congrArg Subtype.val carrier
  rw [state]
  filter_upwards [Lp.coeFn_sub (S X:BurnolQuarterIntervalL2) (Cp:BurnolQuarterIntervalL2),
    read,burnolMeanZeroFourier_ae_raw X] with x difference original fourier
  rw [difference]
  change (S X:BurnolQuarterIntervalL2) x-(Cp:BurnolQuarterIntervalL2) x=_
  rw [original,fourier]

theorem actual_inverse_profiles (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    ((inverseCotest coordinate h).1:BurnolQuarterIntervalL2)=ᵐ[μq] (xProfile coordinate h).1 ∧
    ((inversePartner coordinate h).1:BurnolQuarterIntervalL2)=ᵐ[μq] (yProfile coordinate h).1 ∧
    ((inverseCotest coordinate h).2:BurnolQuarterIntervalL2)=ᵐ[μq] (xProfile coordinate h).2 ∧
    ((inversePartner coordinate h).2:BurnolQuarterIntervalL2)=ᵐ[μq] (yProfile coordinate h).2 := by
  obtain ⟨lowerB,lowerP,upperB,upperP⟩:=actual_inverse_pair coordinate h
  exact ⟨profileX_read _ _ _ _ lowerB (bCotestRaw_read coordinate h (-h/2) (h/2) nonnegative),
    profileY_read _ _ _ _ lowerP (pCotestRaw_read coordinate h (-h/2) (h/2) nonnegative),
    profileX_read _ _ _ _ upperB (bCotestRaw_read coordinate h (h/2) (-h/2) nonnegative),
    profileY_read _ _ _ _ upperP (pCotestRaw_read coordinate h (h/2) (-h/2) nonnegative)⟩

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
