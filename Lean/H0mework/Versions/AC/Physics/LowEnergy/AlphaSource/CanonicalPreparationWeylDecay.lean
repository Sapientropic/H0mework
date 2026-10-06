import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylSmooth

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylDecay
open PreparationVacuumWeyl PreparationActualFactor CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory Set Filter
open scoped Topology ContDiff SchwartzMap BigOperators FourierTransform

def positionCompact : Set PhysicalMomentum := flatPosition ⁻¹' thetaPositionClosed

theorem positionCompact_closed : IsClosed positionCompact :=
  thetaPositionClosed_closed.preimage flatPosition.continuous

theorem positionCompact_compact : IsCompact positionCompact :=
  flatPosition.toHomeomorph.isCompact_preimage.mpr thetaPositionClosed_compact

theorem positionCompact_measure : (volume : Measure PhysicalMomentum) positionCompact=
    flatMeasure thetaPositionClosed :=
  actual_flatPosition_measure.measure_preimage thetaPositionClosed_closed.measurableSet.nullMeasurableSet

def derivativeCompact : Set (PhysicalMomentum × PhysicalMomentum) :=
  positionCompact ×ˢ Metric.sphere 0 1

theorem derivativeCompact_compact : IsCompact derivativeCompact :=
  positionCompact_compact.prod (isCompact_sphere _ _)

theorem sourceDerivativeBound_exists (j : ℕ) :
    ∃ bound : ℝ, 0≤bound ∧ ∀ xp∈derivativeCompact,
      ‖iteratedFDeriv ℝ j jointSymbol xp‖≤bound := by
  have cont : Continuous (fun xp => ‖iteratedFDeriv ℝ j jointSymbol xp‖) :=
    (jointSymbol_smooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))).norm
  obtain ⟨bound,hbound⟩ := derivativeCompact_compact.bddAbove_image cont.continuousOn
  refine ⟨max bound 0,le_max_right _ _,?_⟩
  intro xp hx
  exact (hbound (mem_image_of_mem _ hx)).trans (le_max_left _ _)

def sourceDerivativeBound (j : ℕ) : ℝ := Classical.choose (sourceDerivativeBound_exists j)

theorem sourceDerivativeBound_nonnegative (j : ℕ) : 0≤ sourceDerivativeBound j :=
  (Classical.choose_spec (sourceDerivativeBound_exists j)).1

theorem sourceDerivativeBound_bounds (j : ℕ) (xp : PhysicalMomentum × PhysicalMomentum)
    (inside : xp∈derivativeCompact) : ‖iteratedFDeriv ℝ j jointSymbol xp‖≤ sourceDerivativeBound j :=
  (Classical.choose_spec (sourceDerivativeBound_exists j)).2 xp inside

theorem x_derivative_restriction (j : ℕ) (p x : PhysicalMomentum) :
    ‖iteratedFDeriv ℝ j (symbolSlice p) x‖≤‖iteratedFDeriv ℝ j jointSymbol (x,p)‖ := by
  let inclusion : PhysicalMomentum →L[ℝ] PhysicalMomentum × PhysicalMomentum :=
    ContinuousLinearMap.inl ℝ PhysicalMomentum PhysicalMomentum
  let translated : PhysicalMomentum × PhysicalMomentum → ℂ :=
    fun w => jointSymbol (w+(0,p))
  have smooth : ContDiff ℝ ∞ translated := jointSymbol_smooth.comp (contDiff_id.add contDiff_const)
  have same : symbolSlice p=translated ∘ inclusion := by
    ext y
    simp [translated,inclusion,jointSymbol]
  rw [same,inclusion.iteratedFDeriv_comp_right smooth x
    (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))]
  have translation : iteratedFDeriv ℝ j translated (inclusion x)=
      iteratedFDeriv ℝ j jointSymbol (x,p) := by
    dsimp only [translated]
    rw [iteratedFDeriv_comp_add_right]
    simp [inclusion]
  rw [translation]
  exact (iteratedFDeriv ℝ j jointSymbol (x,p)).norm_compContinuous_linearIsometry_le
    (fun _ => LinearIsometry.inl ℝ PhysicalMomentum PhysicalMomentum)

theorem symbolSlice_position_support (p : PhysicalMomentum) : tsupport (symbolSlice p)⊆positionCompact := by
  apply closure_minimal _ positionCompact_closed
  intro x hx
  by_contra outside
  apply hx
  have rawOutside : flatPosition x∉thetaPositionClosed := outside
  simp only [symbolSlice,b1,factorWeight,sourceThetaRoot_split,
    positionRoot_zero_outside rawOutside,zero_mul,Complex.ofReal_zero]

theorem x_derivative_zero_outside (j : ℕ) (p x : PhysicalMomentum) (outside : x∉positionCompact) :
    iteratedFDeriv ℝ j (symbolSlice p) x=0 := by
  by_contra nonzero
  exact outside (symbolSlice_position_support p
    (support_iteratedFDeriv_subset j (show x∈Function.support (iteratedFDeriv ℝ j (symbolSlice p))
      from nonzero)))

theorem unit_derivative_bound (j : ℕ) (p x : PhysicalMomentum) (unit : ‖p‖=1) :
    ‖iteratedFDeriv ℝ j (symbolSlice p) x‖≤ sourceDerivativeBound j := by
  by_cases inside : x∈positionCompact
  · exact (x_derivative_restriction j p x).trans (sourceDerivativeBound_bounds j (x,p)
      ⟨inside,by simpa only [Metric.mem_sphere,dist_zero_right] using unit⟩)
  · rw [x_derivative_zero_outside j p x inside,norm_zero]
    exact sourceDerivativeBound_nonnegative j

theorem radialRoot_bound (p : PhysicalMomentum) : 0≤radialRoot p ∧ radialRoot p≤1 :=
  ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (chi_le_one _)⟩

theorem x_derivative_order_one (j : ℕ) (p x : PhysicalMomentum) :
    ‖iteratedFDeriv ℝ j (symbolSlice p) x‖≤ sourceDerivativeBound j*‖p‖ := by
  by_cases nonzero : p≠0
  · rw [symbolSlice_radial p nonzero,iteratedFDeriv_const_smul_apply
      ((symbolSlice_smooth (unitMomentum p)).of_le
        (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))).contDiffAt,norm_smul]
    have radial := radialRoot_bound p
    have coefficient : ‖((‖p‖*radialRoot p : ℝ) : ℂ)‖≤‖p‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) radial.1)]
      exact mul_le_of_le_one_right (norm_nonneg _) radial.2
    calc
      _ ≤ ‖p‖*sourceDerivativeBound j := mul_le_mul coefficient
        (unit_derivative_bound j _ x (unitMomentum_norm p nonzero)) (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · have pzero : p=0 := not_not.mp nonzero
    subst p
    have zero : symbolSlice (0 : PhysicalMomentum)=(fun _ => (0 : ℂ)) := by
      ext y
      simp only [symbolSlice,b1_zero_low (flatPosition y,0) (by norm_num),Complex.ofReal_zero]
    rw [zero,norm_zero,mul_zero]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero,norm_zero,le_refl]
    | succ j => rw [iteratedFDeriv_succ_const]; simp

def sourceDerivativeIntegralBound (j : ℕ) : ℝ := sourcePositionVolume*sourceDerivativeBound j

theorem sourceDerivativeIntegralBound_nonnegative (j : ℕ) : 0≤ sourceDerivativeIntegralBound j :=
  mul_nonneg sourcePositionVolume_nonnegative (sourceDerivativeBound_nonnegative j)

theorem derivative_integral_bound (j : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ j (symbolSlice p) x‖)≤
      sourceDerivativeIntegralBound j*‖p‖ := by
  have integrable : Integrable (fun x : PhysicalMomentum => ‖iteratedFDeriv ℝ j (symbolSlice p) x‖) :=
    (symbolSlice_smooth p).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤)) |>.integrable_of_hasCompactSupport
      ((symbolSlice_compact p).iteratedFDeriv j) |>.norm
  have finite : (volume : Measure PhysicalMomentum) positionCompact≠⊤ :=
    positionCompact_compact.measure_ne_top
  have supportEq : (∫ x in positionCompact,‖iteratedFDeriv ℝ j (symbolSlice p) x‖)=
      ∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ j (symbolSlice p) x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [x_derivative_zero_outside j p x hx,norm_zero])
  calc
    _ = ∫ x in positionCompact,‖iteratedFDeriv ℝ j (symbolSlice p) x‖ := supportEq.symm
    _ ≤ ∫ _x in positionCompact,sourceDerivativeBound j*‖p‖ :=
      setIntegral_mono_on integrable.integrableOn (integrableOn_const finite)
        positionCompact_closed.measurableSet (fun x _ => x_derivative_order_one j p x)
    _ = sourceDerivativeIntegralBound j*‖p‖ := by
      rw [setIntegral_const]
      change ((volume : Measure PhysicalMomentum) positionCompact).toReal*(sourceDerivativeBound j*‖p‖)=_
      rw [positionCompact_measure]
      change sourcePositionVolume*(sourceDerivativeBound j*‖p‖)=_
      rw [sourceDerivativeIntegralBound]
      ring

def sourceRapidBound : ℝ :=
  2^101*(sourceDerivativeIntegralBound 0+2^102*
    ∑ j∈Finset.range 103,sourceDerivativeIntegralBound j)

theorem sourceRapidBound_nonnegative : 0≤ sourceRapidBound := by
  unfold sourceRapidBound
  exact mul_nonneg (by positivity) (add_nonneg (sourceDerivativeIntegralBound_nonnegative 0)
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sourceDerivativeIntegralBound_nonnegative j)))

theorem partialFourier_rapid_bound (p k : PhysicalMomentum) :
    (1+‖k‖)^102*‖partialFourier p k‖≤ sourceRapidBound*‖p‖ := by
  have zero : ‖partialFourier p k‖≤ sourceDerivativeIntegralBound 0*‖p‖ := by
    apply (partialFourier_norm_bound p k).trans
    simpa only [norm_iteratedFDeriv_zero] using derivative_integral_bound 0 p
  have high : ‖k‖^102*‖partialFourier p k‖≤
      2^102*(∑ j∈Finset.range 103,sourceDerivativeIntegralBound j)*‖p‖ := by
    have transformed := Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞)) (symbolSlice_smooth p)
      (fun a j _ _ => (sourceSchwartzSlice p).integrable_pow_mul_iteratedFDeriv volume a j)
      (k := 0) (n := 102) (by simp) (by simp) k
    simp at transformed
    apply transformed.trans
    have sum := Finset.sum_le_sum (s := Finset.range 103)
      (fun j _ => derivative_integral_bound j p)
    rw [←Finset.sum_mul] at sum
    exact (mul_le_mul_of_nonneg_left sum (by positivity)).trans_eq (by ring)
  have binomial := add_pow_le (by norm_num : (0 : ℝ)≤1) (norm_nonneg k) 102
  simp only [one_pow] at binomial
  calc
    _ ≤ (2^101*(1+‖k‖^102))*‖partialFourier p k‖ :=
      mul_le_mul_of_nonneg_right binomial (norm_nonneg _)
    _ = 2^101*(‖partialFourier p k‖+‖k‖^102*‖partialFourier p k‖) := by ring
    _ ≤ 2^101*(sourceDerivativeIntegralBound 0*‖p‖+
      2^102*(∑ j∈Finset.range 103,sourceDerivativeIntegralBound j)*‖p‖) :=
      mul_le_mul_of_nonneg_left (add_le_add zero high) (by positivity)
    _ = _ := by rw [sourceRapidBound]; ring

end LowEnergy.PreparationVacuumWeylDecay
