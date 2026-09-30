import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Mixed.Series

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeMixedHeatSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open NativeFullOrderAction NativeFullOrderSynthesis NativeWindowSpacetimeFourier
open NativeWindowTailMoments NativeMixedHeatLimit
noncomputable section
variable {nu : Viscosity}

theorem scalarMode_bound_at (coefficient : ℕ → IntegerWavevector → ℝ → ℂ)
    (evolves : ∀ n wave time, HasDerivAt (coefficient n wave) (coefficient (n + 1) wave time) time)
    (bound : ℕ → ℕ → ℝ) (pair : Spacetime)
    (bounded : ∀ rank order wave, frequencySize wave ^ order * ‖coefficient rank wave pair.1‖  ≤
      bound rank order * decay wave) (order : ℕ) (wave : IntegerWavevector) :
    ‖iteratedFDeriv ℝ order (scalarMode coefficient wave) pair‖  ≤  modeBudget bound order * decay wave := by
  apply (norm_iteratedFDeriv_mul_le (timeCoefficient_smooth coefficient evolves wave)
    (spaceMonomial_smooth wave) pair (n := order)
    (by exact_mod_cast (le_top : (order : ℕ∞)  ≤  ⊤))).trans
  rw [modeBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro rank _
  have timeBound := timeCoefficient_bound coefficient evolves wave rank pair
  have spaceBound := spaceMonomial_bound wave (order - rank) pair
  calc
    _  ≤  (order.choose rank : ℝ) * (2 * Real.pi) ^ (order - rank) *
        (frequencySize wave ^ (order - rank) * ‖coefficient rank wave pair.1‖) := by
      have scaled := mul_le_mul_of_nonneg_left
        (mul_le_mul timeBound spaceBound (norm_nonneg _) (norm_nonneg _)) (Nat.cast_nonneg (order.choose rank))
      convert! scaled using 1
      · ring
      · rw [mul_pow]
        ring
    _  ≤  _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bounded rank (order - rank) wave)
        (mul_nonneg (Nat.cast_nonneg (order.choose rank)) (pow_nonneg (by positivity : 0  ≤  2 * Real.pi) _))


def heatFactor (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector) : ℝ :=
  finiteStateVorticityHeatMultiplier nu.coeff lag wave

theorem heatFactor_low (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector) : 0  ≤  heatFactor nu lag wave :=
  finiteStateVorticityHeatMultiplier_nonneg _ _ _

theorem heatFactor_high (nu : Viscosity) (lag : ℝ≥0) (wave : IntegerWavevector) : heatFactor nu lag wave  ≤  1 :=
  finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave

theorem heatFactor_tendsto (nu : Viscosity) (wave : IntegerWavevector) :
    Tendsto (fun lag : ℝ≥0 => heatFactor nu lag wave) (𝓝 0) (𝓝 1) := by
  simpa only [heatFactor,finiteStateVorticityHeatMultiplier,NNReal.coe_zero,mul_zero,neg_zero,Real.exp_zero] using
    (NativeZeroHeat.multiplier_continuous nu wave).tendsto 0

theorem scalar_heat_uniform (nu : Viscosity) (coefficient : ℕ → IntegerWavevector → ℝ → ℂ)
    (evolves : ∀ n wave time, HasDerivAt (coefficient n wave) (coefficient (n + 1) wave time) time)
    (left right : ℝ) (bound : ℕ → ℕ → ℝ) (nonnegative : ∀ rank order, 0  ≤  bound rank order)
    (bounded : ∀ time  ∈  Icc left right, ∀ rank order wave,
      frequencySize wave ^ order * ‖coefficient rank wave time‖  ≤  bound rank order * decay wave)
    (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n
      (fun pair : Spacetime => ∑' wave, heatFactor nu lag wave • scalarMode coefficient wave pair))
      (iteratedFDeriv ℝ n (scalarField coefficient)) (𝓝 0) (Ioo left right ×ˢ univ) := by
  apply multiplier_jets_uniform (scalarMode coefficient) (scalarMode_smooth coefficient evolves)
    (isOpen_Ioo.prod isOpen_univ) ((convex_Ioo _ _).prod convex_univ)
    (fun n wave => modeBudget bound n * decay wave) (fun n => decay_summable.mul_left _)
  · intro order wave
    apply mul_nonneg _ (sq_nonneg _)
    apply Finset.sum_nonneg
    intro rank _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (nonnegative rank (order-rank))
  · intro order wave pair inside
    exact scalarMode_bound_at coefficient evolves bound pair
      (bounded pair.1 ⟨inside.1.1.le,inside.1.2.le⟩) order wave
  · exact heatFactor_low nu
  · exact heatFactor_high nu
  · exact heatFactor_tendsto nu

theorem velocity_series (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (coordinate : Coordinate) :
    scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag coordinate) =
      fun pair : Spacetime => ∑' wave, heatFactor nu lag wave •
        scalarMode (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate) wave pair := by
  funext pair
  apply tsum_congr
  intro wave
  change NativeWindowSpacetimeVelocity.coefficient seed lag coordinate 0 wave pair.1 * monomial wave pair.2 =
    heatFactor nu lag wave • (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate 0 wave pair.1 * monomial wave pair.2)
  simp only [NativeWindowSpacetimeVelocity.coefficient,NativeWindowHeatEvolution.velocityJet,NativeZeroHeatWindow.jet_zero]
  change NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedHeatAction.heatCLM nu lag
    (NativeForwardWindowJets.jet seed 0 pair.1).fst) wave coordinate * monomial wave pair.2 = _
  rw [NativeCompleteHeatTransport.velocity_heat,Pi.smul_apply,smul_mul_assoc]
  rfl

theorem stress_series (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (entry : Coordinate × Coordinate) :
    scalarField (NativeWindowSpacetimeStress.coefficient seed lag entry) =
      fun pair : Spacetime => ∑' wave, heatFactor nu lag wave •
        scalarMode (NativeWindowSpacetimeStress.coefficient seed 0 entry) wave pair := by
  funext pair
  apply tsum_congr
  intro wave
  change NativeWindowSpacetimeStress.coefficient seed lag entry 0 wave pair.1 * monomial wave pair.2 =
    heatFactor nu lag wave • (NativeWindowSpacetimeStress.coefficient seed 0 entry 0 wave pair.1 * monomial wave pair.2)
  simp only [NativeWindowSpacetimeStress.coefficient,NativeZeroHeatWindow.jet_zero]
  change NativeCompleteStressCarrier.read (NativeCompleteHeatTransport.tensorHeat nu lag
    (NativeForwardWindowJets.jet seed 0 pair.1).snd) wave entry.1 entry.2 * monomial wave pair.2 = _
  rw [NativeCompleteHeatTransport.tensorHeat_read,Pi.smul_apply,Pi.smul_apply,smul_mul_assoc]
  rfl

theorem velocity_scalar_jets (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (coordinate : Coordinate) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n
      (scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag coordinate)))
      (iteratedFDeriv ℝ n (scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate)))
      (𝓝 0) (Ioo (NativeAbsoluteEventualControl.startTime seed-1) horizon ×ˢ univ) := by
  have generated := scalar_heat_uniform nu (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate)
    (NativeWindowSpacetimeVelocity.coefficient_hasDerivAt seed 0 coordinate)
    (NativeAbsoluteEventualControl.startTime seed-1) horizon
    (fun rank order => velocityBudget seed horizon rank (order+4))
    (fun rank order => mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (Real.sqrt_nonneg _))
    (fun time inside rank order wave => by
      simpa only [NativeWindowSpacetimeVelocity.coefficient,NativeWindowHeatEvolution.velocityJet,
        NativeZeroHeatWindow.jet_zero] using window_velocity_decay seed horizon time inside rank order wave coordinate) n
  simpa only [← velocity_series seed] using generated

theorem stress_scalar_jets (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (entry : Coordinate × Coordinate) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n
      (scalarField (NativeWindowSpacetimeStress.coefficient seed lag entry)))
      (iteratedFDeriv ℝ n (scalarField (NativeWindowSpacetimeStress.coefficient seed 0 entry)))
      (𝓝 0) (Ioo (NativeAbsoluteEventualControl.startTime seed-1) horizon ×ˢ univ) := by
  have generated := scalar_heat_uniform nu (NativeWindowSpacetimeStress.coefficient seed 0 entry)
    (NativeWindowSpacetimeStress.coefficient_hasDerivAt seed 0 entry)
    (NativeAbsoluteEventualControl.startTime seed-1) horizon
    (fun rank order => stressBudget seed horizon rank (order+4))
    (fun rank order => mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (Real.sqrt_nonneg _))
    (fun time inside rank order wave => by
      simpa only [NativeWindowSpacetimeStress.coefficient,NativeZeroHeatWindow.jet_zero] using
        window_stress_decay seed horizon time inside rank order wave entry.1 entry.2) n
  simpa only [← stress_series seed] using generated

theorem jets_eqOn_of_eqOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} (opened : IsOpen s)
    {f g : E → F} (same : EqOn f g s) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n f) (iteratedFDeriv ℝ n g) s := by
  intro x inside
  have germ : f =ᶠ[𝓝 x] g := by
    filter_upwards [opened.mem_nhds inside] with y member
    exact same member
  exact (germ.iteratedFDeriv ℝ n).self_of_nhds

theorem product_sum_smul (f g : IntegerWavevector → ℂ)
    (fpaid : Summable fun i => ‖f i‖) (gpaid : Summable fun i => ‖g i‖) (lag : ℝ≥0) :
    (∑' i, heatFactor nu lag i • f i) * (∑' j, heatFactor nu lag j • g j) =
      ∑' pair : IntegerWavevector × IntegerWavevector,
        (heatFactor nu lag pair.1 * heatFactor nu lag pair.2) • (f pair.1*g pair.2) := by
  have left : Summable fun i => ‖heatFactor nu lag i • f i‖ :=
    fpaid.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by
      rw [norm_smul,Real.norm_of_nonneg (heatFactor_low nu lag i)]
      exact mul_le_of_le_one_left (norm_nonneg _) (heatFactor_high nu lag i))
  have right : Summable fun i => ‖heatFactor nu lag i • g i‖ :=
    gpaid.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by
      rw [norm_smul,Real.norm_of_nonneg (heatFactor_low nu lag i)]
      exact mul_le_of_le_one_left (norm_nonneg _) (heatFactor_high nu lag i))
  rw [tsum_mul_tsum_of_summable_norm left right]
  apply tsum_congr
  intro pair
  exact smul_mul_smul_comm _ _ _ _

theorem product_heat_uniform (nu : Viscosity) (first last : ℕ → IntegerWavevector → ℝ → ℂ)
    (evolvesFirst : ∀ n wave time, HasDerivAt (first n wave) (first (n+1) wave time) time)
    (evolvesLast : ∀ n wave time, HasDerivAt (last n wave) (last (n+1) wave time) time)
    (left right : ℝ) (bound : ℕ → ℕ → ℝ) (nonnegative : ∀ rank order, 0 ≤ bound rank order)
    (firstBound : ∀ time  ∈  Icc left right, ∀ rank order wave,
      frequencySize wave^order*‖first rank wave time‖ ≤ bound rank order*decay wave)
    (lastBound : ∀ time  ∈  Icc left right, ∀ rank order wave,
      frequencySize wave^order*‖last rank wave time‖ ≤ bound rank order*decay wave)
    (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n
      (fun x : Spacetime => (∑' k,heatFactor nu lag k • scalarMode first k x)*
        (∑' k,heatFactor nu lag k • scalarMode last k x)))
      (iteratedFDeriv ℝ n (fun x => scalarField first x*scalarField last x)) (𝓝 0)
      (Ioo left right ×ˢ univ) := by
  let modes := fun pair : IntegerWavevector × IntegerWavevector =>
    fun x : Spacetime => scalarMode first pair.1 x*scalarMode last pair.2 x
  let B := fun order => ∑ rank ∈ Finset.range (order+1),
    (order.choose rank : ℝ)*modeBudget bound rank*modeBudget bound (order-rank)
  have budget0 (order : ℕ) : 0 ≤ modeBudget bound order := by
    apply Finset.sum_nonneg
    intro rank _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (nonnegative rank (order-rank))
  have pairPaid : Summable (fun pair : IntegerWavevector × IntegerWavevector => decay pair.1*decay pair.2) :=
    summable_mul_of_summable_norm decay_summable.norm decay_summable.norm
  have b0 (n : ℕ) : 0 ≤ B n := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (budget0 i)) (budget0 (n-i))
  have modesBound (order : ℕ) (pair : IntegerWavevector × IntegerWavevector) (x : Spacetime)
      (inside : x ∈ Ioo left right ×ˢ (univ : Set PhysicalSpace)) :
      ‖iteratedFDeriv ℝ order (modes pair) x‖  ≤  B order*(decay pair.1*decay pair.2) := by
    apply (norm_iteratedFDeriv_mul_le (scalarMode_smooth first evolvesFirst pair.1)
      (scalarMode_smooth last evolvesLast pair.2) x
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).trans
    dsimp only [B]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro rank _
    have one := scalarMode_bound_at first evolvesFirst bound x
      (firstBound x.1 ⟨inside.1.1.le,inside.1.2.le⟩) rank pair.1
    have two := scalarMode_bound_at last evolvesLast bound x
      (lastBound x.1 ⟨inside.1.1.le,inside.1.2.le⟩) (order-rank) pair.2
    have estimate := mul_le_mul_of_nonneg_left (mul_le_mul one two (norm_nonneg _)
      (mul_nonneg (budget0 rank) (sq_nonneg _))) (Nat.cast_nonneg (order.choose rank))
    convert! estimate using 1 <;> ring
  have result := multiplier_jets_uniform modes
    (fun pair => (scalarMode_smooth first evolvesFirst pair.1).mul (scalarMode_smooth last evolvesLast pair.2))
    (isOpen_Ioo.prod isOpen_univ) ((convex_Ioo _ _).prod convex_univ)
    (fun order pair => B order*(decay pair.1*decay pair.2)) (fun order => pairPaid.mul_left (B order))
    (fun order pair => mul_nonneg (b0 order) (mul_nonneg (sq_nonneg _) (sq_nonneg _))) modesBound
    (fun lag pair => heatFactor nu lag pair.1*heatFactor nu lag pair.2)
    (fun lag pair => mul_nonneg (heatFactor_low nu lag pair.1) (heatFactor_low nu lag pair.2))
    (fun lag pair => by
      nlinarith [heatFactor_low nu lag pair.1,heatFactor_low nu lag pair.2,
        heatFactor_high nu lag pair.1,heatFactor_high nu lag pair.2])
    (fun pair => by simpa only [mul_one] using (heatFactor_tendsto nu pair.1).mul (heatFactor_tendsto nu pair.2)) n
  have firstPaid (x : Spacetime) (inside : x ∈ Ioo left right ×ˢ (univ : Set PhysicalSpace)) :
      Summable fun k => ‖scalarMode first k x‖ := by
    apply (decay_summable.mul_left (modeBudget bound 0)).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    simpa only [norm_iteratedFDeriv_zero] using scalarMode_bound_at first evolvesFirst bound x
      (firstBound x.1 ⟨inside.1.1.le,inside.1.2.le⟩) 0 k
  have lastPaid (x : Spacetime) (inside : x ∈ Ioo left right ×ˢ (univ : Set PhysicalSpace)) :
      Summable fun k => ‖scalarMode last k x‖ := by
    apply (decay_summable.mul_left (modeBudget bound 0)).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    simpa only [norm_iteratedFDeriv_zero] using scalarMode_bound_at last evolvesLast bound x
      (lastBound x.1 ⟨inside.1.1.le,inside.1.2.le⟩) 0 k
  apply (result.congr (Eventually.of_forall fun lag => jets_eqOn_of_eqOn (isOpen_Ioo.prod isOpen_univ)
    (fun x inside => (product_sum_smul _ _ (firstPaid x inside) (lastPaid x inside) lag).symm) n)).congr_right
  apply jets_eqOn_of_eqOn (isOpen_Ioo.prod isOpen_univ)
  intro x inside
  exact (tsum_mul_tsum_of_summable_norm (firstPaid x inside) (lastPaid x inside)).symm

end
end SaturationMonoid.NavierStokes.NativeMixedHeatSource
