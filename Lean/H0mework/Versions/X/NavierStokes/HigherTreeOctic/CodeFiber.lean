import H0mework.Versions.X.NavierStokes.HigherTreeOctic.InitialNorm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTreeTime
noncomputable section

/-- The address-free cap of one complete original Gram basis vector. -/
def basisCap (nu : Viscosity) : ℝ :=
  (2*Real.pi)⁻¹ * (2*NativeUnheatedTreeHeatTopology.factor nu)^6 *
    (NativeUnheatedTreeLocalHeat.cap nu * (2*Real.pi))

theorem basisCap_nonnegative (nu : Viscosity) : 0 ≤ basisCap nu := by
  unfold basisCap
  positivity [NativeUnheatedTreeHeatTopology.factor_positive nu, NativeUnheatedTreeLocalHeat.cap_positive nu]

/-- Coordinate-summed Fourier weight of the original velocity. -/
def velocityWeight {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) : ℝ :=
  ∑ coordinate : Coordinate, ‖NativeUnheatedTriadRows.velocity seed time wave coordinate‖

/-- Coordinate-summed Fourier weight of the original velocity together with its actual nonlinear action. -/
def sourceWeight {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) : ℝ :=
  ∑ coordinate : Coordinate, (‖NativeUnheatedTriadRows.velocity seed time wave coordinate‖ +
    ‖NativeUnheatedTriadRows.action seed time wave coordinate‖)

theorem velocityWeight_nonnegative {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) : 0 ≤ velocityWeight seed time wave :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sourceWeight_nonnegative {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) : 0 ≤ sourceWeight seed time wave :=
  Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem velocity_le_weight {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    ‖NativeUnheatedTriadRows.velocity seed time wave coordinate‖ ≤ velocityWeight seed time wave :=
  Finset.single_le_sum (f := fun c => ‖NativeUnheatedTriadRows.velocity seed time wave c‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ coordinate)

theorem velocity_le_source {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    ‖NativeUnheatedTriadRows.velocity seed time wave coordinate‖ ≤ sourceWeight seed time wave :=
  (le_add_of_nonneg_right (norm_nonneg _)).trans
    (Finset.single_le_sum (f := fun c => ‖NativeUnheatedTriadRows.velocity seed time wave c‖ +
      ‖NativeUnheatedTriadRows.action seed time wave c‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ coordinate))

theorem action_le_source {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    ‖NativeUnheatedTriadRows.action seed time wave coordinate‖ ≤ sourceWeight seed time wave :=
  (le_add_of_nonneg_left (norm_nonneg _)).trans
    (Finset.single_le_sum (f := fun c => ‖NativeUnheatedTriadRows.velocity seed time wave c‖ +
      ‖NativeUnheatedTriadRows.action seed time wave c‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ coordinate))

theorem product_weight {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (slots : Fin 7 → Slot)
    (time : ℝ) : ‖product seed slots time‖ ≤ ∏ n, velocityWeight seed time (slots n).1 := by
  unfold product
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun n _ => velocity_le_weight seed time _ _)

theorem forcing_weight {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (slots : Fin 7 → Slot)
    (time : ℝ) : ‖forcing seed slots time‖ ≤ 7 * ∏ n, sourceWeight seed time (slots n).1 := by
  unfold forcing
  refine (norm_sum_le _ _).trans ?_
  have each (number : Fin 7) :
      ‖NativeUnheatedTriadRows.action seed time (slots number).1 (slots number).2 * cofactor seed slots number time‖ ≤
        ∏ n, sourceWeight seed time (slots n).1 := by
    rw [norm_mul, cofactor, norm_prod, ← Finset.mul_prod_erase Finset.univ
      (fun n => sourceWeight seed time (slots n).1) (Finset.mem_univ number)]
    exact mul_le_mul (action_le_source seed time _ _)
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun n _ => velocity_le_source seed time _ _))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) (sourceWeight_nonnegative seed time _)
  calc _ ≤ ∑ _number : Fin 7, ∏ n, sourceWeight seed time (slots n).1 :=
        Finset.sum_le_sum fun number _ => each number
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num

/-- A finite family of seven-slot codes is paid by the Wiener sum over the frequencies it touches. -/
theorem code_sum_wiener (codes : Finset (Fin 7 → IntegerWavevector)) (weight : IntegerWavevector → ℝ)
    (nonnegative : ∀ wave, 0 ≤ weight wave) :
    ∑ f ∈ codes, ∏ n, weight (f n) ≤
      (∑ wave ∈ codes.biUnion (fun f => Finset.univ.image f), weight wave)^7 := by
  rw [Finset.sum_pow']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f member
    rw [Fintype.mem_piFinset]
    intro n
    exact Finset.mem_biUnion.mpr ⟨f, member, Finset.mem_image_of_mem f (Finset.mem_univ n)⟩
  · intro f _ _
    exact Finset.prod_nonneg fun n _ => nonnegative (f n)

variable {nu : Viscosity}
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)

theorem basis_cap (test : Test) (entry : Address) :
    ‖basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ ≤
      basisCap nu * ‖test entry.1‖ := by
  have paid := basis_upper (nu := nu) slot leaf position newest i j response outside l m p q r s u v
    selected a b test entry
  rw [oldCap_eq] at paid
  calc _ ≤ _ := paid
    _ = _ := by unfold basisCap; ring

/-- Every coefficient field paid by a code weight is paid fibre by fibre on every finite observation. -/
theorem code_fiber_bound (test : Test) (observed : Finset Address) (coefficient : Address → ℂ)
    (weight : (Fin 7 → IntegerWavevector) → ℝ) (nonnegative : ∀ f, 0 ≤ weight f)
    (paid : ∀ entry ∈ observed,
      ‖coefficient entry‖ ≤ weight (code slot leaf position newest i j outside l m p q r s u v selected b entry)) :
    ‖∑ entry ∈ observed, coefficient entry •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ ≤
      basisCap nu * ‖test‖ *
        ∑ f ∈ observed.image (code slot leaf position newest i j outside l m p q r s u v selected b), weight f := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := observed.image (code slot leaf position newest i j outside l m p q r s u v selected b))
    (g := code slot leaf position newest i j outside l m p q r s u v selected b)
    (fun entry member => Finset.mem_image_of_mem _ member)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  set family := observed.filter
    (fun entry => code slot leaf position newest i j outside l m p q r s u v selected b entry = f)
  have fiberCode {entry : Address} (member : entry ∈ family) :
      code slot leaf position newest i j outside l m p q r s u v selected b entry = f :=
    (Finset.mem_filter.mp member).2
  have insideInj : Set.InjOn (fun entry : Address => entry.2.2) family := by
    intro first firstMember last lastMember same
    exact entry_injective slot leaf position newest i j outside l m p q r s u v selected b same
      ((fiberCode firstMember).trans (fiberCode lastMember).symm)
  have outputInj : Set.InjOn (fun entry : Address => entry.1) family := by
    intro first firstMember last lastMember same
    have firstSum := code_sum slot leaf position newest i j outside l m p q r s u v selected b first
    have lastSum := code_sum slot leaf position newest i j outside l m p q r s u v selected b last
    rw [fiberCode firstMember] at firstSum
    rw [fiberCode lastMember] at lastSum
    have inside : first.2.2 = last.2.2 := by
      have joined := firstSum.symm.trans lastSum
      have sameOutput : first.1 = last.1 := same
      rw [sameOutput] at joined
      exact sub_right_injective joined
    exact entry_injective slot leaf position newest i j outside l m p q r s u v selected b inside
      ((fiberCode firstMember).trans (fiberCode lastMember).symm)
  let content : Address → NativeUnheatedOcticGramDualPulse.Pulse := fun entry =>
    coefficient entry •
      (constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry •
        NativeUnheatedOcticGramDualPulse.pulse (nu := nu)
          (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected entry)
          (rest_nonnegative slot leaf position newest i j outside l m p q r s u v selected entry)
          (other slot leaf position newest i j outside l m p q r s u v selected entry))
  have single (entry : Address) :
      coefficient entry •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry =
        lp.single 2 entry.2.2 (content entry) :=
    (lp.single_smul 2 entry.2.2 _ _).symm
  have contentBound {entry : Address} (member : entry ∈ family) :
      ‖content entry‖ ≤ weight f * basisCap nu * ‖test entry.1‖ := by
    have normEq : ‖content entry‖ = ‖coefficient entry •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ := by
      rw [single entry, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    rw [normEq, norm_smul, mul_assoc]
    have coefficientBound := paid entry (Finset.mem_filter.mp member).1
    rw [fiberCode member] at coefficientBound
    exact mul_le_mul coefficientBound
      (basis_cap slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      (norm_nonneg _) (nonnegative f)
  have pythagoras := lp_single_pythagoras family (fun entry : Address => entry.2.2) content insideInj
  have imageSum : ∑ k ∈ family.image (fun entry : Address => entry.1), ‖test k‖^2 =
      ∑ entry ∈ family, ‖test entry.1‖^2 :=
    Finset.sum_image (f := fun k => ‖test k‖^2) outputInj
  have testSum : ∑ entry ∈ family, ‖test entry.1‖^2 ≤ ‖test‖^2 := by
    rw [← imageSum]
    have summed := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) test
      (family.image fun entry : Address => entry.1)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using summed
  have scale0 : 0 ≤ weight f * basisCap nu := mul_nonneg (nonnegative f) (basisCap_nonnegative nu)
  have squares : ‖∑ entry ∈ family, coefficient entry •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖^2 ≤
      (weight f * basisCap nu * ‖test‖)^2 := by
    rw [Finset.sum_congr rfl fun entry _ => single entry, pythagoras]
    calc ∑ entry ∈ family, ‖content entry‖^2 ≤ ∑ entry ∈ family, (weight f * basisCap nu)^2 * ‖test entry.1‖^2 := by
          apply Finset.sum_le_sum
          intro entry member
          calc _ ≤ (weight f * basisCap nu * ‖test entry.1‖)^2 :=
                pow_le_pow_left₀ (norm_nonneg _) (contentBound member) 2
            _ = _ := by ring
      _ = (weight f * basisCap nu)^2 * ∑ entry ∈ family, ‖test entry.1‖^2 := by rw [Finset.mul_sum]
      _ ≤ (weight f * basisCap nu)^2 * ‖test‖^2 := mul_le_mul_of_nonneg_left testSum (sq_nonneg _)
      _ = _ := by ring
  have final := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg scale0 (norm_nonneg _)) two_ne_zero).mp squares
  calc _ ≤ weight f * basisCap nu * ‖test‖ := final
    _ = _ := by ring

/-- All slot frequencies touched by a finite observation. -/
def touched (observed : Finset Address) : Finset IntegerWavevector :=
  (observed.image (code slot leaf position newest i j outside l m p q r s u v selected b)).biUnion
    (fun f => Finset.univ.image f)

/-- The complete original Gram vector is paid at every time by the touched Wiener sum of the same velocity. -/
theorem vector_wiener_bound (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address)
    (time : ℝ) :
    ‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖ ≤
      basisCap nu * ‖test‖ *
        (∑ wave ∈ touched slot leaf position newest i j outside l m p q r s u v selected b observed,
          velocityWeight seed time wave)^7 := by
  rw [vector_source]
  refine (code_fiber_bound slot leaf position newest i j response outside l m p q r s u v selected a b test observed
    _ (fun f => ∏ n, velocityWeight seed time (f n))
    (fun f => Finset.prod_nonneg fun n _ => velocityWeight_nonnegative seed time (f n))
    (fun entry _ => product_weight seed _ time)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (code_sum_wiener _ _ (velocityWeight_nonnegative seed time))
    (mul_nonneg (basisCap_nonnegative nu) (norm_nonneg _))

/-- The actual observed forcing is paid at every time by the touched Wiener sum of the same source. -/
theorem forcingVector_wiener_bound (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) :
    ‖forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖ ≤
      basisCap nu * ‖test‖ *
        (7 * (∑ wave ∈ touched slot leaf position newest i j outside l m p q r s u v selected b observed,
          sourceWeight seed time wave)^7) := by
  unfold forcingVector
  refine (code_fiber_bound slot leaf position newest i j response outside l m p q r s u v selected a b test observed
    _ (fun f => 7 * ∏ n, sourceWeight seed time (f n))
    (fun f => mul_nonneg (by norm_num) (Finset.prod_nonneg fun n _ => sourceWeight_nonnegative seed time (f n)))
    (fun entry _ => forcing_weight seed _ time)).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (code_sum_wiener _ _ (sourceWeight_nonnegative seed time)) (by norm_num))
    (mul_nonneg (basisCap_nonnegative nu) (norm_nonneg _))

/-- The observation-uniform forcing integral is paid by the source Wiener integral. -/
theorem forcing_source_budget (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (summable : ∀ time ∈ Icc 0 horizon, Summable (sourceWeight seed time))
    (integrable : IntervalIntegrable (fun time => (∑' wave, sourceWeight seed time wave)^7) volume 0 horizon) :
    (∫ time in (0 : ℝ)..horizon,
      ‖forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test
        seed observed time‖) ≤
      basisCap nu * ‖test‖ * (7 * ∫ time in (0 : ℝ)..horizon, (∑' wave, sourceWeight seed time wave)^7) := by
  have forceIntegrable := (forcingVector_integrable (nu := nu) slot leaf position newest i j response outside
    l m p q r s u v selected a b test seed observed 0 horizon le_rfl nonnegative).norm
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on nonnegative forceIntegrable
    ((integrable.const_mul 7).const_mul (basisCap nu * ‖test‖))
  intro time inside
  refine (forcingVector_wiener_bound slot leaf position newest i j response outside l m p q r s u v selected a b
    test seed observed time).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (basisCap_nonnegative nu) (norm_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun wave _ => sourceWeight_nonnegative seed time wave)
    ((summable time inside).sum_le_tsum _ fun wave _ => sourceWeight_nonnegative seed time wave) 7

/-- On the original seed, the complete Gram vector is uniform once the same source has a Wiener integral. -/
theorem vector_source_budget (test : Test) (observed : Finset Address) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (summable : ∀ time ∈ Icc 0 horizon,
      Summable (sourceWeight RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent time))
    (integrable : IntervalIntegrable (fun time =>
      (∑' wave, sourceWeight RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent time wave)^7)
      volume 0 horizon) :
    ‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test
        RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent observed horizon‖ ≤
      initialCap * ‖test‖ + 2 * (basisCap RationalVorticityEvaluator.butterflyGainViscosity * ‖test‖ *
        (7 * ∫ time in (0 : ℝ)..horizon,
          (∑' wave, sourceWeight RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent
            time wave)^7)) := by
  have growth := vector_initial_response slot leaf position newest i j response outside l m p q r s u v
    selected a b test observed horizon nonnegative
  have budget := forcing_source_budget slot leaf position newest i j response outside l m p q r s u v selected a b
    test _ observed horizon nonnegative summable integrable
  linarith

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
