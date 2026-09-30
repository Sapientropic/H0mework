import H0mework.Versions.X.NavierStokes.HigherTreeSextic.Kernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticCollapse
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedSexticKernel NativeUnheatedQuinticFiveRows NativeUnheatedTriadKernel
noncomputable section
variable {nu : Viscosity}

theorem split_rate (old : NativeUnheatedQuinticLeaf.Nodes) (leaf : Fin 4) (p q : Coordinate) (inside : IntegerWavevector) :
    NativeUnheatedQuarticTime.sumRate nu (old 0) (old 1) (old 2) (old 3) ≤
      2*NativeUnheatedQuinticTime.sumRate nu (NativeUnheatedQuinticLeaf.slots old leaf p q inside 0)
        (NativeUnheatedQuinticLeaf.slots old leaf p q inside 1) (NativeUnheatedQuinticLeaf.slots old leaf p q inside 2)
        (NativeUnheatedQuinticLeaf.slots old leaf p q inside 3) (NativeUnheatedQuinticLeaf.slots old leaf p q inside 4) := by
  have sum : integerWaveViscousMultiplier (old 0).1+integerWaveViscousMultiplier (old 1).1+
      integerWaveViscousMultiplier (old 2).1+integerWaveViscousMultiplier (old 3).1 =
      integerWaveViscousMultiplier (old leaf).1 +
        (integerWaveViscousMultiplier (old (leaf.succAbove 0)).1+integerWaveViscousMultiplier (old (leaf.succAbove 1)).1+
          integerWaveViscousMultiplier (old (leaf.succAbove 2)).1) := by
    have actual := Fin.sum_univ_succAbove (fun position : Fin 4 => integerWaveViscousMultiplier (old position).1) leaf
    rw [Fin.sum_univ_four (fun position : Fin 4 => integerWaveViscousMultiplier (old position).1), Fin.sum_univ_three] at actual
    exact actual
  have paid := output_multiplier inside ((old leaf).1-inside)
  rw [add_sub_cancel] at paid
  have total := mul_le_mul_of_nonneg_left paid nu.coeff_pos.le
  rw [NativeUnheatedQuarticTime.sumRate, sum]
  change nu.coeff*(_+(_+_+_)) ≤ 2*(nu.coeff*(integerWaveViscousMultiplier inside+
    integerWaveViscousMultiplier ((old leaf).1-inside)+integerWaveViscousMultiplier (old (leaf.succAbove 0)).1+
    integerWaveViscousMultiplier (old (leaf.succAbove 1)).1+integerWaveViscousMultiplier (old (leaf.succAbove 2)).1))
  nlinarith [nu.coeff_pos, multiplier_nonnegative (old (leaf.succAbove 0)).1,
    multiplier_nonnegative (old (leaf.succAbove 1)).1, multiplier_nonnegative (old (leaf.succAbove 2)).1]

theorem rate_parent (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) :
    rates nu slot leaf wave i j outside l m p q index 2 ≤ 2*rates nu slot leaf wave i j outside l m p q index 3 :=
  split_rate (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index.1) leaf p q index.2

theorem collapsed_power (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) :
    ‖NativeUnheatedSexticInput.kernel nu slot leaf position wave i j response outside l m p q index‖^4 ≤
      8*nu.coeff⁻¹^7*(rates nu slot leaf wave i j outside l m p q index 0)⁻¹^2*
        (rates nu slot leaf wave i j outside l m p q index 1)⁻¹^2*
        (rates nu slot leaf wave i j outside l m p q index 2)⁻¹^5 := by
  have paid := hierarchical_power (nu := nu) slot leaf position wave i j response outside l m p q index
  by_cases zero : rates nu slot leaf wave i j outside l m p q index 2 = 0
  · simpa only [zero, inv_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (5 : ℕ) ≠ 0), mul_zero, zero_mul] using paid
  · have positive : 0 < rates nu slot leaf wave i j outside l m p q index 2 :=
      lt_of_le_of_ne (rate_nonnegative slot leaf wave i j outside l m p q index 2) (Ne.symm zero)
    have vBound : (rates nu slot leaf wave i j outside l m p q index 3)⁻¹ ≤
        2*(rates nu slot leaf wave i j outside l m p q index 2)⁻¹ := by
      have original := one_div_le_one_div_of_le (half_pos positive)
        (show rates nu slot leaf wave i j outside l m p q index 2/2 ≤ rates nu slot leaf wave i j outside l m p q index 3 by
          linarith [rate_parent (nu := nu) slot leaf wave i j outside l m p q index])
      simpa only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul] using original
    apply paid.trans
    calc
      _ ≤ nu.coeff⁻¹^7*(rates nu slot leaf wave i j outside l m p q index 0)⁻¹^2*
          (rates nu slot leaf wave i j outside l m p q index 1)⁻¹^2*
          (rates nu slot leaf wave i j outside l m p q index 2)⁻¹^2*
          (2*(rates nu slot leaf wave i j outside l m p q index 2)⁻¹)^3 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (inv_nonneg.mpr (rate_nonnegative slot leaf wave i j outside l m p q index 3)) vBound 3) (by positivity [nu.coeff_pos])
      _ = _ := by ring

def bound (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector)
    (i j outside l m : Coordinate) (index : NativeUnheatedQuarticAllSlots.Index) : ℝ :=
  (8*nu.coeff⁻¹^7*(NativeUnheatedQuinticKernel.pairRate nu wave index)⁻¹^2*
    (NativeUnheatedQuinticKernel.parentRate nu wave index)⁻¹^2*
    (NativeUnheatedQuarticPrimitiveKernel.rate nu slot wave i j outside l m index)⁻¹^5)^(1/4 : ℝ)

theorem bound_nonnegative (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector)
    (i j outside l m : Coordinate) (index : NativeUnheatedQuarticAllSlots.Index) :
    0 ≤ bound nu slot wave i j outside l m index := Real.rpow_nonneg (by
      positivity [nu.coeff_pos, NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu slot wave i j outside l m index]) _

theorem kernel_bound (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) :
    ‖NativeUnheatedSexticInput.kernel nu slot leaf position wave i j response outside l m p q index‖ ≤
      bound nu slot wave i j outside l m index.1 := by
  have paid := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) 4)
    (collapsed_power (nu := nu) slot leaf position wave i j response outside l m p q index) (by norm_num : (0 : ℝ) ≤ 1/4)
  rw [← Real.rpow_natCast_mul (norm_nonneg _)] at paid
  norm_num only [Nat.cast_ofNat, mul_one_div_cancel, Real.rpow_one] at paid
  exact paid

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion

def remaining (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (_position : Fin 5)
    (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : NativeUnheatedQuarticAllSlots.Index)  : ℂ :=
  ∏ number : Fin 3, inputs number.succ.succ
    (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove number)).1
    (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove number)).2

theorem term_grouped (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate)
    (index : NativeUnheatedQuarticAllSlots.Index) (inside : IntegerWavevector)  :
    NativeUnheatedSexticInput.multilinearTerm inputs nu slot leaf position wave i j response outside l m p q (index,inside) =
      NativeUnheatedSexticInput.kernel nu slot leaf position wave i j response outside l m p q (index,inside)*
        (inputs 0 inside p*
          inputs 1
            ((NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index leaf).1-inside) q)*
        remaining inputs slot leaf position wave i j outside l m index := by
  rw [NativeUnheatedSexticInput.multilinearTerm, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_three, remaining, Fin.prod_univ_three]
  change NativeUnheatedSexticInput.kernel nu slot leaf position wave i j response outside l m p q (index,inside)*
    (inputs 0 inside p*
      (inputs 1
        ((NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index leaf).1-inside) q*
        (inputs 2
          (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove 0)).1
          (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove 0)).2*
        inputs 3
          (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove 1)).1
          (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove 1)).2*
        inputs 4
          (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove 2)).1
          (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index (leaf.succAbove 2)).2))) = _
  simp only [show (0 : Fin 3).succ.succ = (2 : Fin 5) by rfl,
    show (1 : Fin 3).succ.succ = (3 : Fin 5) by rfl, show (2 : Fin 3).succ.succ = (4 : Fin 5) by rfl]
  ring

theorem fiber_point (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate)
    (index : NativeUnheatedQuarticAllSlots.Index) (inside : IntegerWavevector)  :
    ‖NativeUnheatedSexticInput.multilinearTerm inputs nu slot leaf position wave i j response outside l m p q (index,inside)‖ ≤
      bound nu slot wave i j outside l m index*
        ‖inputs 0 inside p*inputs 1
          ((NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index leaf).1-inside) q‖*
        ‖remaining inputs slot leaf position wave i j outside l m index‖ := by
  rw [term_grouped, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (kernel_bound slot leaf position wave i j response outside l m p q (index,inside)) (norm_nonneg _)) (norm_nonneg _)

theorem fiber_summable (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate)
    (index : NativeUnheatedQuarticAllSlots.Index)  :
    Summable (fun inside => ‖NativeUnheatedSexticInput.multilinearTerm inputs nu slot leaf position wave i j response outside l m p q (index,inside)‖) :=
  ((((NativeHigherTimeJets.mixed_pair_summable (inputs 0)
    (inputs 1) (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index leaf).1 q p).norm).mul_left
      (bound nu slot wave i j outside l m index)).mul_right (‖remaining inputs slot leaf position wave i j outside l m index‖)).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun inside => fiber_point inputs slot leaf position wave i j response outside l m p q index inside)

theorem fiber_bound (inputs : Fin 5 → NativeUnheatedTriadSum.E) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (wave : IntegerWavevector) (i j response outside l m p q : Coordinate)
    (index : NativeUnheatedQuarticAllSlots.Index)  :
    (∑' inside, ‖NativeUnheatedSexticInput.multilinearTerm inputs nu slot leaf position wave i j response outside l m p q (index,inside)‖) ≤
      bound nu slot wave i j outside l m index*(3*‖inputs 0‖*
        ‖inputs 1‖)*‖remaining inputs slot leaf position wave i j outside l m index‖ := by
  have pairs := (NativeHigherTimeJets.mixed_pair_summable (inputs 0)
    (inputs 1) (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index leaf).1 q p).norm
  have paid := (fiber_summable inputs slot leaf position wave i j response outside l m p q index).tsum_le_tsum
    (fun inside => fiber_point inputs slot leaf position wave i j response outside l m p q index inside)
    ((pairs.mul_left (bound nu slot wave i j outside l m index)).mul_right ‖remaining inputs slot leaf position wave i j outside l m index‖)
  rw [tsum_mul_right, tsum_mul_left] at paid
  exact paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (NativeUnheatedPairInverseFlux.absolute_pair_bound (inputs 0)
      (inputs 1) (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index leaf).1 q p)
    (bound_nonnegative nu slot wave i j outside l m index)) (norm_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticCollapse
