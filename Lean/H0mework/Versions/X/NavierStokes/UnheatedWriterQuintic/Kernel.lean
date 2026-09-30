import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Power
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.PrimitiveKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedQuarticTime NativeUnheatedQuarticAllSlots NativeUnheatedTriadKernel NativeUnheatedTriadChannels
open NativeUnheatedTriadDepthKernel NativeUnheatedStressPairEvolution NativeUnheatedPairNegativeKernel
open NativeUnheatedHalfNonlinear NativeUnheatedQuinticWeights NativeUnheatedQuinticPower NativeCompleteStressCarrier
open NativeUnheatedQuarticPrimitiveKernel (rate rate_nonnegative)
noncomputable section
variable {nu : Viscosity}

def parents (wave : IntegerWavevector) (index : Index) : Fin 3 → IntegerWavevector :=
  ![index.1.2, wave-index.1.1-index.1.2, index.1.1]

def spectators (slot : Fin 3) (wave : IntegerWavevector) (index : Index) : Fin 2 → IntegerWavevector :=
  ![![parents wave index 1, parents wave index 2], ![parents wave index 0, parents wave index 2],
    ![parents wave index 0, parents wave index 1]] slot

def parentRate (nu : Viscosity) (wave : IntegerWavevector) (index : Index) : ℝ :=
  triadDecay nu (parents wave index 0) (parents wave index 1) (parents wave index 2)

def pairRate (nu : Viscosity) (wave : IntegerWavevector) (index : Index) : ℝ :=
  decay nu (parents wave index 0+parents wave index 1) (parents wave index 2)

theorem quarter_fourth (wave : IntegerWavevector) : quarter wave^4 = integerWaveViscousMultiplier wave := by
  rw [show (4 : ℕ) = 2*2 by decide, pow_mul, quarter_sq, root_sq]

theorem leaf_multiplier (inputs : Fin 4 → Slot) (leaf : Fin 4) :
    integerWaveViscousMultiplier (inputs leaf).1 ≤
      nu.coeff⁻¹*sumRate nu (inputs 0) (inputs 1) (inputs 2) (inputs 3) := by
  have paid := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (fun e _ => multiplier_nonnegative (inputs e).1) (Finset.mem_univ leaf)
  have same : nu.coeff⁻¹*sumRate nu (inputs 0) (inputs 1) (inputs 2) (inputs 3) =
      ∑ e : Fin 4, integerWaveViscousMultiplier (inputs e).1 := by
    rw [sumRate, ← mul_assoc, inv_mul_cancel₀ nu.coeff_pos.ne', one_mul, Fin.sum_univ_four]
  exact paid.trans_eq same.symm

theorem quarter_paid (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) (leaf : Fin 4) :
    quarter (slots slot wave i j outside l m index leaf).1^4*(rate nu slot wave i j outside l m index)⁻¹ ≤ nu.coeff⁻¹ := by
  rw [quarter_fourth]
  exact paid_inverse (rate_nonnegative nu slot wave i j outside l m index) (inv_nonneg.mpr nu.coeff_pos.le)
    (leaf_multiplier (slots slot wave i j outside l m index) leaf)

theorem triad_multiplier (a b c : IntegerWavevector) (index : Fin 3) :
    integerWaveViscousMultiplier (![a,b,c] index) ≤ nu.coeff⁻¹*triadDecay nu a b c := by
  have paid := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun e _ => multiplier_nonnegative (![a,b,c] e)) (Finset.mem_univ index)
  have same : nu.coeff⁻¹*triadDecay nu a b c = ∑ e : Fin 3, integerWaveViscousMultiplier (![a,b,c] e) := by
    rw [triadDecay, ← mul_assoc, inv_mul_cancel₀ nu.coeff_pos.ne', one_mul, Fin.sum_univ_three]
    rfl
  exact paid.trans_eq same.symm

theorem parent_bound (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    parentRate nu wave index ≤ 2*rate nu slot wave i j outside l m index := by
  let a := parents wave index 0
  let b := parents wave index 1
  let c := parents wave index 2
  let d := index.2
  fin_cases slot
  · have same : d+(a-d) = a := by abel
    have paid := NativeUnheatedQuarticKernel.parent_triad_bound (nu := nu) (d,l) (a-d,m) (b,j) (c,outside)
    simpa only [same] using! paid
  · have same : d+(b-d) = b := by abel
    have paid := NativeUnheatedQuarticKernel.parent_triad_bound (nu := nu) (d,l) (b-d,m) (a,i) (c,outside)
    rw [same] at paid
    convert! paid using 1
    unfold parentRate triadDecay
    dsimp only [a,b,c,parents]
    ring
  · have same : d+(c-d) = c := by abel
    have paid := NativeUnheatedQuarticKernel.parent_triad_bound (nu := nu) (d,l) (c-d,m) (a,i) (b,j)
    rw [same] at paid
    convert! paid using 1
    · unfold parentRate triadDecay
      dsimp only [a,b,c,parents]
      ring
    · change 2*sumRate nu (a,i) (b,j) (d,l) (c-d,m) = _
      unfold sumRate
      ring

theorem inverse_parent (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index)
    (nonzero : parentRate nu wave index ≠ 0) :
    (rate nu slot wave i j outside l m index)⁻¹ ≤ 2*(parentRate nu wave index)⁻¹ := by
  have positive : 0 < parentRate nu wave index := lt_of_le_of_ne (triad_nonnegative (nu := nu) (parents wave index 0) (parents wave index 1) (parents wave index 2)) (Ne.symm nonzero)
  have lower := parent_bound (nu := nu) slot wave i j outside l m index
  have paid := one_div_le_one_div_of_le (div_pos positive (by norm_num : (0 : ℝ) < 2))
    (show parentRate nu wave index/2 ≤ rate nu slot wave i j outside l m index by linarith)
  simpa only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul] using paid

theorem pressure_square (wave : IntegerWavevector) (i j response : Coordinate) :
    ‖pressure wave i j response‖^2 ≤ integerWaveViscousMultiplier wave :=
  (pow_le_pow_left₀ (norm_nonneg _) (pressure_bound wave i j response) 2).trans_eq (Real.sq_sqrt (multiplier_nonnegative _))

theorem inner_paid (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m response : Coordinate) (index : Index) :
    ‖pressure (parents wave index slot) l m response‖^2*(rate nu slot wave i j outside l m index)⁻¹ ≤ 2*nu.coeff⁻¹ := by
  apply paid_inverse (rate_nonnegative nu slot wave i j outside l m index) (by positivity [nu.coeff_pos])
  have first := (pressure_square (parents wave index slot) l m response).trans
    (triad_multiplier (nu := nu) (parents wave index 0) (parents wave index 1) (parents wave index 2) slot)
  have second := mul_le_mul_of_nonneg_left (parent_bound (nu := nu) slot wave i j outside l m index) (inv_nonneg.mpr nu.coeff_pos.le)
  exact first.trans (second.trans_eq (by ring))

theorem outer_paid (wave : IntegerWavevector) (i j response : Coordinate) (index : Index) :
    ‖pressure (parents wave index 0+parents wave index 1) i j response‖^2*(pairRate nu wave index)⁻¹ ≤ nu.coeff⁻¹ := by
  apply paid_inverse (mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative _) (multiplier_nonnegative _))) (inv_nonneg.mpr nu.coeff_pos.le)
  have same : nu.coeff⁻¹*pairRate nu wave index =
      integerWaveViscousMultiplier (parents wave index 0+parents wave index 1)+integerWaveViscousMultiplier (parents wave index 2) := by
    rw [pairRate, decay, ← mul_assoc, inv_mul_cancel₀ nu.coeff_pos.ne', one_mul]
  change ‖pressure (parents wave index 0+parents wave index 1) i j response‖^2 ≤ nu.coeff⁻¹*pairRate nu wave index
  rw [same]
  exact (pressure_square _ i j response).trans (le_add_of_nonneg_right (multiplier_nonnegative _))

theorem pair_paid (wave : IntegerWavevector) (i j response l m outside : Coordinate) (index : Index) :
    ‖pressure (parents wave index 0+parents wave index 1) i j response‖*
      ‖pressure (parents wave index 2) l m outside‖*(pairRate nu wave index)⁻¹ ≤ nu.coeff⁻¹ := by
  have bounded := mul_le_mul (pressure_bound (parents wave index 0+parents wave index 1) i j response)
    (pressure_bound (parents wave index 2) l m outside) (norm_nonneg _) (Real.sqrt_nonneg _)
  have d0 : 0 ≤ pairRate nu wave index := mul_nonneg nu.coeff_pos.le
    (add_nonneg (multiplier_nonnegative _) (multiplier_nonnegative _))
  have paid := mul_le_mul_of_nonneg_right bounded (inv_nonneg.mpr d0)
  have original := NativeUnheatedPairNegativeKernel.kernel_bound (nu := nu)
    (parents wave index 0+parents wave index 1) (parents wave index 2)
  have weak : (2*nu.coeff)⁻¹ ≤ nu.coeff⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le nu.coeff_pos (by linarith [nu.coeff_pos] : nu.coeff ≤ 2*nu.coeff)
  exact (paid.trans original).trans weak

theorem tree_original (slot : Fin 3) (wave : IntegerWavevector) (i j response outside l m : Coordinate) (index : Index) :
    tree nu slot wave i j response outside l m index =
      NativeUnheatedTriadChannelWrite.normalizer nu (parents wave index 0) (parents wave index 1) (parents wave index 2) i j response *
        pressure (parents wave index slot) l m (![i,j,outside] slot) := by
  fin_cases slot <;> rfl

def kernel (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector) (i j response outside l m : Coordinate) (index : Index) (leaf : Fin 4) : ℂ :=
  ((rate nu slot wave i j outside l m index)⁻¹ • tree nu slot wave i j response outside l m index)*
    (quarter (slots slot wave i j outside l m index leaf).1 : ℂ)

theorem kernel_norm (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector) (i j response outside l m : Coordinate) (index : Index) (leaf : Fin 4) :
    ‖kernel nu slot wave i j response outside l m index leaf‖ =
      (rate nu slot wave i j outside l m index)⁻¹*(pairRate nu wave index)⁻¹*(parentRate nu wave index)⁻¹*
        ‖pressure (parents wave index 0+parents wave index 1) i j response‖*
        ‖pressure (parents wave index slot) l m (![i,j,outside] slot)‖*
        quarter (slots slot wave i j outside l m index leaf).1 := by
  have d0 : 0 ≤ pairRate nu wave index := mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative _) (multiplier_nonnegative _))
  have t0 : 0 ≤ parentRate nu wave index := triad_nonnegative (nu := nu) _ _ _
  rw [kernel, norm_mul, norm_smul, tree_original]
  simp only [NativeUnheatedTriadChannelWrite.normalizer, norm_mul, norm_smul]
  change ‖(rate nu slot wave i j outside l m index)⁻¹‖*
    (‖(pairRate nu wave index)⁻¹‖*‖(parentRate nu wave index)⁻¹‖*
      ‖pressure (parents wave index 0+parents wave index 1) i j response‖*
      ‖pressure (parents wave index slot) l m (![i,j,outside] slot)‖)*
      ‖(quarter (slots slot wave i j outside l m index leaf).1 : ℂ)‖ = _
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative nu slot wave i j outside l m index)),
    Real.norm_of_nonneg (inv_nonneg.mpr d0), Real.norm_of_nonneg (inv_nonneg.mpr t0), Complex.norm_real,
    Real.norm_of_nonneg (quarter_nonnegative _)]
  ring

theorem spectator_inverse (slot : Fin 3) (wave : IntegerWavevector) (index : Index) (which : Fin 2) :
    (parentRate nu wave index)⁻¹ ≤ (floor nu)⁻¹*weight (spectators slot wave index which) := by
  fin_cases slot <;> fin_cases which
  · exact triad_inverse_internal (parents wave index 0) (parents wave index 1) (parents wave index 2) 1
  · exact triad_inverse_internal (parents wave index 0) (parents wave index 1) (parents wave index 2) 2
  · exact triad_inverse_internal (parents wave index 0) (parents wave index 1) (parents wave index 2) 0
  · exact triad_inverse_internal (parents wave index 0) (parents wave index 1) (parents wave index 2) 2
  · exact triad_inverse_internal (parents wave index 0) (parents wave index 1) (parents wave index 2) 0
  · exact triad_inverse_internal (parents wave index 0) (parents wave index 1) (parents wave index 2) 1

theorem spectator_pair_inverse (slot : Fin 3) (notLast : slot ≠ 2) (wave : IntegerWavevector) (index : Index) :
    (pairRate nu wave index)⁻¹ ≤ (floor nu)⁻¹*weight (spectators slot wave index 1) := by
  fin_cases slot
  · exact inverse_internal_bound (parents wave index 0+parents wave index 1) (parents wave index 2)
  · exact inverse_internal_bound (parents wave index 0+parents wave index 1) (parents wave index 2)
  · exact False.elim (notLast rfl)

theorem kernel_zero_parent (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (leaf : Fin 4) (zero : parentRate nu wave index = 0) :
    kernel nu slot wave i j response outside l m index leaf = 0 := by
  have sumZero : integerWaveViscousMultiplier (parents wave index 0)+integerWaveViscousMultiplier (parents wave index 1)+
      integerWaveViscousMultiplier (parents wave index 2) = 0 := (mul_eq_zero.mp zero).resolve_left nu.coeff_pos.ne'
  have square := pressure_square (parents wave index 0+parents wave index 1) i j response
  have paired := NativeUnheatedTriadKernel.output_multiplier (parents wave index 0) (parents wave index 1)
  have pressureZero : pressure (parents wave index 0+parents wave index 1) i j response = 0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    apply le_antisymm _ (sq_nonneg _)
    linarith [multiplier_nonnegative (parents wave index 2)]
  simp only [kernel, tree_original, NativeUnheatedTriadChannelWrite.normalizer, pressureZero, smul_zero, zero_mul]

theorem kernel_zero_pair (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (leaf : Fin 4) (zero : pairRate nu wave index = 0) :
    kernel nu slot wave i j response outside l m index leaf = 0 := by
  have sumZero : integerWaveViscousMultiplier (parents wave index 0+parents wave index 1)+
      integerWaveViscousMultiplier (parents wave index 2) = 0 := (mul_eq_zero.mp zero).resolve_left nu.coeff_pos.ne'
  have square := pressure_square (parents wave index 0+parents wave index 1) i j response
  have pressureZero : pressure (parents wave index 0+parents wave index 1) i j response = 0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    apply le_antisymm _ (sq_nonneg _)
    linarith [multiplier_nonnegative (parents wave index 2)]
  simp only [kernel, tree_original, NativeUnheatedTriadChannelWrite.normalizer, pressureZero, smul_zero, zero_mul]

theorem kernel_bound (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (leaf : Fin 4) :
    ‖kernel nu slot wave i j response outside l m index leaf‖ ≤
      NativeUnheatedQuinticWeights.cap nu*eta (spectators slot wave index 0)*eta (spectators slot wave index 1) := by
  by_cases pairZero : pairRate nu wave index = 0
  · rw [kernel_zero_pair nu slot wave i j response outside l m index leaf pairZero, norm_zero]
    exact mul_nonneg (mul_nonneg (NativeUnheatedQuinticWeights.cap_nonnegative nu)
      (eta_nonnegative (spectators slot wave index 0))) (eta_nonnegative (spectators slot wave index 1))
  by_cases zero : parentRate nu wave index = 0
  · rw [kernel_zero_parent nu slot wave i j response outside l m index leaf zero, norm_zero]
    exact mul_nonneg (mul_nonneg (NativeUnheatedQuinticWeights.cap_nonnegative nu)
      (eta_nonnegative (spectators slot wave index 0))) (eta_nonnegative (spectators slot wave index 1))
  · apply from_eighth
    rw [kernel_norm]
    have d0 : 0 ≤ (pairRate nu wave index)⁻¹ := inv_nonneg.mpr
      (mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative _) (multiplier_nonnegative _)))
    have t0 : 0 ≤ (parentRate nu wave index)⁻¹ := inv_nonneg.mpr (triad_nonnegative (nu := nu) _ _ _)
    have s0 := inv_nonneg.mpr (rate_nonnegative nu slot wave i j outside l m index)
    have v0 := inv_nonneg.mpr (floor_positive nu).le
    have x0 := (weight_pos (spectators slot wave index 0)).le
    have qPaid := quarter_paid (nu := nu) slot wave i j outside l m index leaf
    have sPaid := inverse_parent (nu := nu) slot wave i j outside l m index zero
    have left := spectator_inverse (nu := nu) slot wave index 0
    have right := spectator_inverse (nu := nu) slot wave index 1
    by_cases last : slot = 2
    · subst slot
      exact outer_power (norm_nonneg _) (norm_nonneg _) d0 t0 s0 v0 x0
        (pair_paid (nu := nu) wave i j response l m outside index) qPaid sPaid left right
    · exact inner_power d0 t0 s0 v0 x0 (outer_paid (nu := nu) wave i j response index)
        (inner_paid (nu := nu) slot wave i j outside l m (![i,j,outside] slot) index) qPaid sPaid
        (spectator_pair_inverse (nu := nu) slot last wave index) left right

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticKernel
