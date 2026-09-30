import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Kernel
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.Input

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedQuinticFiveRows NativeUnheatedQuinticKernel NativeUnheatedTriadKernel
open NativeUnheatedTriadChannels NativeUnheatedHalfNonlinear NativeUnheatedTriadDepthKernel
open NativeUnheatedQuinticTime NativeUnheatedQuinticWeights
noncomputable section
variable {nu : Viscosity}

def rates (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) : Fin 4 → ℝ :=
  ![pairRate nu wave index.1, parentRate nu wave index.1,
    NativeUnheatedQuarticPrimitiveKernel.rate nu slot wave i j outside l m index.1,
    NativeUnheatedQuinticPrimitiveKernel.rate nu slot leaf wave i j outside l m p q index]

theorem rate_nonnegative (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) (number : Fin 4) :
    0 ≤ rates nu slot leaf wave i j outside l m p q index number := by
  fin_cases number
  · exact mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative _) (multiplier_nonnegative _))
  · exact triad_nonnegative (nu := nu) _ _ _
  · exact NativeUnheatedQuarticPrimitiveKernel.rate_nonnegative nu slot wave i j outside l m index.1
  · exact NativeUnheatedQuinticPrimitiveKernel.rate_nonnegative nu slot leaf wave i j outside l m p q index

theorem newest_quarter (inputs : Fin 5 → Slot) (position : Fin 5) :
    quarter (inputs position).1^4*(sumRate nu (inputs 0) (inputs 1) (inputs 2) (inputs 3) (inputs 4))⁻¹ ≤ nu.coeff⁻¹ := by
  rw [quarter_fourth]
  apply paid_inverse (NativeUnheatedQuinticNormalForm.rate_nonnegative _ _ _ _ _) (inv_nonneg.mpr nu.coeff_pos.le)
  have paid := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 5)))
    (fun e _ => multiplier_nonnegative (inputs e).1) (Finset.mem_univ position)
  have same : nu.coeff⁻¹*sumRate nu (inputs 0) (inputs 1) (inputs 2) (inputs 3) (inputs 4) =
      ∑ e : Fin 5, integerWaveViscousMultiplier (inputs e).1 := by
    rw [sumRate, ← mul_assoc, inv_mul_cancel₀ nu.coeff_pos.ne', one_mul, Fin.sum_univ_succ, Fin.sum_univ_four]
    change _ = integerWaveViscousMultiplier (inputs 0).1+(integerWaveViscousMultiplier (inputs 1).1+
      integerWaveViscousMultiplier (inputs 2).1+integerWaveViscousMultiplier (inputs 3).1+integerWaveViscousMultiplier (inputs 4).1)
    ring
  exact paid.trans_eq same.symm

theorem norm_original (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) :
    ‖NativeUnheatedSexticInput.kernel nu slot leaf position wave i j response outside l m p q index‖ =
      (rates nu slot leaf wave i j outside l m p q index 0)⁻¹*(rates nu slot leaf wave i j outside l m p q index 1)⁻¹*
      (rates nu slot leaf wave i j outside l m p q index 2)⁻¹*(rates nu slot leaf wave i j outside l m p q index 3)⁻¹*
      ‖pressure (parents wave index.1 0+parents wave index.1 1) i j response‖*
      ‖pressure (parents wave index.1 slot) l m (![i,j,outside] slot)‖*
      ‖pressure (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index.1 leaf).1 p q
        (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index.1 leaf).2‖*
      quarter (nodes slot leaf wave i j outside l m p q index position).1 := by
  rw [NativeUnheatedSexticInput.kernel, norm_mul, NativeUnheatedQuinticNormalForm.normalizer,
    norm_smul, NativeUnheatedQuinticFiveRows.kernel, NativeUnheatedQuinticLeaf.kernel, norm_mul,
    base, NativeUnheatedQuarticKernel.normalizer, norm_smul, tree_original]
  simp only [NativeUnheatedTriadChannelWrite.normalizer, norm_mul, norm_smul]
  change ‖(rates nu slot leaf wave i j outside l m p q index 3)⁻¹‖*
    (‖(rates nu slot leaf wave i j outside l m p q index 2)⁻¹‖*
      (‖(rates nu slot leaf wave i j outside l m p q index 0)⁻¹‖*‖(rates nu slot leaf wave i j outside l m p q index 1)⁻¹‖*
        ‖pressure (parents wave index.1 0+parents wave index.1 1) i j response‖*
        ‖pressure (parents wave index.1 slot) l m (![i,j,outside] slot)‖)*
      ‖pressure (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index.1 leaf).1 p q
        (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index.1 leaf).2‖)*
      ‖(quarter (nodes slot leaf wave i j outside l m p q index position).1 : ℂ)‖ = _
  simp only [Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative slot leaf wave i j outside l m p q index _)),
    Complex.norm_real, Real.norm_of_nonneg (quarter_nonnegative _)]
  ring

theorem hierarchical_power (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) :
    ‖NativeUnheatedSexticInput.kernel nu slot leaf position wave i j response outside l m p q index‖^4 ≤
      nu.coeff⁻¹^7*(rates nu slot leaf wave i j outside l m p q index 0)⁻¹^2*
        (rates nu slot leaf wave i j outside l m p q index 1)⁻¹^2*
        (rates nu slot leaf wave i j outside l m p q index 2)⁻¹^2*
        (rates nu slot leaf wave i j outside l m p q index 3)⁻¹^3 := by
  let d := (rates nu slot leaf wave i j outside l m p q index 0)⁻¹
  let t := (rates nu slot leaf wave i j outside l m p q index 1)⁻¹
  let s := (rates nu slot leaf wave i j outside l m p q index 2)⁻¹
  let v := (rates nu slot leaf wave i j outside l m p q index 3)⁻¹
  let P := ‖pressure (parents wave index.1 0+parents wave index.1 1) i j response‖
  let R := ‖pressure (parents wave index.1 slot) l m (![i,j,outside] slot)‖
  let Z := ‖pressure (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index.1 leaf).1 p q
    (NativeUnheatedQuarticAllSlots.slots slot wave i j outside l m index.1 leaf).2‖
  let Q := quarter (nodes slot leaf wave i j outside l m p q index position).1
  have pPaid : P^2*d ≤ nu.coeff⁻¹ := outer_paid (nu := nu) wave i j response index.1
  have rPaid : R^2*t ≤ nu.coeff⁻¹ := by
    apply paid_inverse (rate_nonnegative slot leaf wave i j outside l m p q index 1) (inv_nonneg.mpr nu.coeff_pos.le)
    exact (pressure_square _ l m _).trans (triad_multiplier (nu := nu) _ _ _ slot)
  have zPaid : Z^2*s ≤ nu.coeff⁻¹ := by
    apply paid_inverse (rate_nonnegative slot leaf wave i j outside l m p q index 2) (inv_nonneg.mpr nu.coeff_pos.le)
    exact (pressure_square _ p q _).trans (leaf_multiplier (nu := nu) _ leaf)
  have qPaid : Q^4*v ≤ nu.coeff⁻¹ := newest_quarter (nodes slot leaf wave i j outside l m p q index) position
  have d0 : 0 ≤ d := inv_nonneg.mpr (rate_nonnegative slot leaf wave i j outside l m p q index 0)
  have t0 : 0 ≤ t := inv_nonneg.mpr (rate_nonnegative slot leaf wave i j outside l m p q index 1)
  have s0 : 0 ≤ s := inv_nonneg.mpr (rate_nonnegative slot leaf wave i j outside l m p q index 2)
  have v0 : 0 ≤ v := inv_nonneg.mpr (rate_nonnegative slot leaf wave i j outside l m p q index 3)
  rw [norm_original]
  change (d*t*s*v*P*R*Z*Q)^4 ≤ _
  calc
    _ = (P^2*d)^2*(R^2*t)^2*(Z^2*s)^2*(Q^4*v)*d^2*t^2*s^2*v^3 := by ring
    _ ≤ nu.coeff⁻¹^2*nu.coeff⁻¹^2*nu.coeff⁻¹^2*nu.coeff⁻¹*d^2*t^2*s^2*v^3 := by gcongr
    _ = _ := by ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticKernel
