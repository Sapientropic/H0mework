import H0mework.NavierStokes.UnheatedWriterTriad.CubicKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedCubicIdentity
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeTimeJetCarrier NativeHigherTimeJets NativeEndpointVelocityCarrier NativeResolventCompactness NativeWholeResolvent
open NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedStressPairEvolution
open NativeUnheatedPairNegativeKernel NativeUnheatedTriadChannels NativeUnheatedCubicRows
noncomputable section

theorem row_channels (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) (response : Coordinate) :
    projectedDivergenceCLM wave (mixedFlux left right wave) response =
      ∑ i : Coordinate, ∑ j : Coordinate, pressure wave i j response*(∑' a, left a i*right (wave-a) j) := by
  classical
  have expanded : mixedFlux left right wave =
      ∑ i : Coordinate, ∑ j : Coordinate, (∑' a, left a i*right (wave-a) j) • basis i j := by
    funext output input
    simp [basis, Pi.single_apply, apply_ite, Finset.sum_apply, mixedFlux]
  rw [expanded, map_sum]
  simp only [map_sum, projected_complex_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pressure]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem kernel_inner (nu : Viscosity) (wave : IntegerWavevector) (i j response : Coordinate)
    (left right : ComplexVorticityHilbertState) (c : IntegerWavevector) :
    NativeUnheatedTriadSum.innerValue (NativeUnheatedCubicKernel.kernel nu i j response) wave i j left right c =
      ((decay nu (wave-c) c)⁻¹*(root c)⁻¹) •
        (pressure (wave-c) i j response*(∑' a, left a i*right (wave-c-a) j)) := by
  unfold NativeUnheatedTriadSum.innerValue NativeUnheatedTriadSum.innerTerm NativeUnheatedCubicKernel.kernel
  have joined (a : IntegerWavevector) : a+(wave-c-a) = wave-c := by abel
  simp only [joined, Complex.real_smul, mul_assoc, tsum_mul_left]

theorem value_channels (nu : Viscosity) (left right : ComplexVorticityHilbertState)
    (outer : wholePhysical) (regular : H1 outer) (wave : IntegerWavevector) (response outside : Coordinate) :
    NativeUnheatedCubicRows.value nu left right (wholeVelocity outer.1) wave response outside =
      ∑ i : Coordinate, ∑ j : Coordinate, NativeUnheatedCubicKernel.value nu wave i j response outside
        left right (wholeVelocity (gradientValue outer regular)) := by
  let term (i j : Coordinate) (c : IntegerWavevector) :=
    NativeUnheatedTriadSum.innerValue (NativeUnheatedCubicKernel.kernel nu i j response) wave i j left right c *
      wholeVelocity (gradientValue outer regular) c outside
  have each (i j : Coordinate) : Summable (term i j) :=
    NativeUnheatedTriadSum.outer_summable _ (NativeUnheatedCubicKernel.cap nu) (NativeUnheatedCubicKernel.kernel_bound nu i j response)
      _ _ _ _ _ _ _
  have point (c : IntegerWavevector) :
      (decay nu c (wave-c))⁻¹ • ((∑' a, rowTerm left right (wave-c) a response)*wholeVelocity outer.1 c outside) =
        ∑ i : Coordinate, ∑ j : Coordinate, term i j c := by
    by_cases zero : c = 0
    · subst c
      simp only [wholeVelocity_zero, Pi.zero_apply, mul_zero, smul_zero, term, Finset.sum_const_zero]
    · have projected : (∑' a, rowTerm left right (wave-c) a response) =
          projectedDivergenceCLM (wave-c) (mixedFlux left right (wave-c)) response := by
        rw [← tsum_apply (rowTerm_summable left right (wave-c))]
        unfold rowTerm
        rw [← (projectedDivergenceCLM (wave-c)).map_tsum (dyad_summable _ _ _), dyad_sum]
      rw [projected, row_channels]
      simp only [term, kernel_inner, NativeUnheatedCubicKernel.gradient_row, Pi.smul_apply,
        Complex.real_smul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have swapped : decay nu c (wave-c) = decay nu (wave-c) c := by unfold decay; rw [add_comm]
      rw [swapped]
      push_cast
      field_simp [(root_positive c zero).ne']
  unfold NativeUnheatedCubicRows.value
  simp_rw [point]
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => each i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Summable.tsum_finsetSum (fun j _ => each i j)]
  rfl

def bound (nu : Viscosity) : ℝ := 27*NativeUnheatedCubicKernel.cap nu*‖NativeUnheatedTriadSum.weights‖

theorem value_bound (nu : Viscosity) (left right : ComplexVorticityHilbertState)
    (outer : wholePhysical) (regular : H1 outer) (wave : IntegerWavevector) (response outside : Coordinate) :
    ‖NativeUnheatedCubicRows.value nu left right (wholeVelocity outer.1) wave response outside‖ ≤
      bound nu*‖left‖*‖right‖*‖gradientValue outer regular‖ := by
  rw [value_channels nu left right outer regular wave response outside]
  apply (norm_sum_le _ _).trans
  have bounded := Finset.sum_le_sum fun (i : Coordinate) (_ : i ∈ (Finset.univ : Finset Coordinate)) =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun (j : Coordinate) (_ : j ∈ (Finset.univ : Finset Coordinate)) =>
      (NativeUnheatedCubicKernel.value_bound nu wave i j response outside left right _).trans
        (mul_le_mul_of_nonneg_left (wholeVelocity_norm_le (gradientValue outer regular)) (by
          unfold NativeUnheatedCubicKernel.cap
          positivity [nu.coeff_pos])))
  exact bounded.trans_eq (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; unfold bound; ring)

theorem action_bound (nu : Viscosity) (outer : wholePhysical) (regular : H1 outer)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖NativeUnheatedPairNegativeKernel.bilinear nu 0 wave output input
      (negativeAction outer outer regular regular) (inverseGradient outer.1) +
      NativeUnheatedPairNegativeKernel.bilinear nu 0 wave output input
        (inverseGradient outer.1) (negativeAction outer outer regular regular)‖ ≤
      2*bound nu*‖wholeVelocity outer.1‖^2*‖gradientValue outer regular‖ := by
  rw [bilinear_swap nu _ _ wave output input, bilinear_value, bilinear_value]
  apply (norm_add_le _ _).trans
  simp only [norm_neg]
  exact (add_le_add (value_bound nu _ _ outer regular wave input output)
    (value_bound nu _ _ outer regular wave output input)).trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedCubicIdentity
