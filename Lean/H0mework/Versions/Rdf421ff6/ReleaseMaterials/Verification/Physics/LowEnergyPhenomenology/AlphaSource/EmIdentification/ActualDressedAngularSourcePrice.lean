import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularRegularChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedOrderedStatic
open scoped BigOperators

def directionCoefficientPrice (P : DirectionParameters) : ℝ := ∑d∈P.support, ‖P.coeff d‖
def directionPolynomialPrice (P : DirectionParameters[X]) : ℝ := ∑j∈P.support, directionCoefficientPrice (P.coeff j)

theorem direction_coefficient_price_nonneg (P : DirectionParameters) : 0≤directionCoefficientPrice P :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem direction_polynomial_price_nonneg (P : DirectionParameters[X]) : 0≤directionPolynomialPrice P :=
  Finset.sum_nonneg (fun _ _ => direction_coefficient_price_nonneg _)

private theorem direction_coordinate_price (n : PhysicalMomentum) (unit : spatialSquare n=1) (j : Fin 3) :
    ‖directionValues n j‖≤1 := by
  have single : (n j)^2≤∑k : Fin 3,(n k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (n k)) (Finset.mem_univ j)
  have value : (n j)^2≤ spatialSquare n := by simpa only [spatialSquare,Fin.sum_univ_three] using single
  rw [unit] at value
  have bound : |n j|≤1 := abs_le.mpr ⟨by nlinarith [sq_nonneg (n j+1)],by nlinarith [sq_nonneg (n j-1)]⟩
  simpa only [directionValues,Complex.norm_real,Real.norm_eq_abs] using bound

private theorem coefficient_price (P : DirectionParameters) (x : Fin 3→ℂ) (bound : ∀j,‖x j‖≤1) :
    ‖MvPolynomial.eval x P‖≤directionCoefficientPrice P := by
  rw [MvPolynomial.eval_eq']
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply (Finset.norm_prod_le _ _).trans
  simp only [norm_pow]
  apply Finset.prod_le_one (fun _ _ => pow_nonneg (norm_nonneg _) _)
  intro j _
  exact pow_le_one₀ (norm_nonneg _) (bound j)

theorem actual_direction_coefficient_price (P : DirectionParameters) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) : ‖MvPolynomial.eval (directionValues n) P‖≤directionCoefficientPrice P :=
  coefficient_price P _ (direction_coordinate_price n unit)

theorem actual_direction_polynomial_price (P : DirectionParameters[X]) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (z : ℂ) (small : ‖z‖≤1) :
    ‖P.eval₂ (MvPolynomial.eval (directionValues n)) z‖≤directionPolynomialPrice P := by
  rw [eval₂_eq_sum,Polynomial.sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) small)).trans
  exact actual_direction_coefficient_price _ n unit

private theorem source_power_quotient {R : Type*} [CommRing R] (P : R[X]) (m : ℕ) (factor : X^m∣P) :
    X^m*(P /ₘ X^m)=P := by
  obtain ⟨Q,eq⟩ := factor
  rw [eq,mul_divByMonic_cancel_left Q (monic_X_pow m)]

private theorem source_quotient_constant {R : Type*} [CommRing R] (P : R[X]) (m : ℕ) (factor : X^m∣P) :
    (P /ₘ X^m).coeff 0=P.coeff m := by
  have paid := congrArg (fun Q : R[X] => Q.coeff m) (source_power_quotient P m factor)
  have coefficient : (X^m*(P /ₘ X^m)).coeff m=(P /ₘ X^m).coeff 0 := by
    simpa only [zero_add] using coeff_X_pow_mul (P /ₘ X^m) m 0
  exact coefficient.symm.trans paid

def directionReducedDenominator (event : DressedEvent) : DirectionParameters[X] :=
  directionSpatialDenominator event /ₘ X^directionSpatialOrder event

def directionTailPrice (event : DressedEvent) : ℝ := directionPolynomialPrice (divX (directionReducedDenominator event))
def sourceDirectionRadius (event : DressedEvent) (eta : ℝ) : ℝ := min 1 (eta/(2*(1+directionTailPrice event)))

theorem source_direction_radius_positive (event : DressedEvent) (eta : ℝ) (positive : 0<eta) :
    0<sourceDirectionRadius event eta := by
  apply lt_min (by norm_num)
  have nonneg := direction_polynomial_price_nonneg (divX (directionReducedDenominator event))
  change 0≤directionTailPrice event at nonneg
  exact div_pos positive (by positivity)

private theorem reduced_constant (event : DressedEvent) :
    (directionReducedDenominator event).coeff 0=directionLeadingDenominator event :=
  source_quotient_constant _ _ (X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less))

theorem actual_direction_reduced_denominator_price (event : DressedEvent) (eta : ℝ) (_positive : 0<eta)
    (n : PhysicalMomentum) (chart : n∈sourceDirectionChart event eta) (eps : ℝ)
    (small : |eps|<sourceDirectionRadius event eta) :
    eta/2≤‖(directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)‖ := by
  let Q := directionReducedDenominator event
  let f := MvPolynomial.eval (directionValues n)
  have zSmall : ‖(eps : ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (small.trans_le (min_le_left _ _)).le
  have tail := actual_direction_polynomial_price (divX Q) n chart.1 (eps : ℂ) zSmall
  have expansion := congrArg (fun P : DirectionParameters[X] => P.eval₂ f (eps : ℂ)) (X_mul_divX_add Q)
  simp only [eval₂_add,eval₂_mul,eval₂_X,eval₂_C] at expansion
  have difference : Q.eval₂ f (eps : ℂ)-directionLeadingRead event n=
      (eps : ℂ)*(divX Q).eval₂ f (eps : ℂ) := by
    rw [reduced_constant] at expansion
    exact sub_eq_iff_eq_add.mpr (by simpa only [directionLeadingRead,add_comm] using expansion.symm)
  have error : ‖Q.eval₂ f (eps : ℂ)-directionLeadingRead event n‖≤eta/2 := by
    rw [difference,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have cutoff : |eps|<eta/(2*(1+directionTailPrice event)) := small.trans_le (min_le_right _ _)
    have denominator : 0<2*(1+directionTailPrice event) := by
      have paid := direction_polynomial_price_nonneg (divX Q)
      change 0≤directionTailPrice event at paid
      linarith
    have scaled := (lt_div_iff₀ denominator).mp cutoff
    have nonnegative := direction_polynomial_price_nonneg (divX Q)
    change 0≤directionTailPrice event at nonnegative
    have estimate := mul_le_mul_of_nonneg_left tail (abs_nonneg eps)
    change |eps| * ‖(divX Q).eval₂ f (eps : ℂ)‖≤|eps| * directionTailPrice event at estimate
    nlinarith [abs_nonneg eps]
  have lower := norm_sub_norm_le (directionLeadingRead event n) (Q.eval₂ f (eps : ℂ))
  rw [norm_sub_rev] at lower
  change eta/2≤‖Q.eval₂ f (eps : ℂ)‖
  linarith [chart.2]

end LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
