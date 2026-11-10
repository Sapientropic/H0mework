import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularSourcePrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedOrderedStatic
open ActualDressedCorrectedElectronRead ActualDressedEMTensorClock ActualCompositeFieldCurrent
open LowEnergy.ActualDressedVisiblePole Filter Set
open scoped Topology Matrix

def directionZeroClockEM (event : DressedEvent) : Matrix (Fin 4) (Fin 4) DirectionParameters[X] :=
  fun mu nu => (directionClockEMNumerator event mu nu).coeff (directionClockOrder event)
def directionZeroClockProbe (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : DirectionParameters[X] :=
  (directionClockProbeNumerator event pd ps dL dR sL sR).coeff (directionClockOrder event)

def DirectionClockFinite (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : Prop :=
  (∀mu nu,X^directionClockOrder event∣directionClockEMNumerator event mu nu) ∧
  X^directionClockOrder event∣directionClockProbeNumerator event pd ps dL dR sL sR

def DirectionSpatialFinite (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : Prop :=
  (∀mu nu,X^directionSpatialOrder event∣X^4*directionZeroClockEM event mu nu) ∧
  X^directionSpatialOrder event∣X^4*directionZeroClockProbe event pd ps dL dR sL sR

def directionScaledNumerator (event : DressedEvent) (N : DirectionParameters[X]) : DirectionParameters[X] :=
  (X^4*N) /ₘ X^directionSpatialOrder event

def sourceAngularReadPrice (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ) : ℝ :=
  2*directionPolynomialPrice (directionScaledNumerator event N)/eta

theorem actual_direction_clock_finite (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (regular : directionLeadingRead event n≠0)
    (clock : DirectionClockFinite event pd ps dL dR sL sR) : ClockFinite event n pd ps dL dR sL sR := by
  have mapped {P : DirectionStaticPolynomials} (factor : X^directionClockOrder event∣P) :
      X^directionClockOrder event∣directionSpecialize n P := by
    have paid := (_root_.map_dvd (directionSpecialize n)) factor
    simpa only [map_pow,directionSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_X] using paid
  constructor
  · intro mu nu
    rw [actual_direction_clock_order event n regular,←actual_direction_clock_em]
    exact mapped (clock.1 mu nu)
  · rw [actual_direction_clock_order event n regular,←actual_direction_clock_probe]
    exact mapped clock.2

theorem actual_direction_zero_clock_em (event : DressedEvent) (n : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) (mu nu : Fin 4) :
    zeroClockEMNumerator event n mu nu=(directionZeroClockEM event mu nu).map (MvPolynomial.eval (directionValues n)) := by
  unfold zeroClockEMNumerator
  rw [actual_direction_clock_order event n regular,←actual_direction_clock_em]
  simp only [directionSpecialize,Polynomial.coe_mapRingHom,coeff_map,directionZeroClockEM]

theorem actual_direction_zero_clock_probe (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (regular : directionLeadingRead event n≠0) :
    zeroClockProbeNumerator event n pd ps dL dR sL sR=
      (directionZeroClockProbe event pd ps dL dR sL sR).map (MvPolynomial.eval (directionValues n)) := by
  unfold zeroClockProbeNumerator
  rw [actual_direction_clock_order event n regular,←actual_direction_clock_probe]
  simp only [directionSpecialize,Polynomial.coe_mapRingHom,coeff_map,directionZeroClockProbe]

private theorem quotient_factor {R : Type*} [CommRing R] (P : R[X]) (m : ℕ) (factor : X^m∣P) :
    X^m*(P /ₘ X^m)=P := by
  obtain ⟨Q,eq⟩ := factor
  rw [eq,mul_divByMonic_cancel_left Q (monic_X_pow m)]

private theorem source_ratio (event : DressedEvent) (N : DirectionParameters[X]) (n : PhysicalMomentum)
    (eps : ℝ) (away : eps≠0) (factor : X^directionSpatialOrder event∣X^4*N)
    (_denominator : (directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)≠0) :
    (eps : ℂ)^4*N.eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)/
      (directionSpatialDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)=
    (directionScaledNumerator event N).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)/
      (directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ) := by
  let f := MvPolynomial.eval (directionValues n)
  have nEq := congrArg (fun P : DirectionParameters[X] => P.eval₂ f (eps : ℂ)) (quotient_factor _ _ factor)
  have dEq := congrArg (fun P : DirectionParameters[X] => P.eval₂ f (eps : ℂ))
    (quotient_factor (directionSpatialDenominator event) (directionSpatialOrder event)
      (X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)))
  simp only [eval₂_mul,eval₂_pow,eval₂_X] at nEq dEq
  change (eps : ℂ)^4*N.eval₂ f (eps : ℂ)/(directionSpatialDenominator event).eval₂ f (eps : ℂ)=_
  rw [←dEq,←nEq]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr away))

private theorem source_scaled_price (event : DressedEvent) (N : DirectionParameters[X])
    (eta : ℝ) (positive : 0<eta) (n : PhysicalMomentum) (chart : n∈sourceDirectionChart event eta)
    (eps : ℝ) (away : eps≠0) (small : |eps|<sourceDirectionRadius event eta)
    (factor : X^directionSpatialOrder event∣X^4*N) :
    ‖(eps : ℂ)^4*N.eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)/
      (directionSpatialDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)‖≤
        sourceAngularReadPrice event N eta := by
  have lower := actual_direction_reduced_denominator_price event eta positive n chart eps small
  have nonzero : (directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)≠0 := by
    intro zero
    rw [zero,norm_zero] at lower
    linarith
  rw [source_ratio event N n eps away factor nonzero,norm_div]
  have bound := actual_direction_polynomial_price (directionScaledNumerator event N) n chart.1 (eps : ℂ)
    (by rw [Complex.norm_real,Real.norm_eq_abs]; exact (small.trans_le (min_le_left _ _)).le)
  have denominatorPositive : 0<‖(directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)‖ := by linarith
  rw [div_le_iff₀ denominatorPositive]
  unfold sourceAngularReadPrice
  have mass := direction_polynomial_price_nonneg (directionScaledNumerator event N)
  have weighted := mul_le_mul_of_nonneg_left lower (div_nonneg (by positivity : 0≤2*directionPolynomialPrice (directionScaledNumerator event N)) positive.le)
  have cancel : (2*directionPolynomialPrice (directionScaledNumerator event N)/eta)*(eta/2)=
      directionPolynomialPrice (directionScaledNumerator event N) := by field_simp
  rw [cancel] at weighted
  exact bound.trans weighted

theorem actual_direction_spatial_chart (event : DressedEvent) (eta : ℝ) (positive : 0<eta)
    (n : PhysicalMomentum) (chart : n∈sourceDirectionChart event eta) (eps : ℝ)
    (away : eps≠0) (small : |eps|<sourceDirectionRadius event eta) :
    (sourceClockDenominator event n).eval (eps : ℂ)≠0 := by
  have regular := (direction_chart_regular event eta positive n chart).2
  have lower := actual_direction_reduced_denominator_price event eta positive n chart eps small
  have reducedNonzero : (directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)≠0 := by
    intro zero; rw [zero,norm_zero] at lower; linarith
  have dEq := congrArg (fun P : DirectionParameters[X] => P.eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ))
    (quotient_factor (directionSpatialDenominator event) (directionSpatialOrder event)
      (X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)))
  simp only [eval₂_mul,eval₂_pow,eval₂_X] at dEq
  rw [actual_direction_spatial_denominator event n regular,eval_map,←dEq]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr away)) reducedNonzero

/-- Both actual independent probe legs and every EM entry share one direction chart and one spatial radius. -/
theorem actual_direction_full_read_price (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (eta : ℝ) (positive : 0<eta)
    (n : PhysicalMomentum) (chart : n∈sourceDirectionChart event eta) (eps : ℝ)
    (away : eps≠0) (small : |eps|<sourceDirectionRadius event eta)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    (∀mu nu,‖-(eps : ℂ)^4*zeroClockEMRead event eps n mu nu‖≤
      sourceAngularReadPrice event (directionZeroClockEM event mu nu) eta) ∧
    ‖-(eps : ℂ)^4*zeroClockProbeRead event eps n pd ps dL dR sL sR‖≤
      sourceAngularReadPrice event (directionZeroClockProbe event pd ps dL dR sL sR) eta := by
  have regular := (direction_chart_regular event eta positive n chart).2
  have dRegular := actual_direction_spatial_chart event eta positive n chart eps away small
  constructor
  · intro mu nu
    rw [zeroClockEMRead,zeroClockEMFraction,reduced_read_at_regular _ _ _ dRegular,
      actual_direction_zero_clock_em event n regular mu nu,actual_direction_spatial_denominator event n regular,
      eval_map,eval_map,neg_mul,norm_neg,←mul_div_assoc]
    exact source_scaled_price event _ eta positive n chart eps away small (spatial.1 mu nu)
  · rw [zeroClockProbeRead,zeroClockProbeFraction,reduced_read_at_regular _ _ _ dRegular,
      actual_direction_zero_clock_probe event n pd ps dL dR sL sR regular,actual_direction_spatial_denominator event n regular,
      eval_map,eval_map,neg_mul,norm_neg,←mul_div_assoc]
    exact source_scaled_price event _ eta positive n chart eps away small spatial.2

/-- Source coefficient divisibility returns the original full damping limits and the common chart price together. -/
theorem actual_direction_finite_chart_return (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (clock : DirectionClockFinite event pd ps dL dR sL sR)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) (eta : ℝ) (positive : 0<eta)
    (n : PhysicalMomentum) (chart : n∈sourceDirectionChart event eta) (eps : ℝ)
    (away : eps≠0) (small : |eps|<sourceDirectionRadius event eta) :
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n)) ∧
    Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockProbeRead event eps n pd ps dL dR sL sR)) ∧
    (∀mu nu,‖-(eps : ℂ)^4*zeroClockEMRead event eps n mu nu‖≤
      sourceAngularReadPrice event (directionZeroClockEM event mu nu) eta) ∧
    ‖-(eps : ℂ)^4*zeroClockProbeRead event eps n pd ps dL dR sL sR‖≤
      sourceAngularReadPrice event (directionZeroClockProbe event pd ps dL dR sL sR) eta := by
  have regular := (direction_chart_regular event eta positive n chart).2
  have finite := actual_direction_clock_finite event n pd ps dL dR sL sR regular clock
  have dRegular := actual_direction_spatial_chart event eta positive n chart eps away small
  refine ⟨?_,actual_zero_clock_probe event eps n pd ps dL dR sL sR dRegular finite.2,?_⟩
  · apply tendsto_pi_nhds.2
    intro mu
    apply tendsto_pi_nhds.2
    intro nu
    exact actual_zero_clock_em_entry event eps n dRegular mu nu (finite.1 mu nu)
  · exact actual_direction_full_read_price event pd ps dL dR sL sR eta positive n chart eps away small spatial

def DirectionActualChartReturn (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Prop :=
  ∀eta : ℝ,0<eta→∀n : PhysicalMomentum,n∈sourceDirectionChart event eta→∀eps : ℝ,
    eps≠0→|eps|<sourceDirectionRadius event eta→
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n)) ∧
    Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockProbeRead event eps n pd ps dL dR sL sR)) ∧
    (∀mu nu,‖-(eps : ℂ)^4*zeroClockEMRead event eps n mu nu‖≤
      sourceAngularReadPrice event (directionZeroClockEM event mu nu) eta) ∧
    ‖-(eps : ℂ)^4*zeroClockProbeRead event eps n pd ps dL dR sL sR‖≤
      sourceAngularReadPrice event (directionZeroClockProbe event pd ps dL dR sL sR) eta

inductive AngularSourceDisposition (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Type
  | singular (whole_determinant_zero : directionClockDeterminant event=0)
  | clockResponsibility (whole_determinant_nonzero : directionClockDeterminant event≠0)
      (clock_responsibility : ¬DirectionClockFinite event pd ps dL dR sL sR)
  | spatialResponsibility (whole_determinant_nonzero : directionClockDeterminant event≠0)
      (clock_finite : DirectionClockFinite event pd ps dL dR sL sR)
      (spatial_responsibility : ¬DirectionSpatialFinite event pd ps dL dR sL sR)
  | chart (whole_determinant_nonzero : directionClockDeterminant event≠0)
      (clock_finite : DirectionClockFinite event pd ps dL dR sL sR)
      (spatial_finite : DirectionSpatialFinite event pd ps dL dR sL sR)
      (actual_chart_return : DirectionActualChartReturn event pd ps dL dR sL sR)

/-- Branch tests use the same actual whole source coefficients; no caller supplies an inverse, price or isotropy. -/
def sourceAngularDisposition (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : AngularSourceDisposition event pd ps dL dR sL sR := by
  classical
  by_cases singular : directionClockDeterminant event=0
  · exact .singular singular
  · by_cases clock : DirectionClockFinite event pd ps dL dR sL sR
    · by_cases spatial : DirectionSpatialFinite event pd ps dL dR sL sR
      · exact .chart singular clock spatial (actual_direction_finite_chart_return event pd ps dL dR sL sR clock spatial)
      · exact .spatialResponsibility singular clock spatial
    · exact .clockResponsibility singular clock

end LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
