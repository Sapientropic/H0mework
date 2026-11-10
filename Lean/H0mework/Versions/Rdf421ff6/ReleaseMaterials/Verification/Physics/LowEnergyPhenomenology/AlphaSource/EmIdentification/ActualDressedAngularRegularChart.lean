import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularStaticCarrier
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open ActualDressedFullCoulomb ActualDressedOrderedStatic ActualDressedZeroDamping
open PreparationVacuumPhysicalCharacteristic Filter Set
open scoped Topology

def directionClockOrder (event : DressedEvent) : ℕ := (directionClockDeterminant event).natTrailingDegree

def directionSpatialDenominator (event : DressedEvent) : DirectionParameters[X] :=
  (directionClockDeterminant event).coeff (directionClockOrder event)

def directionSpatialOrder (event : DressedEvent) : ℕ := (directionSpatialDenominator event).natTrailingDegree

/-- This coefficient is generated before choosing a direction. Its zero set records genuine specialization exceptions. -/
def directionLeadingDenominator (event : DressedEvent) : DirectionParameters :=
  (directionSpatialDenominator event).coeff (directionSpatialOrder event)

def directionLeadingRead (event : DressedEvent) (n : PhysicalMomentum) : ℂ :=
  MvPolynomial.eval (directionValues n) (directionLeadingDenominator event)

def sourceExceptionalDirections (event : DressedEvent) : Set PhysicalMomentum :=
  {n | spatialSquare n=1 ∧ directionLeadingRead event n=0}

def sourceRegularDirections (event : DressedEvent) : Set PhysicalMomentum :=
  {n | spatialSquare n=1 ∧ directionLeadingRead event n≠0}

def sourceDirectionChart (event : DressedEvent) (eta : ℝ) : Set PhysicalMomentum :=
  {n | spatialSquare n=1 ∧ eta≤‖directionLeadingRead event n‖}

private theorem trailing_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R→+*S) (P : R[X]) (regular : f (P.coeff P.natTrailingDegree)≠0) :
    (P.map f).natTrailingDegree=P.natTrailingDegree := by
  have lead : (P.map f).coeff P.natTrailingDegree≠0 := by simpa only [coeff_map,directionLeadingRead,directionLeadingDenominator] using regular
  have nonzero : P.map f≠0 := fun zero => lead (by rw [zero,coeff_zero])
  apply le_antisymm (natTrailingDegree_le_of_ne_zero lead)
  apply le_natTrailingDegree nonzero
  intro j less
  rw [coeff_map,coeff_eq_zero_of_lt_natTrailingDegree less,map_zero]

private theorem coefficient_nonzero_polynomial {R : Type*} [Semiring R] (P : R[X]) (j : ℕ)
    (regular : P.coeff j≠0) : P≠0 := fun zero => regular (by rw [zero,coeff_zero])

theorem actual_direction_clock_order (event : DressedEvent) (n : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) : sourceClockOrder event n=directionClockOrder event := by
  have spatialLead : ((directionSpatialDenominator event).map (MvPolynomial.eval (directionValues n))).coeff
      (directionSpatialOrder event)≠0 := by simpa only [coeff_map,directionLeadingRead,directionLeadingDenominator] using regular
  have spatialNonzero := coefficient_nonzero_polynomial _ _ spatialLead
  have paid := trailing_map (Polynomial.mapRingHom (MvPolynomial.eval (directionValues n)))
    (directionClockDeterminant event) spatialNonzero
  unfold sourceClockOrder
  rw [←actual_direction_clock_determinant]
  exact paid

theorem actual_direction_spatial_denominator (event : DressedEvent) (n : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) :
    sourceClockDenominator event n=(directionSpatialDenominator event).map (MvPolynomial.eval (directionValues n)) := by
  unfold sourceClockDenominator
  rw [actual_direction_clock_order event n regular,←actual_direction_clock_determinant]
  simp only [directionSpecialize,Polynomial.coe_mapRingHom,coeff_map,directionSpatialDenominator]

theorem actual_direction_spatial_order (event : DressedEvent) (n : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) :
    (sourceClockDenominator event n).natTrailingDegree=directionSpatialOrder event := by
  rw [actual_direction_spatial_denominator event n regular]
  exact trailing_map _ _ regular

theorem actual_direction_determinant_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) : irClockDeterminant event n≠0 := by
  have leading : (sourceClockDenominator event n).coeff (directionSpatialOrder event)≠0 := by
    rw [actual_direction_spatial_denominator event n regular,coeff_map]
    exact regular
  have nonzero := coefficient_nonzero_polynomial _ _ leading
  exact fun zero => nonzero (by unfold sourceClockDenominator; rw [zero,coeff_zero])

theorem actual_direction_original_chart (event : DressedEvent) (n : PhysicalMomentum)
    (regular : directionLeadingRead event n≠0) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      (sourceClockDenominator event n).eval (eps : ℂ)≠0 ∧ dampingDeterminant event eps n≠0 ∧
        ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi 0), 0<sigma ∧
          ActualDressedCorrectedGreen.correctedDet event eps 0 sigma n≠0 :=
  source_ordered_original_chart event n (actual_direction_determinant_nonzero event n regular)

theorem direction_leading_continuous (event : DressedEvent) : Continuous (directionLeadingRead event) := by
  apply (MvPolynomial.continuous_eval (directionLeadingDenominator event)).comp
  apply continuous_pi
  intro j
  exact Complex.continuous_ofReal.comp (continuous_apply j)

theorem direction_regular_open (event : DressedEvent) : IsOpen {n : PhysicalMomentum | directionLeadingRead event n≠0} :=
  isOpen_ne.preimage (direction_leading_continuous event)

theorem direction_chart_regular (event : DressedEvent) (eta : ℝ) (positive : 0<eta)
    (n : PhysicalMomentum) (chart : n∈sourceDirectionChart event eta) : n∈sourceRegularDirections event := by
  refine ⟨chart.1,?_⟩
  intro zero
  have bound := chart.2
  rw [zero,norm_zero] at bound
  exact (not_le_of_gt positive) bound

theorem direction_sphere_disposition (event : DressedEvent) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    n∈sourceExceptionalDirections event ∨ n∈sourceRegularDirections event := by
  classical
  by_cases zero : directionLeadingRead event n=0
  · exact Or.inl ⟨unit,zero⟩
  · exact Or.inr ⟨unit,zero⟩

end LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
