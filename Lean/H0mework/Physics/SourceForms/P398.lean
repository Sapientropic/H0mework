import H0mework.Physics.RunningSources.P397

/-!
# Proposition 398: physical four-pi sigma/gauge corridor equivalence

P397 reduces the physical finite RG path table to a compact selected-sigma
weak corridor.  But running sigma is not the physical primitive; P274 defines
it as `g^2 / fourPi`.  Under physical normalization `fourPi = 4*pi`, and since
`4*pi` is positive, order in the sigma coordinate is exactly order in the
squared gauge coupling coordinate.

This file therefore proves that the live physical-four-pi corridor may be
stated on the gauge-coupling side without loss.  The remaining producer
surface is now: construct the zero-free certificate, prove `fourPi = 4*pi`, and
prove each selected Yukawa squared gauge coupling is bounded by the weak
endpoint.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Sigma order is gauge-coupling-square order for positive four-pi -/

/-- THEOREM 1: with a positive common `fourPi`, the selected running-sigma weak
corridor is equivalent to the selected squared-gauge-coupling weak corridor. -/
theorem selectedYukawaGaugeCouplingsBoundedByWeak_of_selectedYukawaSigmaBoundedByWeak
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (hfour : 0 < Z.running.fourPi)
    (hZ : SelectedYukawaSigmaBoundedByWeak Z) :
    SelectedYukawaGaugeCouplingsBoundedByWeak Z := by
  refine ⟨hfour, ?_⟩
  intro y
  have hdiv :
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) /
          Z.running.fourPi ≤
        (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat) /
          Z.running.fourPi := by
    simpa [alphaFromGaugeCoupling, Z.running.sigma_eq_alpha
        (StandardModelScaleCode.yukawa y),
      Z.running.sigma_eq_alpha StandardModelScaleCode.weak] using hZ y
  exact (div_le_div_iff_of_pos_right hfour).mp hdiv

/-! ## Physical-four-pi gauge corridor witness -/

/-- Physical-normalization gauge-side weak corridor: the denominator is fixed
to `4*pi`, and every selected Yukawa squared gauge coupling is bounded by the
weak endpoint. -/
structure PhysicalFourPiGaugeWeakCorridorWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  fourPi_eq_realFourPi : Z.running.fourPi = realFourPi
  selected_yukawa_gauge_le_weak :
    ∀ y : YukawaParameter,
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat)

namespace PhysicalFourPiGaugeWeakCorridorWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Forget the physical equality to P382's positive gauge-coupling corridor. -/
theorem toSelectedYukawaGaugeCouplingsBoundedByWeak
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) :
    SelectedYukawaGaugeCouplingsBoundedByWeak Z := by
  refine ⟨?_, W.selected_yukawa_gauge_le_weak⟩
  rw [W.fourPi_eq_realFourPi]
  exact realFourPi_pos

/-- Convert the physical gauge-side corridor to P396/P397's physical sigma-side
corridor. -/
theorem toPhysicalFourPiRunningSigmaIndependentCoordinateWitness
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) :
    PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z := by
  exact
    { fourPi_eq_realFourPi := W.fourPi_eq_realFourPi
      selected_yukawa_sigma_le_weak :=
        selectedYukawaSigmaBoundedByWeak_of_selectedYukawaGaugeCouplingsBoundedByWeak
          Z W.toSelectedYukawaGaugeCouplingsBoundedByWeak }

end PhysicalFourPiGaugeWeakCorridorWitness

namespace PhysicalFourPiRunningSigmaIndependentCoordinateWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert the physical sigma-side corridor back to the physical gauge-side
corridor. -/
theorem toPhysicalFourPiGaugeWeakCorridorWitness
    (W : PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z) :
    PhysicalFourPiGaugeWeakCorridorWitness Z := by
  have hfour : 0 < Z.running.fourPi := by
    rw [W.fourPi_eq_realFourPi]
    exact realFourPi_pos
  exact
    { fourPi_eq_realFourPi := W.fourPi_eq_realFourPi
      selected_yukawa_gauge_le_weak :=
        (selectedYukawaGaugeCouplingsBoundedByWeak_of_selectedYukawaSigmaBoundedByWeak
          Z hfour W.selected_yukawa_sigma_le_weak).2 }

end PhysicalFourPiRunningSigmaIndependentCoordinateWitness

/-- A zero-free certificate equipped with the physical-four-pi gauge-side weak
corridor. -/
def ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (PhysicalFourPiGaugeWeakCorridorWitness Z)

/-- THEOREM 5: the physical gauge-side corridor supplies the physical sigma-side
corridor. -/
theorem existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_of_physicalGaugeCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ->
      ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier := by
  rintro ⟨Z, ⟨W⟩⟩
  exact ⟨Z, ⟨W.toPhysicalFourPiRunningSigmaIndependentCoordinateWitness⟩⟩

/-- THEOREM 6: the physical sigma-side corridor supplies the physical gauge-side
corridor. -/
theorem existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_of_physicalSigmaCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ->
      ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier := by
  rintro ⟨Z, ⟨W⟩⟩
  exact ⟨Z, ⟨W.toPhysicalFourPiGaugeWeakCorridorWitness⟩⟩

/-- THEOREM 7: with physical four-pi normalization, the selected-sigma weak
corridor and selected squared-gauge-coupling weak corridor are exactly
producer-equivalent. -/
theorem existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_iff_physicalGaugeCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ↔
      ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier := by
  constructor
  · exact existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_of_physicalSigmaCorridor
  · exact existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_of_physicalGaugeCorridor

/-- THEOREM 8: P397's physical-four-pi finite path table can equivalently be
accepted as the physical gauge-side weak corridor. -/
theorem existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_iff_physicalGaugeCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ↔
      ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier := by
  exact
    existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_iff_physicalFourPiWitness.trans
      existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_iff_physicalGaugeCorridor

/-- THEOREM 9: the physical gauge-side weak corridor constructs the current
P384 grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalGaugeCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalFourPiWitness ∘
    existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_of_physicalGaugeCorridor

end StandardModelConstraint
end SaturationMonoid
