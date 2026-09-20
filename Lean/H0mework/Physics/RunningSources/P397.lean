import H0mework.Physics.CouplingSources.P396

/-!
# Proposition 397: physical four-pi RG table normal form

P396 leaves two equivalent-looking producer surfaces in the physical
normalization route:

* a compact corridor witness: `fourPi = 4*pi` and every selected Yukawa
  running-sigma coordinate is bounded by the weak endpoint;
* an explicit nine-row finite path table: each Yukawa slot reaches `weak`
  through a sigma-monotone step relation.

This file proves that the explicit path table adds no extra mathematical
content.  Given the corridor witness, take the local step relation itself to
be sigma order; then each Yukawa slot reaches `weak` in one certified step.
Conversely, P396 already proved that the table collapses back to the corridor.

Boundary: this is still a normal-form theorem, not a physical RG solution.
The remaining producer obligation is now exactly the zero-free certificate
plus the physical-four-pi selected-sigma weak corridor.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

namespace PhysicalFourPiRunningSigmaIndependentCoordinateWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert the compact physical-four-pi corridor witness to P396's explicit
nine-row path table by taking sigma-order as the local step relation. -/
def toPhysicalFourPiRunningSigmaYukawaRGPathTableProducer
    (W : PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z) :
    PhysicalFourPiRunningSigmaYukawaRGPathTableProducer Z :=
  { step := fun a b => Z.running.sigma a ≤ Z.running.sigma b
    fourPi_eq_realFourPi := W.fourPi_eq_realFourPi
    up_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.up))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.up)
    charm_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.charm))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.charm)
    top_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.top))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.top)
    down_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.down))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.down)
    strange_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.strange))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.strange)
    bottom_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.bottom))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.bottom)
    electron_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.electron))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.electron)
    muon_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.muon))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.muon)
    tau_reaches_weak :=
      RGStepReach.tail
        (RGStepReach.refl (StandardModelScaleCode.yukawa YukawaParameter.tau))
        (W.selected_yukawa_sigma_le_weak YukawaParameter.tau)
    step_sigma_monotone := by
      intro a b h
      exact h }

end PhysicalFourPiRunningSigmaIndependentCoordinateWitness

/-- THEOREM 1: the compact physical-four-pi corridor witness supplies the
explicit physical-four-pi finite path table. -/
theorem existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_of_physicalFourPiWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ->
      ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  rintro ⟨Z, ⟨W⟩⟩
  exact
    ⟨Z,
      ⟨W.toPhysicalFourPiRunningSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 2: the physical-four-pi finite path table is exactly a normal form
for the compact physical-four-pi selected-sigma weak corridor. -/
theorem existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_iff_physicalFourPiWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ↔
      ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier := by
  constructor
  · exact existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_of_pathTable
  · exact existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_of_physicalFourPiWitness

/-- THEOREM 3: P396's physical-four-pi path-table receipt theorem can be read
through the compact corridor normal form. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalFourPiPathTable_normalForm
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  intro h
  exact rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalFourPiPathTable h

end StandardModelConstraint
end SaturationMonoid
