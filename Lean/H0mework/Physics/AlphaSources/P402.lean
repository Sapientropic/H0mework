import H0mework.Physics.AlphaSources.P401

/-!
# Proposition 402: alpha-bound grand-unification entrypoint

P401 proves that the physical gauge weak corridor is equivalent to the direct
alpha-coordinate producer obligation

`fourPi = 4*pi` and `alpha_yukawa <= 81/500`.

This file makes that alpha-bound the front door of the Standard-Model
grand-unification layer: once the alpha-bound producer is supplied, the already
proved chain yields the P384 receipt, the P374 unified formula spine, P378's
primitive producer atoms, and P380's perturbative selected-Yukawa gauge
surface.

Boundary: this still does not construct the physical alpha-bound producer.  It
proves that this producer, and not the older path-table / coordinate / gauge
comparison wrappers, is now sufficient for the current Lean grand-unification
receipt.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Direct alpha-bound consequences -/

/-- THEOREM 1: the physical alpha weak-bound producer constructs the current
P384 grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  intro h
  exact
    rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalGaugeCorridor
      ((existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_iff_alphaWeakBound).mpr h)

/-- THEOREM 2: the physical alpha weak-bound producer yields the P374 unified
formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_alphaWeakBound h)

/-- THEOREM 3: the same alpha-bound producer yields the P378 primitive
producer atoms. -/
theorem primitiveProducerAtoms_nonempty_of_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_alphaWeakBound h)

/-- THEOREM 4: the alpha-bound producer also supplies P380's perturbative
selected-Yukawa gauge surface. -/
theorem existsZeroFreePerturbativeSelectedYukawaGauge_of_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier ->
      ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier := by
  intro h
  exact
    existsZeroFreePerturbativeSelectedYukawaGauge_of_physicalGaugeCorridor
      ((existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_iff_alphaWeakBound).mpr h)

/-- THEOREM 5: the alpha-bound producer gives the selected-Yukawa
nonabsorbing-rate surface. -/
theorem existsZeroFreeNonabsorbing_of_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier ->
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  intro h
  exact
    existsZeroFreeNonabsorbing_of_physicalGaugeCorridor
      ((existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_iff_alphaWeakBound).mpr h)

/-- THEOREM 6: one compact receipt: the physical alpha-bound producer is
sufficient for the current grand-unification receipt, unified formula spine,
primitive producer atoms, and perturbative/nonabsorbing selected-Yukawa
surfaces. -/
theorem alphaWeakBound_grandUnification_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) ∧
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) ∧
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) ∧
      ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier ∧
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  intro h
  exact
    ⟨rgMonotonicityGrandUnificationReceipt_nonempty_of_alphaWeakBound h,
      unifiedFormulaSpine_nonempty_of_alphaWeakBound h,
      primitiveProducerAtoms_nonempty_of_alphaWeakBound h,
      existsZeroFreePerturbativeSelectedYukawaGauge_of_alphaWeakBound h,
      existsZeroFreeNonabsorbing_of_alphaWeakBound h⟩

end StandardModelConstraint
end SaturationMonoid
