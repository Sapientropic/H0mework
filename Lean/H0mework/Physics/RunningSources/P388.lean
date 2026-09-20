import H0mework.Physics.YukawaSources.P387

/-!
# Proposition 388: coordinate-certified finite RG-step paths

P386 asks each local RG step to carry the adjacent `g^2` monotonicity
inequality directly.  P385 asks for a global scalar RG coordinate whose order
controls `g^2`.

This file glues those two producer shapes: a concrete threshold calculation may
provide local step edges plus a scalar coordinate, prove that every step moves
monotonically in that coordinate, and prove the coordinate-to-`g^2`
monotonicity once.  Lean then derives the P386 adjacent `g^2` checks and hence
the P384 grand-unification receipt.

Boundary: the physical coordinate, the step graph, and the beta/threshold
proofs of coordinate monotonicity remain producer data.  This file only proves
that those local coordinate facts are sufficient for the existing
grand-unification spine.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Coordinate-certified finite RG-step producer -/

/-- A finite RG-step producer whose adjacent monotonicity is certified through
a scalar RG coordinate. -/
structure CoordinateRGStepPathProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  rgCoordinate : StandardModelScaleCode -> ℝ
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  fourPi_pos : 0 < Z.running.fourPi
  selected_yukawa_reaches_weak :
    ∀ y : YukawaParameter,
      RGStepReach step (StandardModelScaleCode.yukawa y)
        StandardModelScaleCode.weak
  step_coord_monotone :
    ∀ {a b : StandardModelScaleCode}, step a b ->
      rgCoordinate a ≤ rgCoordinate b
  gaugeCouplingSq_monotone_on_coordinate :
    ∀ {a b : StandardModelScaleCode}, rgCoordinate a ≤ rgCoordinate b ->
      (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling b) ^ (2 : Nat)

namespace CoordinateRGStepPathProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: coordinate monotonicity on each step gives adjacent `g^2`
monotonicity on each step. -/
theorem gaugeCouplingSq_step_monotone
    (C : CoordinateRGStepPathProducer Z)
    {a b : StandardModelScaleCode}
    (h : C.step a b) :
    (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
      (Z.running.gaugeCoupling b) ^ (2 : Nat) :=
  C.gaugeCouplingSq_monotone_on_coordinate (C.step_coord_monotone h)

/-- Convert the coordinate-certified step producer to P386's step-path
producer. -/
def toRGStepPathProducer
    (C : CoordinateRGStepPathProducer Z) :
    RGStepPathProducer Z :=
  { step := C.step
    fourPi_pos := C.fourPi_pos
    selected_yukawa_reaches_weak := C.selected_yukawa_reaches_weak
    gaugeCouplingSq_step_monotone := C.gaugeCouplingSq_step_monotone }

/-- THEOREM 3: hence a coordinate-certified step producer gives P382's gauge
weak corridor. -/
theorem toSelectedYukawaGaugeCouplingsBoundedByWeak
    (C : CoordinateRGStepPathProducer Z) :
    SelectedYukawaGaugeCouplingsBoundedByWeak Z :=
  C.toRGStepPathProducer.toSelectedYukawaGaugeCouplingsBoundedByWeak

end CoordinateRGStepPathProducer

/-- A zero-free certificate equipped with a coordinate-certified finite RG-step
producer. -/
def ExistsZeroFreeCoordinateRGStepPathProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (CoordinateRGStepPathProducer Z)

/-- THEOREM 4: coordinate-certified finite RG steps supply P386's step-path
producer. -/
theorem existsZeroFreeRGStepPathProducer_of_coordinateStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier ->
      ExistsZeroFreeRGStepPathProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toRGStepPathProducer⟩⟩

/-- THEOREM 5: coordinate-certified finite RG steps construct the P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  intro h
  exact
    rgMonotonicityGrandUnificationReceipt_nonempty_of_stepPathProducer
      (existsZeroFreeRGStepPathProducer_of_coordinateStepPath h)

/-- THEOREM 6: coordinate-certified finite RG steps therefore provide the P374
unified-formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_coordinateStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateStepPath h)

/-- THEOREM 7: coordinate-certified finite RG steps also provide the primitive
producer atoms. -/
theorem primitiveProducerAtoms_nonempty_of_coordinateStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateStepPath h)

end StandardModelConstraint
end SaturationMonoid
