/-
  Proposition 465: faithful final front door for the Standard-Model surface.

  P449/P450 installed the nondegenerate physical-faithfulness layer on the
  P447 irreducible grand-unification kernel, and proved that the degenerate
  `Unit/Unit/Unit` toy carrier cannot pass it.  P419/P420/P463 then expose the
  later Poincare-resolved and one-loop-carrier final doors.

  This file welds those two lines together.  A faithful grand-unification
  kernel plus the still-explicit 4D Poincare geometry certificate constructs
  the final P419 output and, by P463, carries the P462/P464 one-loop carrier
  receipt.  The result is intentionally a stricter sufficient front door, not
  an equivalence: ordinary P419 output still does not by itself prove
  nondegenerate physical faithfulness.
-/

import H0mework.Physics.SourceContracts.P450
import H0mework.Physics.RepresentationSources.P463
import H0mework.Physics.RepresentationSources.P464

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-! ## Faithful final front door -/

/-- The final strict front door currently justified by the Lean spine:

* a P449 physically faithful P447 kernel;
* a 4D Poincare generation-slot geometry certificate.

The geometry field remains explicit because P280/P419 deliberately keep
manifold Poincare duality as a producer obligation. -/
def PhysicallyFaithfulPoincareHolyGrailFrontDoor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  PhysicallyFaithfulGrandUnificationFrontDoor Index A CKMCarrier ∧
    Nonempty FourDimensionalPoincareGenerationSlotCertificate

/-- THEOREM 1: the faithful final front door supplies P419's final concrete
Standard-Model holy-grail output. -/
theorem faithfulPoincareFrontDoor_implies_holyGrailOutput :
    PhysicallyFaithfulPoincareHolyGrailFrontDoor Index A CKMCarrier ->
      Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) := by
  rintro ⟨hfaithful, hgeometry⟩
  have hreceipt :
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) :=
    faithfulFrontDoor_implies_singleSourcePhysicalHolyGrailReceipt
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier) hfaithful
  exact
    (standardModelPoincareResolved_nonempty_iff_holyGrailOutput
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).mp
      ((standardModelPoincareResolved_nonempty_iff_receipt_and_geometry
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).mpr
        ⟨hreceipt, hgeometry⟩)

/-- THEOREM 2: the faithful final front door also supplies P420's expanded
kernel, because P420 is existence-equivalent to the P419 output. -/
theorem faithfulPoincareFrontDoor_implies_concreteKernel :
    PhysicallyFaithfulPoincareHolyGrailFrontDoor Index A CKMCarrier ->
      Nonempty
        (ConcreteStandardModelHolyGrailProducerKernel
          Index A CKMCarrier) := by
  intro h
  exact
    (standardModelPoincareHolyGrailOutput_nonempty_iff_concreteKernel
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).mp
      (faithfulPoincareFrontDoor_implies_holyGrailOutput
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier) h)

/-- THEOREM 3: attaching the P462/P464 one-loop carrier receipt costs no
additional producer assumption on the faithful final front door. -/
theorem faithfulPoincareFrontDoor_implies_kernelWithOneLoop :
    PhysicallyFaithfulPoincareHolyGrailFrontDoor Index A CKMCarrier ->
      Nonempty
        (ConcreteHolyGrailKernelWithOneLoopCarrier
          Index A CKMCarrier) := by
  intro h
  exact
    (concreteKernelWithOneLoop_nonempty_iff_concreteKernel
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).mpr
      (faithfulPoincareFrontDoor_implies_concreteKernel
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier) h)

/-- THEOREM 4: compact citation form.  A faithful final front door yields the
final P419 output and the P464 one-loop provenance receipt. -/
theorem faithfulPoincareFrontDoor_outputs_holyGrail_and_oneLoopProvenance :
    PhysicallyFaithfulPoincareHolyGrailFrontDoor Index A CKMCarrier ->
      Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) ∧
        RunningSigmaBeta.OneLoopCoefficientProvenanceReceipt := by
  intro h
  exact
    ⟨faithfulPoincareFrontDoor_implies_holyGrailOutput
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier) h,
      RunningSigmaBeta.oneLoopCoefficientProvenanceReceipt⟩

/-! ## Degenerate carrier rejection at the final door -/

/-- THEOREM 5: the degenerate unit carrier cannot pass the faithful final
front door, regardless of whether a geometry certificate is supplied. -/
theorem unitCarrier_no_faithfulPoincareFrontDoor :
    ¬ PhysicallyFaithfulPoincareHolyGrailFrontDoor Unit Unit Unit := by
  rintro ⟨hfaithful, _hgeometry⟩
  exact unitCarrier_no_faithfulFrontDoor hfaithful

/-- THEOREM 6: on the unit carrier, the current single-source receipt may be
inhabited by the P448 toy kernel, but the faithful final door is impossible.

This transports P450's strictness all the way to the final Poincare/one-loop
surface. -/
theorem unitCarrier_singleSourceReceipt_without_faithfulPoincareFrontDoor :
    Nonempty (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
        Unit Unit Unit) ∧
      ¬ PhysicallyFaithfulPoincareHolyGrailFrontDoor Unit Unit Unit := by
  exact
    ⟨DegenerateKernelAudit.unitToy_singleSourcePhysicalHolyGrailReceipt,
      unitCarrier_no_faithfulPoincareFrontDoor⟩

/-- THEOREM 7: on the unit carrier, the old central constants still do not
imply the faithful final door. -/
theorem unitCarrier_currentCentral_does_not_imply_faithfulPoincareFrontDoor :
    ¬ (CurrentFormalExactGeometryCentralHolyGrailConstants Unit Unit Unit ->
        PhysicallyFaithfulPoincareHolyGrailFrontDoor Unit Unit Unit) := by
  intro h
  exact
    unitCarrier_no_faithfulPoincareFrontDoor
      (h DegenerateKernelAudit.unitToy_currentCentralHolyGrailConstants)

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
