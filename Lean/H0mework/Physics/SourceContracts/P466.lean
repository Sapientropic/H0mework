/-
  Proposition 466: final-door degeneracy audit.

  P465 introduces the faithful final front door and proves that the unit carrier
  cannot pass it.  This file proves why that strict door is still necessary:
  the ordinary P419/P463 final output can be inhabited by combining the P448
  unit toy receipt with a trivial 4D Poincare-duality geometry certificate.

  Thus the ordinary final output is a normal-form surface; the faithful final
  door is the physical-faithfulness surface.
-/

import H0mework.Physics.SourceContracts.P465

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm
namespace DegenerateFinalDoorAudit

/-! ## Trivial 4D Poincare geometry producer -/

/-- A completely collapsed 4D Poincare-duality certificate with every
cohomology carrier equal to `Unit`.

This is a valid instance of P280's abstract certificate interface, and that is
exactly the audit point: P280's geometry certificate is intentionally still a
producer obligation, not a physical manifold construction. -/
def unitPoincareDualityCohomologyCertificate :
    PoincareDualityCohomologyCertificate 4 where
  cohomology := fun _ => Unit
  duality := by
    intro k hk
    exact Equiv.refl Unit
  above_top_subsingleton := by
    intro k hk
    infer_instance

/-- THEOREM 1: the trivial Poincare certificate inhabits the 4D generation-slot
geometry interface. -/
theorem unitFourDimensionalPoincareGenerationSlotCertificate_nonempty :
    Nonempty FourDimensionalPoincareGenerationSlotCertificate := by
  exact
    ⟨{ geometry := unitPoincareDualityCohomologyCertificate }⟩

/-! ## Ordinary final output is still inhabitable by the unit toy -/

/-- THEOREM 2: the ordinary P417/P419 Poincare-resolved surface is inhabited on
the degenerate `Unit/Unit/Unit` carrier. -/
theorem unitToy_standardModelPoincareResolved_nonempty :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Unit Unit Unit := by
  exact
    (standardModelPoincareResolved_nonempty_iff_receipt_and_geometry
      (Index := Unit) (A := Unit) (CKMCarrier := Unit)).mpr
      ⟨DegenerateKernelAudit.unitToy_singleSourcePhysicalHolyGrailReceipt,
        unitFourDimensionalPoincareGenerationSlotCertificate_nonempty⟩

/-- THEOREM 3: therefore the ordinary P419 final holy-grail output is
inhabited on the degenerate `Unit/Unit/Unit` carrier. -/
theorem unitToy_standardModelPoincareHolyGrailOutput_nonempty :
    Nonempty (StandardModelPoincareHolyGrailOutput Unit Unit Unit) := by
  exact
    (standardModelPoincareResolved_nonempty_iff_holyGrailOutput
      (Index := Unit) (A := Unit) (CKMCarrier := Unit)).mp
      unitToy_standardModelPoincareResolved_nonempty

/-- THEOREM 4: the ordinary P463 kernel-with-one-loop surface is also
inhabited on the degenerate `Unit/Unit/Unit` carrier. -/
theorem unitToy_kernelWithOneLoop_nonempty :
    Nonempty
      (ConcreteHolyGrailKernelWithOneLoopCarrier Unit Unit Unit) := by
  exact
    (standardModelPoincareHolyGrailOutput_nonempty_iff_kernelWithOneLoop
      (Index := Unit) (A := Unit) (CKMCarrier := Unit)).mp
      unitToy_standardModelPoincareHolyGrailOutput_nonempty

/-! ## Strictness of the faithful final door -/

/-- THEOREM 5: ordinary final output can hold while the faithful final door is
impossible. -/
theorem unitCarrier_finalOutput_without_faithfulPoincareFrontDoor :
    Nonempty (StandardModelPoincareHolyGrailOutput Unit Unit Unit) ∧
      ¬ PhysicallyFaithfulPoincareHolyGrailFrontDoor Unit Unit Unit := by
  exact
    ⟨unitToy_standardModelPoincareHolyGrailOutput_nonempty,
      unitCarrier_no_faithfulPoincareFrontDoor⟩

/-- THEOREM 6: ordinary kernel-with-one-loop output can hold while the faithful
final door is impossible. -/
theorem unitCarrier_kernelWithOneLoop_without_faithfulPoincareFrontDoor :
    Nonempty (ConcreteHolyGrailKernelWithOneLoopCarrier Unit Unit Unit) ∧
      ¬ PhysicallyFaithfulPoincareHolyGrailFrontDoor Unit Unit Unit := by
  exact
    ⟨unitToy_kernelWithOneLoop_nonempty,
      unitCarrier_no_faithfulPoincareFrontDoor⟩

/-- THEOREM 7: on the unit carrier, ordinary final output does not imply the
faithful final door. -/
theorem unitCarrier_finalOutput_does_not_imply_faithfulPoincareFrontDoor :
    ¬ (Nonempty (StandardModelPoincareHolyGrailOutput Unit Unit Unit) ->
        PhysicallyFaithfulPoincareHolyGrailFrontDoor Unit Unit Unit) := by
  intro h
  exact
    unitCarrier_no_faithfulPoincareFrontDoor
      (h unitToy_standardModelPoincareHolyGrailOutput_nonempty)

/-- THEOREM 8: same strictness statement for P463's kernel-with-one-loop
surface. -/
theorem unitCarrier_kernelWithOneLoop_does_not_imply_faithfulPoincareFrontDoor :
    ¬ (Nonempty (ConcreteHolyGrailKernelWithOneLoopCarrier Unit Unit Unit) ->
        PhysicallyFaithfulPoincareHolyGrailFrontDoor Unit Unit Unit) := by
  intro h
  exact
    unitCarrier_no_faithfulPoincareFrontDoor
      (h unitToy_kernelWithOneLoop_nonempty)

end DegenerateFinalDoorAudit
end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
