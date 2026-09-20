import H0mework.Physics.JointSources.P633

/-!
# Proposition 634: singleton primitive source surface

P633 lowered the one-axis source law to a primitive producer object carrying
QCD input, spacetime dimension, and the axis equation.  This file removes the
remaining object-level freedom on that surface.

Lean proves every `OneAxisPrimitiveSourceProducer` is equal to the canonical
one.  Therefore the primitive surface is a singleton (equivalent to `Unit`),
and every accepted primitive producer inherits the same P633/P632 three-nail
receipt.

Boundary: singleton closure is for the already named primitive fields.  The
upstream physical task remains to produce those fields from smooth SU(7)
breaking / threshold / Higgs-spectrum / RG dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Singleton closure of the primitive producer surface -/

/-- THEOREM 1: every primitive source producer is the canonical one. -/
theorem oneAxisPrimitiveSourceProducer_eq_canonical
    (P : OneAxisPrimitiveSourceProducer) :
    P = canonicalOneAxisPrimitiveSourceProducer := by
  cases P with
  | mk qcdInput spacetimeDimension axis qcd_input_eq
      spacetime_dimension_eq axis_eq_source =>
      cases qcd_input_eq
      cases spacetime_dimension_eq
      cases axis_eq_source
      rfl

/-- THEOREM 2: the primitive source-producer surface is a subsingleton. -/
theorem oneAxisPrimitiveSourceProducer_subsingleton :
    Subsingleton OneAxisPrimitiveSourceProducer := by
  refine ⟨?_⟩
  intro P Q
  rw [oneAxisPrimitiveSourceProducer_eq_canonical P,
    oneAxisPrimitiveSourceProducer_eq_canonical Q]

/-- THEOREM 3: the primitive surface is equivalent to `Unit`. -/
def oneAxisPrimitiveSourceProducerEquivUnit :
    OneAxisPrimitiveSourceProducer ≃ Unit where
  toFun _ := ()
  invFun _ := canonicalOneAxisPrimitiveSourceProducer
  left_inv := by
    intro P
    exact (oneAxisPrimitiveSourceProducer_eq_canonical P).symm
  right_inv := by
    intro u
    cases u
    rfl

/-- THEOREM 4: every primitive receipt is transported from the canonical
producer. -/
theorem oneAxisPrimitiveSourceProducer_receipt_eq_canonical
    (P : OneAxisPrimitiveSourceProducer) :
    HEq (oneAxisPrimitiveSourceProducerReceipt P)
      canonicalOneAxisPrimitiveSourceProducerReceipt := by
  cases oneAxisPrimitiveSourceProducer_eq_canonical P
  rfl

/-! ## Bundled current root -/

/-- The current one-axis primitive-source core: there is a unique primitive
source producer and it carries the full three-nail receipt. -/
structure CurrentUnifiedEquationOneAxisPrimitiveSourceCoreCertificate where
  producer_surface_singleton :
    Subsingleton OneAxisPrimitiveSourceProducer
  producer_equiv_unit :
    OneAxisPrimitiveSourceProducer ≃ Unit
  canonical_receipt :
    OneAxisPrimitiveSourceProducerReceipt
      canonicalOneAxisPrimitiveSourceProducer
  all_producers_equal_canonical :
    ∀ P : OneAxisPrimitiveSourceProducer,
      P = canonicalOneAxisPrimitiveSourceProducer
  every_producer_receipt :
    ∀ P : OneAxisPrimitiveSourceProducer,
      OneAxisPrimitiveSourceProducerReceipt P

/-- THEOREM 5: current primitive-source core certificate. -/
def currentUnifiedEquationOneAxisPrimitiveSourceCoreCertificate :
    CurrentUnifiedEquationOneAxisPrimitiveSourceCoreCertificate where
  producer_surface_singleton := oneAxisPrimitiveSourceProducer_subsingleton
  producer_equiv_unit := oneAxisPrimitiveSourceProducerEquivUnit
  canonical_receipt := canonicalOneAxisPrimitiveSourceProducerReceipt
  all_producers_equal_canonical :=
    oneAxisPrimitiveSourceProducer_eq_canonical
  every_producer_receipt := oneAxisPrimitiveSourceProducerReceipt

end StandardModelConstraint
end SaturationMonoid
