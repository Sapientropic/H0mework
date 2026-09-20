import Mathlib.Algebra.Field.TransferInstance
import H0mework.Realization.Fibres.P551

/-!
# Proposition 552: sigma-zero relaxed fibers transport semiring, ring, and field structure

P551 packaged the zero-fiber forgetful map as `AddEquiv` and `MulEquiv`.
This file pushes the algebraic face one level higher.  Mathlib already knows
how to transport `Semiring`, `Ring`, `CommRing`, `DivisionRing`, and `Field`
structure across an equivalence.  Applying that transfer to the generic
zero-fiber equivalence proves that the annealed fiber is not merely compatible
with two binary operations: it can carry the full standard algebraic structure
pulled back from the carrier.

Boundary: this is still the `sigma = 0` annealing face.  P549 remains the
active-fiber guardrail: nonzero fibers retain headroom and are not silently
identified with the standard object.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Generic transported ring-level instances -/

/-- Transport a `Semiring` structure from `X` to the sigma-zero relaxed
fiber. -/
@[reducible] def sigmaZeroRelaxedSemiringInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Semiring X] :
    Semiring (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.semiring (sigmaZeroRelaxedEquiv K X H)

/-- Transport a `Ring` structure from `X` to the sigma-zero relaxed fiber. -/
@[reducible] def sigmaZeroRelaxedRingInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Ring X] :
    Ring (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.ring (sigmaZeroRelaxedEquiv K X H)

/-- Transport a `CommRing` structure from `X` to the sigma-zero relaxed
fiber. -/
@[reducible] def sigmaZeroRelaxedCommRingInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [CommRing X] :
    CommRing (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.commRing (sigmaZeroRelaxedEquiv K X H)

/-- Transport a `DivisionRing` structure from `X` to the sigma-zero relaxed
fiber. -/
@[reducible] def sigmaZeroRelaxedDivisionRingInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [DivisionRing X] :
    DivisionRing (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.divisionRing (sigmaZeroRelaxedEquiv K X H)

/-- Transport a `Field` structure from `X` to the sigma-zero relaxed fiber. -/
@[reducible] def sigmaZeroRelaxedFieldInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Field X] :
    Field (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.field (sigmaZeroRelaxedEquiv K X H)

/-! ## Generic ring equivalences with transported source structure -/

/-- THEOREM 1: with the transported `Semiring` structure, the zero fiber is
ring-equivalent to its standard carrier. -/
def sigmaZeroRelaxedSemiringRingEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Semiring X] : by
      letI := sigmaZeroRelaxedSemiringInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃+* X := by
  letI := sigmaZeroRelaxedSemiringInst K X H
  exact Equiv.ringEquiv (sigmaZeroRelaxedEquiv K X H)

/-- THEOREM 2: with the transported `Ring` structure, the zero fiber is
ring-equivalent to its standard carrier. -/
def sigmaZeroRelaxedRingRingEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Ring X] : by
      letI := sigmaZeroRelaxedRingInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃+* X := by
  letI := sigmaZeroRelaxedRingInst K X H
  exact Equiv.ringEquiv (sigmaZeroRelaxedEquiv K X H)

/-- THEOREM 3: with the transported `Field` structure, the zero fiber is
ring-equivalent to its standard carrier. -/
def sigmaZeroRelaxedFieldRingEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Field X] : by
      letI := sigmaZeroRelaxedFieldInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃+* X := by
  letI := sigmaZeroRelaxedFieldInst K X H
  exact Equiv.ringEquiv (sigmaZeroRelaxedEquiv K X H)

@[simp] theorem sigmaZeroRelaxedSemiringRingEquiv_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Semiring X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedSemiringInst K X H
    sigmaZeroRelaxedSemiringRingEquiv K X H z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

@[simp] theorem sigmaZeroRelaxedRingRingEquiv_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Ring X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedRingInst K X H
    sigmaZeroRelaxedRingRingEquiv K X H z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

@[simp] theorem sigmaZeroRelaxedFieldRingEquiv_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Field X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedFieldInst K X H
    sigmaZeroRelaxedFieldRingEquiv K X H z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

/-! ## Constants and unary operations are transported too -/

@[simp] theorem sigmaZeroRelaxedSemiringRingEquiv_map_zero
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Semiring X] :
    letI := sigmaZeroRelaxedSemiringInst K X H
    sigmaZeroRelaxedSemiringRingEquiv K X H 0 = (0 : X) :=
  rfl

@[simp] theorem sigmaZeroRelaxedSemiringRingEquiv_map_one
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Semiring X] :
    letI := sigmaZeroRelaxedSemiringInst K X H
    sigmaZeroRelaxedSemiringRingEquiv K X H 1 = (1 : X) :=
  rfl

@[simp] theorem sigmaZeroRelaxedRingRingEquiv_map_neg
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Ring X] :
    letI := sigmaZeroRelaxedRingInst K X H
    ∀ z : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedRingRingEquiv K X H (-z) =
        -sigmaZeroRelaxedRingRingEquiv K X H z := by
  intro z
  rfl

@[simp] theorem sigmaZeroRelaxedRingRingEquiv_map_sub
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Ring X] :
    letI := sigmaZeroRelaxedRingInst K X H
    ∀ z₁ z₂ : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedRingRingEquiv K X H (z₁ - z₂) =
        sigmaZeroRelaxedRingRingEquiv K X H z₁ -
          sigmaZeroRelaxedRingRingEquiv K X H z₂ := by
  intro z₁ z₂
  rfl

@[simp] theorem sigmaZeroRelaxedFieldRingEquiv_map_inv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Field X] :
    letI := sigmaZeroRelaxedFieldInst K X H
    ∀ z : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedFieldRingEquiv K X H z⁻¹ =
        (sigmaZeroRelaxedFieldRingEquiv K X H z)⁻¹ := by
  intro z
  rfl

@[simp] theorem sigmaZeroRelaxedFieldRingEquiv_map_div
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Field X] :
    letI := sigmaZeroRelaxedFieldInst K X H
    ∀ z₁ z₂ : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedFieldRingEquiv K X H (z₁ / z₂) =
        sigmaZeroRelaxedFieldRingEquiv K X H z₁ /
          sigmaZeroRelaxedFieldRingEquiv K X H z₂ := by
  intro z₁ z₂
  rfl

/-- Compact certificate for the generic semiring/ring/field transported
zero-fiber structures. -/
structure SigmaZeroRelaxedRingLevelCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Field X] where
  semiring_inst :
    Semiring (SigmaRelaxedObject K X H (0 : K))
  ring_inst :
    Ring (SigmaRelaxedObject K X H (0 : K))
  field_inst :
    Field (SigmaRelaxedObject K X H (0 : K))
  field_ring_equiv :
    letI := field_inst
    SigmaRelaxedObject K X H (0 : K) ≃+* X
  map_zero :
    letI := field_inst
    field_ring_equiv 0 = (0 : X)
  map_one :
    letI := field_inst
    field_ring_equiv 1 = (1 : X)
  map_inv :
    letI := field_inst
    ∀ z : SigmaRelaxedObject K X H (0 : K),
      field_ring_equiv z⁻¹ = (field_ring_equiv z)⁻¹

/-- THEOREM 4: the generic ring-level zero-fiber certificate is inhabited for
field carriers. -/
def sigmaZeroRelaxedRingLevelCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Field X] :
    SigmaZeroRelaxedRingLevelCertificate K X H where
  semiring_inst := sigmaZeroRelaxedSemiringInst K X H
  ring_inst := sigmaZeroRelaxedRingInst K X H
  field_inst := sigmaZeroRelaxedFieldInst K X H
  field_ring_equiv := by
    letI := sigmaZeroRelaxedFieldInst K X H
    exact sigmaZeroRelaxedFieldRingEquiv K X H
  map_zero := rfl
  map_one := rfl
  map_inv := by
    intro z
    rfl

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object ring-level table -/

/-- Transported `Semiring` structure on any semiring-valued core-object
zero fiber. -/
@[reducible] def coreObjectSigmaZeroSemiringInst
    (O : CoreMathematicalObject18) [Semiring (CoreObjectCarrier O)] :
    Semiring (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedSemiringInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- Transported `Ring` structure on any ring-valued core-object zero fiber. -/
@[reducible] def coreObjectSigmaZeroRingInst
    (O : CoreMathematicalObject18) [Ring (CoreObjectCarrier O)] :
    Ring (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedRingInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- Transported `Field` structure on any field-valued core-object zero fiber. -/
@[reducible] def coreObjectSigmaZeroFieldInst
    (O : CoreMathematicalObject18) [Field (CoreObjectCarrier O)] :
    Field (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedFieldInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 5: every semiring-valued core object's zero fiber is
ring-equivalent to its standard carrier under the transported semiring
structure. -/
def coreObjectSigmaZeroSemiringRingEquiv
    (O : CoreMathematicalObject18) [Semiring (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroSemiringInst O
      exact CoreObjectSigmaZeroFiber O ≃+* CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroSemiringInst O
  exact sigmaZeroRelaxedSemiringRingEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 6: every ring-valued core object's zero fiber is ring-equivalent
to its standard carrier under the transported ring structure. -/
def coreObjectSigmaZeroRingRingEquiv
    (O : CoreMathematicalObject18) [Ring (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroRingInst O
      exact CoreObjectSigmaZeroFiber O ≃+* CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroRingInst O
  exact sigmaZeroRelaxedRingRingEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 7: every field-valued core object's zero fiber is ring-equivalent
to its standard carrier under the transported field structure. -/
def coreObjectSigmaZeroFieldRingEquiv
    (O : CoreMathematicalObject18) [Field (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroFieldInst O
      exact CoreObjectSigmaZeroFiber O ≃+* CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroFieldInst O
  exact sigmaZeroRelaxedFieldRingEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[simp] theorem coreObjectSigmaZeroSemiringRingEquiv_map_zero
    (O : CoreMathematicalObject18) [Semiring (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroSemiringInst O
    coreObjectSigmaZeroSemiringRingEquiv O 0 =
      (0 : CoreObjectCarrier O) :=
  rfl

@[simp] theorem coreObjectSigmaZeroSemiringRingEquiv_map_one
    (O : CoreMathematicalObject18) [Semiring (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroSemiringInst O
    coreObjectSigmaZeroSemiringRingEquiv O 1 =
      (1 : CoreObjectCarrier O) :=
  rfl

@[simp] theorem coreObjectSigmaZeroRingRingEquiv_map_neg
    (O : CoreMathematicalObject18) [Ring (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroRingInst O
    ∀ z : CoreObjectSigmaZeroFiber O,
      coreObjectSigmaZeroRingRingEquiv O (-z) =
        -coreObjectSigmaZeroRingRingEquiv O z := by
  intro z
  rfl

@[simp] theorem coreObjectSigmaZeroFieldRingEquiv_map_inv
    (O : CoreMathematicalObject18) [Field (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroFieldInst O
    ∀ z : CoreObjectSigmaZeroFiber O,
      coreObjectSigmaZeroFieldRingEquiv O z⁻¹ =
        (coreObjectSigmaZeroFieldRingEquiv O z)⁻¹ := by
  intro z
  rfl

/-- Table certificate: the zero-fiber table now includes transported
semiring/ring/field structures for every core carrier where Mathlib supplies
the corresponding standard instance. -/
structure CoreObjectSigmaZeroRingLevelTableCertificate where
  algebra_table :
    CoreObjectSigmaZeroAlgebraEquivTableCertificate
  semiring_inst :
    ∀ (O : CoreMathematicalObject18) [Semiring (CoreObjectCarrier O)],
      Semiring (CoreObjectSigmaZeroFiber O)
  ring_inst :
    ∀ (O : CoreMathematicalObject18) [Ring (CoreObjectCarrier O)],
      Ring (CoreObjectSigmaZeroFiber O)
  field_inst :
    ∀ (O : CoreMathematicalObject18) [Field (CoreObjectCarrier O)],
      Field (CoreObjectSigmaZeroFiber O)
  semiring_ring_equiv :
    ∀ (O : CoreMathematicalObject18) [Semiring (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroSemiringInst O
      CoreObjectSigmaZeroFiber O ≃+* CoreObjectCarrier O
  ring_ring_equiv :
    ∀ (O : CoreMathematicalObject18) [Ring (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroRingInst O
      CoreObjectSigmaZeroFiber O ≃+* CoreObjectCarrier O
  field_ring_equiv :
    ∀ (O : CoreMathematicalObject18) [Field (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroFieldInst O
      CoreObjectSigmaZeroFiber O ≃+* CoreObjectCarrier O

/-- THEOREM 8: the core-object ring-level table is inhabited. -/
def coreObjectSigmaZeroRingLevelTableCertificate :
    CoreObjectSigmaZeroRingLevelTableCertificate where
  algebra_table := coreObjectSigmaZeroAlgebraEquivTableCertificate
  semiring_inst := by
    intro O _inst
    exact coreObjectSigmaZeroSemiringInst O
  ring_inst := by
    intro O _inst
    exact coreObjectSigmaZeroRingInst O
  field_inst := by
    intro O _inst
    exact coreObjectSigmaZeroFieldInst O
  semiring_ring_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroSemiringRingEquiv O
  ring_ring_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroRingRingEquiv O
  field_ring_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroFieldRingEquiv O

end SaturationMonoid
