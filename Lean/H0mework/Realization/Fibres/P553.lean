import Mathlib.Algebra.Group.TransferInstance
import H0mework.Realization.Fibres.P552

/-!
# Proposition 553: sigma-zero relaxed fibers transport monoid and group structure

P552 transported semiring/ring/field structure across the zero-fiber
equivalence.  This file closes the parallel group face: monoids, groups,
commutative groups, and their additive variants are transported to the
sigma-zero relaxed fiber, and the forgetful map becomes a genuine `MulEquiv`
or `AddEquiv` preserving units, inverses, division, zeros, negation, and
subtraction.

This matters for the eighteen-object table because `.groups` is represented
by a standard group carrier.  The result says that the group object is also a
zero-fiber specialization, not merely a set-level shadow.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Generic multiplicative transfer -/

@[reducible] def sigmaZeroRelaxedMonoidInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Monoid X] :
    Monoid (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.monoid (sigmaZeroRelaxedEquiv K X H)

@[reducible] def sigmaZeroRelaxedCommMonoidInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [CommMonoid X] :
    CommMonoid (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.commMonoid (sigmaZeroRelaxedEquiv K X H)

@[reducible] def sigmaZeroRelaxedGroupInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Group X] :
    Group (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.group (sigmaZeroRelaxedEquiv K X H)

@[reducible] def sigmaZeroRelaxedCommGroupInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [CommGroup X] :
    CommGroup (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.commGroup (sigmaZeroRelaxedEquiv K X H)

/-- THEOREM 1: monoid-valued zero fibers are multiplicatively equivalent to
their standard carriers. -/
def sigmaZeroRelaxedMonoidMulEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Monoid X] : by
      letI := sigmaZeroRelaxedMonoidInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃* X := by
  letI := sigmaZeroRelaxedMonoidInst K X H
  exact Equiv.mulEquiv (sigmaZeroRelaxedEquiv K X H)

/-- THEOREM 2: group-valued zero fibers are multiplicatively equivalent to
their standard carriers. -/
def sigmaZeroRelaxedGroupMulEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Group X] : by
      letI := sigmaZeroRelaxedGroupInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃* X := by
  letI := sigmaZeroRelaxedGroupInst K X H
  exact Equiv.mulEquiv (sigmaZeroRelaxedEquiv K X H)

@[simp] theorem sigmaZeroRelaxedMonoidMulEquiv_map_one
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Monoid X] :
    letI := sigmaZeroRelaxedMonoidInst K X H
    sigmaZeroRelaxedMonoidMulEquiv K X H 1 = (1 : X) :=
  rfl

@[simp] theorem sigmaZeroRelaxedGroupMulEquiv_map_inv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Group X] :
    letI := sigmaZeroRelaxedGroupInst K X H
    ∀ z : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedGroupMulEquiv K X H z⁻¹ =
        (sigmaZeroRelaxedGroupMulEquiv K X H z)⁻¹ := by
  intro z
  rfl

@[simp] theorem sigmaZeroRelaxedGroupMulEquiv_map_div
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Group X] :
    letI := sigmaZeroRelaxedGroupInst K X H
    ∀ z₁ z₂ : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedGroupMulEquiv K X H (z₁ / z₂) =
        sigmaZeroRelaxedGroupMulEquiv K X H z₁ /
          sigmaZeroRelaxedGroupMulEquiv K X H z₂ := by
  intro z₁ z₂
  rfl

/-! ## Generic additive transfer -/

@[reducible] def sigmaZeroRelaxedAddMonoidInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddMonoid X] :
    AddMonoid (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.addMonoid (sigmaZeroRelaxedEquiv K X H)

@[reducible] def sigmaZeroRelaxedAddCommMonoidInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddCommMonoid X] :
    AddCommMonoid (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.addCommMonoid (sigmaZeroRelaxedEquiv K X H)

@[reducible] def sigmaZeroRelaxedAddGroupInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddGroup X] :
    AddGroup (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.addGroup (sigmaZeroRelaxedEquiv K X H)

@[reducible] def sigmaZeroRelaxedAddCommGroupInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddCommGroup X] :
    AddCommGroup (SigmaRelaxedObject K X H (0 : K)) :=
  Equiv.addCommGroup (sigmaZeroRelaxedEquiv K X H)

/-- THEOREM 3: additive-monoid-valued zero fibers are additively equivalent
to their standard carriers. -/
def sigmaZeroRelaxedAddMonoidAddEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddMonoid X] : by
      letI := sigmaZeroRelaxedAddMonoidInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃+ X := by
  letI := sigmaZeroRelaxedAddMonoidInst K X H
  exact Equiv.addEquiv (sigmaZeroRelaxedEquiv K X H)

/-- THEOREM 4: additive-group-valued zero fibers are additively equivalent to
their standard carriers. -/
def sigmaZeroRelaxedAddGroupAddEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddGroup X] : by
      letI := sigmaZeroRelaxedAddGroupInst K X H
      exact SigmaRelaxedObject K X H (0 : K) ≃+ X := by
  letI := sigmaZeroRelaxedAddGroupInst K X H
  exact Equiv.addEquiv (sigmaZeroRelaxedEquiv K X H)

@[simp] theorem sigmaZeroRelaxedAddMonoidAddEquiv_map_zero
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddMonoid X] :
    letI := sigmaZeroRelaxedAddMonoidInst K X H
    sigmaZeroRelaxedAddMonoidAddEquiv K X H 0 = (0 : X) :=
  rfl

@[simp] theorem sigmaZeroRelaxedAddGroupAddEquiv_map_neg
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddGroup X] :
    letI := sigmaZeroRelaxedAddGroupInst K X H
    ∀ z : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedAddGroupAddEquiv K X H (-z) =
        -sigmaZeroRelaxedAddGroupAddEquiv K X H z := by
  intro z
  rfl

@[simp] theorem sigmaZeroRelaxedAddGroupAddEquiv_map_sub
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [AddGroup X] :
    letI := sigmaZeroRelaxedAddGroupInst K X H
    ∀ z₁ z₂ : SigmaRelaxedObject K X H (0 : K),
      sigmaZeroRelaxedAddGroupAddEquiv K X H (z₁ - z₂) =
        sigmaZeroRelaxedAddGroupAddEquiv K X H z₁ -
          sigmaZeroRelaxedAddGroupAddEquiv K X H z₂ := by
  intro z₁ z₂
  rfl

/-- Compact certificate for the generic group-level zero-fiber structures. -/
structure SigmaZeroRelaxedGroupLevelCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [CommGroup X] [AddCommGroup X] where
  comm_group_inst :
    CommGroup (SigmaRelaxedObject K X H (0 : K))
  add_comm_group_inst :
    AddCommGroup (SigmaRelaxedObject K X H (0 : K))
  mul_equiv :
    letI := comm_group_inst
    SigmaRelaxedObject K X H (0 : K) ≃* X
  add_equiv :
    letI := add_comm_group_inst
    SigmaRelaxedObject K X H (0 : K) ≃+ X
  map_one :
    letI := comm_group_inst
    mul_equiv 1 = (1 : X)
  map_zero :
    letI := add_comm_group_inst
    add_equiv 0 = (0 : X)

/-- THEOREM 5: the generic group-level zero-fiber certificate is inhabited
for carriers that carry both commutative multiplicative and additive group
structure. -/
def sigmaZeroRelaxedGroupLevelCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [CommGroup X] [AddCommGroup X] :
    SigmaZeroRelaxedGroupLevelCertificate K X H where
  comm_group_inst := sigmaZeroRelaxedCommGroupInst K X H
  add_comm_group_inst := sigmaZeroRelaxedAddCommGroupInst K X H
  mul_equiv := by
    letI := sigmaZeroRelaxedCommGroupInst K X H
    exact sigmaZeroRelaxedGroupMulEquiv K X H
  add_equiv := by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    exact sigmaZeroRelaxedAddGroupAddEquiv K X H
  map_one := rfl
  map_zero := rfl

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object group-level table -/

@[reducible] def coreObjectSigmaZeroMonoidInst
    (O : CoreMathematicalObject18) [Monoid (CoreObjectCarrier O)] :
    Monoid (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedMonoidInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroGroupInst
    (O : CoreMathematicalObject18) [Group (CoreObjectCarrier O)] :
    Group (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedGroupInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroAddMonoidInst
    (O : CoreMathematicalObject18) [AddMonoid (CoreObjectCarrier O)] :
    AddMonoid (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedAddMonoidInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[reducible] def coreObjectSigmaZeroAddGroupInst
    (O : CoreMathematicalObject18) [AddGroup (CoreObjectCarrier O)] :
    AddGroup (CoreObjectSigmaZeroFiber O) :=
  sigmaZeroRelaxedAddGroupInst
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

def coreObjectSigmaZeroMonoidMulEquiv
    (O : CoreMathematicalObject18) [Monoid (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroMonoidInst O
      exact CoreObjectSigmaZeroFiber O ≃* CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroMonoidInst O
  exact sigmaZeroRelaxedMonoidMulEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

def coreObjectSigmaZeroGroupMulEquiv
    (O : CoreMathematicalObject18) [Group (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroGroupInst O
      exact CoreObjectSigmaZeroFiber O ≃* CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroGroupInst O
  exact sigmaZeroRelaxedGroupMulEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

def coreObjectSigmaZeroAddMonoidAddEquiv
    (O : CoreMathematicalObject18) [AddMonoid (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddMonoidInst O
      exact CoreObjectSigmaZeroFiber O ≃+ CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroAddMonoidInst O
  exact sigmaZeroRelaxedAddMonoidAddEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

def coreObjectSigmaZeroAddGroupAddEquiv
    (O : CoreMathematicalObject18) [AddGroup (CoreObjectCarrier O)] : by
      letI := coreObjectSigmaZeroAddGroupInst O
      exact CoreObjectSigmaZeroFiber O ≃+ CoreObjectCarrier O := by
  letI := coreObjectSigmaZeroAddGroupInst O
  exact sigmaZeroRelaxedAddGroupAddEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[simp] theorem coreObjectSigmaZeroMonoidMulEquiv_map_one
    (O : CoreMathematicalObject18) [Monoid (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroMonoidInst O
    coreObjectSigmaZeroMonoidMulEquiv O 1 =
      (1 : CoreObjectCarrier O) :=
  rfl

@[simp] theorem coreObjectSigmaZeroGroupMulEquiv_map_inv
    (O : CoreMathematicalObject18) [Group (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroGroupInst O
    ∀ z : CoreObjectSigmaZeroFiber O,
      coreObjectSigmaZeroGroupMulEquiv O z⁻¹ =
        (coreObjectSigmaZeroGroupMulEquiv O z)⁻¹ := by
  intro z
  rfl

@[simp] theorem coreObjectSigmaZeroAddMonoidAddEquiv_map_zero
    (O : CoreMathematicalObject18) [AddMonoid (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroAddMonoidInst O
    coreObjectSigmaZeroAddMonoidAddEquiv O 0 =
      (0 : CoreObjectCarrier O) :=
  rfl

@[simp] theorem coreObjectSigmaZeroAddGroupAddEquiv_map_neg
    (O : CoreMathematicalObject18) [AddGroup (CoreObjectCarrier O)] :
    letI := coreObjectSigmaZeroAddGroupInst O
    ∀ z : CoreObjectSigmaZeroFiber O,
      coreObjectSigmaZeroAddGroupAddEquiv O (-z) =
        -coreObjectSigmaZeroAddGroupAddEquiv O z := by
  intro z
  rfl

/-- Table certificate: group and additive-group structures are transported to
every core-object zero fiber whose standard carrier has the corresponding
Mathlib instance. -/
structure CoreObjectSigmaZeroGroupLevelTableCertificate where
  ring_level_table :
    CoreObjectSigmaZeroRingLevelTableCertificate
  monoid_inst :
    ∀ (O : CoreMathematicalObject18) [Monoid (CoreObjectCarrier O)],
      Monoid (CoreObjectSigmaZeroFiber O)
  group_inst :
    ∀ (O : CoreMathematicalObject18) [Group (CoreObjectCarrier O)],
      Group (CoreObjectSigmaZeroFiber O)
  add_monoid_inst :
    ∀ (O : CoreMathematicalObject18) [AddMonoid (CoreObjectCarrier O)],
      AddMonoid (CoreObjectSigmaZeroFiber O)
  add_group_inst :
    ∀ (O : CoreMathematicalObject18) [AddGroup (CoreObjectCarrier O)],
      AddGroup (CoreObjectSigmaZeroFiber O)
  monoid_mul_equiv :
    ∀ (O : CoreMathematicalObject18) [Monoid (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroMonoidInst O
      CoreObjectSigmaZeroFiber O ≃* CoreObjectCarrier O
  add_monoid_add_equiv :
    ∀ (O : CoreMathematicalObject18) [AddMonoid (CoreObjectCarrier O)],
      letI := coreObjectSigmaZeroAddMonoidInst O
      CoreObjectSigmaZeroFiber O ≃+ CoreObjectCarrier O

/-- THEOREM 6: the core-object group-level table is inhabited. -/
def coreObjectSigmaZeroGroupLevelTableCertificate :
    CoreObjectSigmaZeroGroupLevelTableCertificate where
  ring_level_table := coreObjectSigmaZeroRingLevelTableCertificate
  monoid_inst := by
    intro O _inst
    exact coreObjectSigmaZeroMonoidInst O
  group_inst := by
    intro O _inst
    exact coreObjectSigmaZeroGroupInst O
  add_monoid_inst := by
    intro O _inst
    exact coreObjectSigmaZeroAddMonoidInst O
  add_group_inst := by
    intro O _inst
    exact coreObjectSigmaZeroAddGroupInst O
  monoid_mul_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroMonoidMulEquiv O
  add_monoid_add_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroAddMonoidAddEquiv O

end SaturationMonoid
