import H0mework.Realization.Fibres.P550

/-!
# Proposition 551: sigma-zero relaxed fibers preserve algebraic structure

P547/P548 proved that the sigma-zero fiber is equivalent to its standard
carrier and that arbitrary unary/binary operations can be pushed forward.
P550 strengthened the topological face to a genuine `Homeomorph`.

This file does the same for the basic algebraic faces supplied by Mathlib:
if the standard carrier has an additive or multiplicative operation, then the
sigma-zero relaxed fiber carries the transported operation and the forgetful
map is a genuine `AddEquiv` or `MulEquiv`.

Boundary: this is still the annealed `sigma = 0` statement.  P549 proves why
the same collapse is not available for active nonzero fibers: away from zero,
the headroom coordinate remains real structure.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Generic additive and multiplicative zero-fiber structure -/

/-- The additive operation transported from `X` to the sigma-zero fiber.

This is deliberately a reducible local instance value rather than a global
instance for all relaxed objects.  It describes the annealed zero face only,
and avoids pretending that active nonzero fibers automatically inherit the
same collapsed operation. -/
@[reducible] def sigmaZeroRelaxedAddInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X] :
    Add (SigmaRelaxedObject K X H (0 : K)) where
  add := sigmaZeroLiftBinary (K := K) (H := H) (fun x y : X => x + y)

/-- The multiplicative operation transported from `X` to the sigma-zero
fiber. -/
@[reducible] def sigmaZeroRelaxedMulInst
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Mul X] :
    Mul (SigmaRelaxedObject K X H (0 : K)) where
  mul := sigmaZeroLiftBinary (K := K) (H := H) (fun x y : X => x * y)

/-- THEOREM 1: if `X` has addition, then its sigma-zero fiber is additively
equivalent to `X`. -/
def sigmaZeroRelaxedAddEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X] :
    @AddEquiv
      (SigmaRelaxedObject K X H (0 : K)) X
      (sigmaZeroRelaxedAddInst K X H) inferInstance :=
  @AddEquiv.mk
    (SigmaRelaxedObject K X H (0 : K)) X
    (sigmaZeroRelaxedAddInst K X H) inferInstance
    (sigmaZeroRelaxedEquiv K X H)
    (by
      intro a b
      rfl)

/-- THEOREM 2: if `X` has multiplication, then its sigma-zero fiber is
multiplicatively equivalent to `X`. -/
def sigmaZeroRelaxedMulEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Mul X] :
    @MulEquiv
      (SigmaRelaxedObject K X H (0 : K)) X
      (sigmaZeroRelaxedMulInst K X H) inferInstance :=
  @MulEquiv.mk
    (SigmaRelaxedObject K X H (0 : K)) X
    (sigmaZeroRelaxedMulInst K X H) inferInstance
    (sigmaZeroRelaxedEquiv K X H)
    (by
      intro a b
      rfl)

@[simp] theorem sigmaZeroRelaxedAddEquiv_toEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X] :
    @AddEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedAddInst K X H) inferInstance
        (sigmaZeroRelaxedAddEquiv K X H) =
      sigmaZeroRelaxedEquiv K X H :=
  rfl

@[simp] theorem sigmaZeroRelaxedMulEquiv_toEquiv
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Mul X] :
    @MulEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedMulInst K X H) inferInstance
        (sigmaZeroRelaxedMulEquiv K X H) =
      sigmaZeroRelaxedEquiv K X H :=
  rfl

@[simp] theorem sigmaZeroRelaxedAddEquiv_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    (@AddEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedAddInst K X H) inferInstance
        (sigmaZeroRelaxedAddEquiv K X H)) z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

@[simp] theorem sigmaZeroRelaxedMulEquiv_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Mul X]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    (@MulEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedMulInst K X H) inferInstance
        (sigmaZeroRelaxedMulEquiv K X H)) z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

@[simp] theorem sigmaZeroRelaxedAddEquiv_symm_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X] (x : X) :
    (@AddEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedAddInst K X H) inferInstance
        (sigmaZeroRelaxedAddEquiv K X H)).symm x =
      sigmaZeroEmbed (K := K) (X := X) (H := H) x :=
  rfl

@[simp] theorem sigmaZeroRelaxedMulEquiv_symm_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Mul X] (x : X) :
    (@MulEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedMulInst K X H) inferInstance
        (sigmaZeroRelaxedMulEquiv K X H)).symm x =
      sigmaZeroEmbed (K := K) (X := X) (H := H) x :=
  rfl

@[simp] theorem sigmaZeroRelaxedAddEquiv_map_add_explicit
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X]
    (a b : SigmaRelaxedObject K X H (0 : K)) :
    (@AddEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedAddInst K X H) inferInstance
        (sigmaZeroRelaxedAddEquiv K X H))
        ((sigmaZeroRelaxedAddInst K X H).add a b) =
      (@AddEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedAddInst K X H) inferInstance
        (sigmaZeroRelaxedAddEquiv K X H)) a +
        (@AddEquiv.toEquiv
          (SigmaRelaxedObject K X H (0 : K)) X
          (sigmaZeroRelaxedAddInst K X H) inferInstance
          (sigmaZeroRelaxedAddEquiv K X H)) b :=
  rfl

@[simp] theorem sigmaZeroRelaxedMulEquiv_map_mul_explicit
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Mul X]
    (a b : SigmaRelaxedObject K X H (0 : K)) :
    (@MulEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedMulInst K X H) inferInstance
        (sigmaZeroRelaxedMulEquiv K X H))
        ((sigmaZeroRelaxedMulInst K X H).mul a b) =
      (@MulEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedMulInst K X H) inferInstance
        (sigmaZeroRelaxedMulEquiv K X H)) a *
        (@MulEquiv.toEquiv
          (SigmaRelaxedObject K X H (0 : K)) X
          (sigmaZeroRelaxedMulInst K X H) inferInstance
          (sigmaZeroRelaxedMulEquiv K X H)) b :=
  rfl

/-- Compact generic algebra certificate for carriers with both additive and
multiplicative structure. -/
structure SigmaZeroRelaxedAlgebraEquivCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X] [Mul X] where
  add_equiv :
    @AddEquiv
      (SigmaRelaxedObject K X H (0 : K)) X
      (sigmaZeroRelaxedAddInst K X H) inferInstance
  mul_equiv :
    @MulEquiv
      (SigmaRelaxedObject K X H (0 : K)) X
      (sigmaZeroRelaxedMulInst K X H) inferInstance
  add_to_equiv :
    @AddEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedAddInst K X H) inferInstance
        add_equiv =
      sigmaZeroRelaxedEquiv K X H
  mul_to_equiv :
    @MulEquiv.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedMulInst K X H) inferInstance
        mul_equiv =
      sigmaZeroRelaxedEquiv K X H

/-- THEOREM 3: the generic sigma-zero algebra certificate. -/
def sigmaZeroRelaxedAlgebraEquivCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [Inhabited H] [Add X] [Mul X] :
    SigmaZeroRelaxedAlgebraEquivCertificate K X H where
  add_equiv := sigmaZeroRelaxedAddEquiv K X H
  mul_equiv := sigmaZeroRelaxedMulEquiv K X H
  add_to_equiv := rfl
  mul_to_equiv := rfl

end AffineRelaxation

open AffineRelaxation

/-! ## Core-object algebra table -/

/-- THEOREM 4: any core object whose carrier has addition receives a
sigma-zero additive equivalence. -/
def coreObjectSigmaZeroAddEquiv
    (O : CoreMathematicalObject18) [Add (CoreObjectCarrier O)] :
    @AddEquiv
      (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
      (sigmaZeroRelaxedAddInst
        ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
      inferInstance :=
  sigmaZeroRelaxedAddEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

/-- THEOREM 5: any core object whose carrier has multiplication receives a
sigma-zero multiplicative equivalence. -/
def coreObjectSigmaZeroMulEquiv
    (O : CoreMathematicalObject18) [Mul (CoreObjectCarrier O)] :
    @MulEquiv
      (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
      (sigmaZeroRelaxedMulInst
        ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
      inferInstance :=
  sigmaZeroRelaxedMulEquiv
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[simp] theorem coreObjectSigmaZeroAddEquiv_toEquiv
    (O : CoreMathematicalObject18) [Add (CoreObjectCarrier O)] :
    @AddEquiv.toEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedAddInst
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
        inferInstance
        (coreObjectSigmaZeroAddEquiv O) =
      coreObjectSigmaZeroEquiv O :=
  rfl

@[simp] theorem coreObjectSigmaZeroMulEquiv_toEquiv
    (O : CoreMathematicalObject18) [Mul (CoreObjectCarrier O)] :
    @MulEquiv.toEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedMulInst
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
        inferInstance
        (coreObjectSigmaZeroMulEquiv O) =
      coreObjectSigmaZeroEquiv O :=
  rfl

@[simp] theorem coreObjectSigmaZeroAddEquiv_apply
    (O : CoreMathematicalObject18) [Add (CoreObjectCarrier O)]
    (z : CoreObjectSigmaZeroFiber O) :
    (@AddEquiv.toEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedAddInst
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
        inferInstance
        (coreObjectSigmaZeroAddEquiv O)) z =
      coreObjectSigmaZeroForget O z :=
  rfl

@[simp] theorem coreObjectSigmaZeroMulEquiv_apply
    (O : CoreMathematicalObject18) [Mul (CoreObjectCarrier O)]
    (z : CoreObjectSigmaZeroFiber O) :
    (@MulEquiv.toEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedMulInst
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
        inferInstance
        (coreObjectSigmaZeroMulEquiv O)) z =
      coreObjectSigmaZeroForget O z :=
  rfl

/-- Table certificate: the eighteen-object zero-fiber table now carries
topological equivalences and all additive/multiplicative equivalences available
from the carrier's standard Mathlib structure. -/
structure CoreObjectSigmaZeroAlgebraEquivTableCertificate where
  homeomorph_table :
    CoreObjectSigmaZeroHomeomorphTableCertificate
  add_equiv :
    ∀ (O : CoreMathematicalObject18) [Add (CoreObjectCarrier O)],
      @AddEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedAddInst
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
        inferInstance
  mul_equiv :
    ∀ (O : CoreMathematicalObject18) [Mul (CoreObjectCarrier O)],
      @MulEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedMulInst
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
        inferInstance
  add_to_equiv :
    ∀ (O : CoreMathematicalObject18) [Add (CoreObjectCarrier O)],
      @AddEquiv.toEquiv
          (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
          (sigmaZeroRelaxedAddInst
            ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
          inferInstance
          (add_equiv O) =
        coreObjectSigmaZeroEquiv O
  mul_to_equiv :
    ∀ (O : CoreMathematicalObject18) [Mul (CoreObjectCarrier O)],
      @MulEquiv.toEquiv
          (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
          (sigmaZeroRelaxedMulInst
            ℝ (CoreObjectCarrier O) CoreObjectHeadroom)
          inferInstance
          (mul_equiv O) =
        coreObjectSigmaZeroEquiv O

/-- THEOREM 6: the core-object algebra equivalence table is inhabited. -/
def coreObjectSigmaZeroAlgebraEquivTableCertificate :
    CoreObjectSigmaZeroAlgebraEquivTableCertificate where
  homeomorph_table := coreObjectSigmaZeroHomeomorphTableCertificate
  add_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroAddEquiv O
  mul_equiv := by
    intro O _inst
    exact coreObjectSigmaZeroMulEquiv O
  add_to_equiv := by
    intro O _inst
    rfl
  mul_to_equiv := by
    intro O _inst
    rfl

end SaturationMonoid
