import H0mework.Realization.Fibres.P549

/-!
# Proposition 550: sigma-zero relaxed fibers are genuine homeomorphs

P547 equipped the zero fiber with the topology induced by the forgetful map
and proved both directions continuous.  P548 transported that topology
certificate to the eighteen-object table.

This file packages the same fact in Mathlib's standard topological-isomorphism
type `≃ₜ`.  The point is small but important: the zero fiber is not merely
set-equivalent to the standard object with two continuous maps written nearby;
it is a genuine homeomorphic specialization.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-- THEOREM 1: the zero fiber, with the induced topology from P547, is
homeomorphic to the standard object. -/
def sigmaZeroRelaxedHomeomorph
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] :
    @Homeomorph
      (SigmaRelaxedObject K X H (0 : K)) X
      (sigmaZeroRelaxedTopology K X H) inferInstance :=
  @Homeomorph.mk
    (SigmaRelaxedObject K X H (0 : K)) X
    (sigmaZeroRelaxedTopology K X H) inferInstance
    (sigmaZeroRelaxedEquiv K X H)
    (continuous_sigmaZeroForget_induced K X H)
    (continuous_sigmaZeroEmbed_induced K X H)

@[simp] theorem sigmaZeroRelaxedHomeomorph_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H]
    (z : SigmaRelaxedObject K X H (0 : K)) :
    (@Homeomorph.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedTopology K X H) inferInstance
        (sigmaZeroRelaxedHomeomorph K X H)) z =
      sigmaZeroForget (K := K) (X := X) (H := H) z :=
  rfl

@[simp] theorem sigmaZeroRelaxedHomeomorph_symm_apply
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] (x : X) :
    (@Homeomorph.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedTopology K X H) inferInstance
        (sigmaZeroRelaxedHomeomorph K X H)).symm x =
      sigmaZeroEmbed (K := K) (X := X) (H := H) x :=
  rfl

/-- Compact generic homeomorphism certificate for the sigma-zero fiber. -/
structure SigmaZeroRelaxedHomeomorphCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] where
  homeomorph :
    @Homeomorph
      (SigmaRelaxedObject K X H (0 : K)) X
      (sigmaZeroRelaxedTopology K X H) inferInstance
  to_equiv :
    @Homeomorph.toEquiv
        (SigmaRelaxedObject K X H (0 : K)) X
        (sigmaZeroRelaxedTopology K X H) inferInstance
        homeomorph =
      sigmaZeroRelaxedEquiv K X H
  forget_apply :
    ∀ z : SigmaRelaxedObject K X H (0 : K),
      (@Homeomorph.toEquiv
          (SigmaRelaxedObject K X H (0 : K)) X
          (sigmaZeroRelaxedTopology K X H) inferInstance
          homeomorph) z =
        sigmaZeroForget (K := K) (X := X) (H := H) z
  embed_symm_apply :
    ∀ x : X,
      (@Homeomorph.toEquiv
          (SigmaRelaxedObject K X H (0 : K)) X
          (sigmaZeroRelaxedTopology K X H) inferInstance
          homeomorph).symm x =
        sigmaZeroEmbed (K := K) (X := X) (H := H) x

/-- THEOREM 2: the generic sigma-zero homeomorphism certificate. -/
def sigmaZeroRelaxedHomeomorphCertificate
    (K : Type u) [Zero K] (X : Type v) (H : Type w)
    [TopologicalSpace X] [Inhabited H] :
    SigmaZeroRelaxedHomeomorphCertificate K X H where
  homeomorph := sigmaZeroRelaxedHomeomorph K X H
  to_equiv := rfl
  forget_apply := by
    intro z
    rfl
  embed_symm_apply := by
    intro x
    rfl

end AffineRelaxation

open AffineRelaxation

/-! ## The eighteen-object homeomorphism table -/

/-- THEOREM 3: every core object's sigma-zero fiber is homeomorphic to its
standard carrier. -/
def coreObjectSigmaZeroHomeomorph
    (O : CoreMathematicalObject18) :
    @Homeomorph
      (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
      (sigmaZeroRelaxedTopology
        ℝ (CoreObjectCarrier O) CoreObjectHeadroom) inferInstance :=
  sigmaZeroRelaxedHomeomorph
    ℝ (CoreObjectCarrier O) CoreObjectHeadroom

@[simp] theorem coreObjectSigmaZeroHomeomorph_apply
    (O : CoreMathematicalObject18)
    (z : CoreObjectSigmaZeroFiber O) :
    (@Homeomorph.toEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedTopology
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom) inferInstance
        (coreObjectSigmaZeroHomeomorph O)) z =
      coreObjectSigmaZeroForget O z :=
  rfl

@[simp] theorem coreObjectSigmaZeroHomeomorph_symm_apply
    (O : CoreMathematicalObject18)
    (x : CoreObjectCarrier O) :
    (@Homeomorph.toEquiv
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedTopology
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom) inferInstance
        (coreObjectSigmaZeroHomeomorph O)).symm x =
      coreObjectSigmaZeroEmbed O x :=
  rfl

/-- Compact table certificate adding Mathlib `Homeomorph` objects to the P548
eighteen-object zero-fiber table and the P549 active-fiber boundary. -/
structure CoreObjectSigmaZeroHomeomorphTableCertificate where
  zero_fiber_table :
    CoreObjectSigmaZeroFiberTableCertificate
  annealing_boundary :
    SigmaZeroAnnealingBoundaryCertificate
  homeomorph :
    ∀ O : CoreMathematicalObject18,
      @Homeomorph
        (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
        (sigmaZeroRelaxedTopology
          ℝ (CoreObjectCarrier O) CoreObjectHeadroom) inferInstance
  homeomorph_to_equiv :
    ∀ O : CoreMathematicalObject18,
      @Homeomorph.toEquiv
          (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
          (sigmaZeroRelaxedTopology
            ℝ (CoreObjectCarrier O) CoreObjectHeadroom) inferInstance
          (homeomorph O) =
        coreObjectSigmaZeroEquiv O
  homeomorph_forget_apply :
    ∀ (O : CoreMathematicalObject18) (z : CoreObjectSigmaZeroFiber O),
      (@Homeomorph.toEquiv
          (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
          (sigmaZeroRelaxedTopology
            ℝ (CoreObjectCarrier O) CoreObjectHeadroom) inferInstance
          (homeomorph O)) z =
        coreObjectSigmaZeroForget O z
  homeomorph_embed_symm_apply :
    ∀ (O : CoreMathematicalObject18) (x : CoreObjectCarrier O),
      (@Homeomorph.toEquiv
          (CoreObjectSigmaZeroFiber O) (CoreObjectCarrier O)
          (sigmaZeroRelaxedTopology
            ℝ (CoreObjectCarrier O) CoreObjectHeadroom) inferInstance
          (homeomorph O)).symm x =
        coreObjectSigmaZeroEmbed O x

/-- THEOREM 4: the eighteen-object sigma-zero homeomorphism table is
inhabited. -/
def coreObjectSigmaZeroHomeomorphTableCertificate :
    CoreObjectSigmaZeroHomeomorphTableCertificate where
  zero_fiber_table := coreObjectSigmaZeroFiberTableCertificate
  annealing_boundary := sigmaZeroAnnealingBoundaryCertificate
  homeomorph := coreObjectSigmaZeroHomeomorph
  homeomorph_to_equiv := by
    intro O
    rfl
  homeomorph_forget_apply := by
    intro O z
    rfl
  homeomorph_embed_symm_apply := by
    intro O x
    rfl

end SaturationMonoid
