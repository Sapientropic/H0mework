import H0mework.Realization.Fibres.P663

/-!
# Proposition 796: sigma-zero conservative extension

P547 proves the generic zero-fiber equivalence `X_0 ≃ X`; P663 packages the
large sigma-zero mathematics foundation spine.  This file is the small hard
front door:

standard mathematics is a conservative special fiber of the saturation /
relaxation carrier.

The theorem is deliberately schema-level.  It does not enumerate another table
of examples.  For every standard carrier `X`, the sigma-zero fiber forgets
back to `X` by an equivalence, and lifted operations, predicates, and relations
push forward to exactly the original data.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open AffineRelaxation

universe u v w x y z

/-! ## Conservative sigma-zero extension -/

/-- Conservative-extension certificate for the sigma-zero special fiber.

The fields split the claim into:

* the already proved P550--P580/P663 mathematics foundation spine;
* the generic object equivalence `X_0 ≃ X`;
* exact conservation of unary operations, binary operations, predicates, and
  relations under the forgetful projection.
-/
structure SigmaRelaxationConservativeExtensionCertificate
    (K : Type u) [Zero K] (𝕜 : Type v) [RCLike 𝕜]
    (H : Type w) [Inhabited H] where
  foundation :
    SigmaZeroMathematicsFoundationCertificate.{u, v, w, x, y, z} K 𝕜 H
  zero_fiber_equiv :
    ∀ X : Type x, SigmaRelaxedObject K X H (0 : K) ≃ X
  forget_embed :
    ∀ (X : Type x) (x : X),
      sigmaZeroForget (K := K) (X := X) (H := H)
          (sigmaZeroEmbed (K := K) (X := X) (H := H) x) = x
  embed_forget :
    ∀ (X : Type x) (z : SigmaRelaxedObject K X H (0 : K)),
      sigmaZeroEmbed (K := K) (X := X) (H := H)
          (sigmaZeroForget (K := K) (X := X) (H := H) z) = z
  unary_conservative :
    ∀ (X : Type x) (f : X -> X)
      (z : SigmaRelaxedObject K X H (0 : K)),
      sigmaZeroForget (K := K) (X := X) (H := H)
          (sigmaZeroLiftUnary (K := K) (H := H) f z) =
        f (sigmaZeroForget (K := K) (X := X) (H := H) z)
  binary_conservative :
    ∀ (X : Type x) (op : X -> X -> X)
      (a b : SigmaRelaxedObject K X H (0 : K)),
      sigmaZeroForget (K := K) (X := X) (H := H)
          (sigmaZeroLiftBinary (K := K) (H := H) op a b) =
        op
          (sigmaZeroForget (K := K) (X := X) (H := H) a)
          (sigmaZeroForget (K := K) (X := X) (H := H) b)
  predicate_conservative :
    ∀ (X : Type x) (P : X -> Prop) (x : X),
      sigmaZeroLiftPredicate (K := K) (H := H) P
          (sigmaZeroEmbed (K := K) (X := X) (H := H) x) ↔ P x
  relation_conservative :
    ∀ (X : Type x) (R : X -> X -> Prop) (x y : X),
      sigmaZeroLiftRelation (K := K) (H := H) R
          (sigmaZeroEmbed (K := K) (X := X) (H := H) x)
          (sigmaZeroEmbed (K := K) (X := X) (H := H) y) ↔ R x y

/-- THEOREM 1: sigma-zero relaxation is a conservative extension of standard
mathematics.

At `sigma = 0`, the headroom coordinate is quotiented away.  The forgetful map
is an equivalence and every lifted standard structure is definitionally
transported back to the original one. -/
def sigmaRelaxationConservativeExtensionCertificate
    (K : Type u) [Zero K] (𝕜 : Type v) [RCLike 𝕜]
    (H : Type w) [Inhabited H] :
    SigmaRelaxationConservativeExtensionCertificate K 𝕜 H where
  foundation := sigmaZeroMathematicsFoundationCertificate K 𝕜 H
  zero_fiber_equiv := by
    intro X
    exact sigmaZeroRelaxedEquiv K X H
  forget_embed := by
    intro X x
    rfl
  embed_forget := by
    intro X z
    exact sigmaZeroEmbed_forget (K := K) (X := X) (H := H) z
  unary_conservative := by
    intro X f z
    rfl
  binary_conservative := by
    intro X op a b
    rfl
  predicate_conservative := by
    intro X P x
    rfl
  relation_conservative := by
    intro X R x y
    rfl

end GrandUnification
end SaturationMonoid
