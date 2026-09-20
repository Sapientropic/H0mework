import H0mework.Realization.Fibres.P314

/-!
# Proposition 315: common-involution equivalence transport

P314 proves the shared complement-involution spine:

* the sigma/rate projection uses `r ↦ 1-r`;
* the analytic functional-equation projection uses `s ↦ 1-s`;
* both can be projections of one common involution.

This file proves the next honest bridge.  If an arithmetic predicate and an
analytic predicate are both faithful pullbacks of the same global obstruction
on the common carrier, then they are equivalent at every common point.

Boundary: this is still a certificate interface.  It does not identify
Goldbach with RH.  A later theorem must supply the actual faithful pullback
certificate for those concrete predicates before the equivalence may be
claimed.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Pulling two predicates back from one global obstruction -/

/-- A common obstruction bridge says that the arithmetic and analytic
predicates are not merely analogous: they are both exactly the pullback of one
global obstruction predicate along the two projections of a common complement
carrier. -/
structure CommonObstructionBridge
    (X Rate Analytic : Type*) [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    (C : CommonComplementInvolution X Rate Analytic) where
  globalObstruction : X -> Prop
  arithmeticObstruction : Rate -> Prop
  analyticObstruction : Analytic -> Prop
  arithmetic_pullback :
    ∀ x : X, arithmeticObstruction (C.rate x) ↔ globalObstruction x
  analytic_pullback :
    ∀ x : X, analyticObstruction (C.analytic x) ↔ globalObstruction x

namespace CommonObstructionBridge

/-- THEOREM 1: two predicates pulled back from the same global obstruction are
equivalent at each common-carrier point. -/
theorem arithmetic_iff_analytic_at
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    {C : CommonComplementInvolution X Rate Analytic}
    (B : CommonObstructionBridge X Rate Analytic C)
    (x : X) :
    B.arithmeticObstruction (C.rate x) ↔
      B.analyticObstruction (C.analytic x) := by
  exact (B.arithmetic_pullback x).trans (B.analytic_pullback x).symm

/-- THEOREM 2: the same equivalence holds after applying the common complement
involution. -/
theorem arithmetic_iff_analytic_at_complement
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    {C : CommonComplementInvolution X Rate Analytic}
    (B : CommonObstructionBridge X Rate Analytic C)
    (x : X) :
    B.arithmeticObstruction (complement (C.rate x)) ↔
      B.analyticObstruction (analyticComplement (C.analytic x)) := by
  rw [← C.rate_projection x, ← C.analytic_projection x]
  exact B.arithmetic_iff_analytic_at (C.involution x)

end CommonObstructionBridge

/-! ## Self-dual bridges preserve both projected obstruction predicates -/

/-- A self-dual bridge adds that the global obstruction itself is invariant
under the common complement involution. -/
structure SelfDualCommonObstructionBridge
    (X Rate Analytic : Type*) [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    (C : CommonComplementInvolution X Rate Analytic)
    extends CommonObstructionBridge X Rate Analytic C where
  global_self_dual :
    ∀ x : X, globalObstruction (C.involution x) ↔ globalObstruction x

namespace SelfDualCommonObstructionBridge

/-- THEOREM 3: if the global obstruction is self-dual, then the arithmetic
projection is invariant under `r ↦ 1-r` along the common carrier. -/
theorem arithmetic_complement_iff
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    {C : CommonComplementInvolution X Rate Analytic}
    (B : SelfDualCommonObstructionBridge X Rate Analytic C)
    (x : X) :
    B.arithmeticObstruction (complement (C.rate x)) ↔
      B.arithmeticObstruction (C.rate x) := by
  rw [← C.rate_projection x]
  exact (B.arithmetic_pullback (C.involution x)).trans
    ((B.global_self_dual x).trans (B.arithmetic_pullback x).symm)

/-- THEOREM 4: if the global obstruction is self-dual, then the analytic
projection is invariant under `s ↦ 1-s` along the common carrier. -/
theorem analytic_complement_iff
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    {C : CommonComplementInvolution X Rate Analytic}
    (B : SelfDualCommonObstructionBridge X Rate Analytic C)
    (x : X) :
    B.analyticObstruction (analyticComplement (C.analytic x)) ↔
      B.analyticObstruction (C.analytic x) := by
  rw [← C.analytic_projection x]
  exact (B.analytic_pullback (C.involution x)).trans
    ((B.global_self_dual x).trans (B.analytic_pullback x).symm)

/-- THEOREM 5: the self-dual bridge gives a four-corner equivalence: arithmetic,
analytic, arithmetic-complement, and analytic-complement are all the same
global obstruction at the common point. -/
theorem arithmetic_complement_iff_analytic
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    {C : CommonComplementInvolution X Rate Analytic}
    (B : SelfDualCommonObstructionBridge X Rate Analytic C)
    (x : X) :
    B.arithmeticObstruction (complement (C.rate x)) ↔
      B.analyticObstruction (C.analytic x) := by
  exact (B.arithmetic_complement_iff x).trans
    (B.toCommonObstructionBridge.arithmetic_iff_analytic_at x)

end SelfDualCommonObstructionBridge

/-! ## Packaged transport certificates -/

/-- A packaged certificate that the two projected predicates are equivalent
because they are the same global obstruction seen through two projections. -/
structure CommonEquivalenceTransportCertificate
    (X Rate Analytic : Type*) [One Rate] [Sub Rate] [One Analytic] [Sub Analytic] where
  common : CommonComplementInvolution X Rate Analytic
  bridge : CommonObstructionBridge X Rate Analytic common

namespace CommonEquivalenceTransportCertificate

/-- THEOREM 6: a transport certificate gives arithmetic/analytic equivalence
at every common-carrier point. -/
theorem arithmetic_iff_analytic
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    (E : CommonEquivalenceTransportCertificate X Rate Analytic)
    (x : X) :
    E.bridge.arithmeticObstruction (E.common.rate x) ↔
      E.bridge.analyticObstruction (E.common.analytic x) := by
  exact E.bridge.arithmetic_iff_analytic_at x

end CommonEquivalenceTransportCertificate

/-- A packaged self-dual version of the equivalence transport certificate. -/
structure SelfDualEquivalenceTransportCertificate
    (X Rate Analytic : Type*) [One Rate] [Sub Rate] [One Analytic] [Sub Analytic] where
  common : CommonComplementInvolution X Rate Analytic
  bridge : SelfDualCommonObstructionBridge X Rate Analytic common

namespace SelfDualEquivalenceTransportCertificate

/-- THEOREM 7: a self-dual transport certificate gives projected invariance
under both complement maps. -/
theorem complement_invariance
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    (E : SelfDualEquivalenceTransportCertificate X Rate Analytic)
    (x : X) :
    (E.bridge.arithmeticObstruction (complement (E.common.rate x)) ↔
        E.bridge.arithmeticObstruction (E.common.rate x)) ∧
      (E.bridge.analyticObstruction (analyticComplement (E.common.analytic x)) ↔
        E.bridge.analyticObstruction (E.common.analytic x)) := by
  exact ⟨E.bridge.arithmetic_complement_iff x,
    E.bridge.analytic_complement_iff x⟩

/-- THEOREM 8: a self-dual transport certificate still gives the ordinary
arithmetic/analytic equivalence. -/
theorem arithmetic_iff_analytic
    {X Rate Analytic : Type*} [One Rate] [Sub Rate] [One Analytic] [Sub Analytic]
    (E : SelfDualEquivalenceTransportCertificate X Rate Analytic)
    (x : X) :
    E.bridge.arithmeticObstruction (E.common.rate x) ↔
      E.bridge.analyticObstruction (E.common.analytic x) := by
  exact E.bridge.toCommonObstructionBridge.arithmetic_iff_analytic_at x

end SelfDualEquivalenceTransportCertificate

/-! ## Concrete product-carrier adapter -/

/-- On the product common carrier, a supplied pointwise link between arithmetic
and analytic predicates is exactly the missing faithful-pullback certificate.
This theorem is intentionally conditional: the link is the mathematical work. -/
def productCommonObstructionBridge
    {Rate Analytic : Type*} [Ring Rate] [Ring Analytic]
    (arithmetic : Rate -> Prop)
    (analytic : Analytic -> Prop)
    (link : ∀ x : Rate × Analytic, arithmetic x.1 ↔ analytic x.2) :
    CommonObstructionBridge (Rate × Analytic) Rate Analytic
      (productComplementInvolution (Rate := Rate) (Analytic := Analytic)) where
  globalObstruction x := arithmetic x.1
  arithmeticObstruction := arithmetic
  analyticObstruction := analytic
  arithmetic_pullback := by
    intro x
    rfl
  analytic_pullback := by
    intro x
    exact (link x).symm

/-- THEOREM 9: on the product carrier, the supplied link transports through the
generic common-obstruction bridge. -/
theorem productCommonObstructionBridge_transports
    {Rate Analytic : Type*} [Ring Rate] [Ring Analytic]
    (arithmetic : Rate -> Prop)
    (analytic : Analytic -> Prop)
    (link : ∀ x : Rate × Analytic, arithmetic x.1 ↔ analytic x.2)
    (x : Rate × Analytic) :
    (productCommonObstructionBridge arithmetic analytic link).arithmeticObstruction
        ((productComplementInvolution (Rate := Rate) (Analytic := Analytic)).rate x) ↔
      (productCommonObstructionBridge arithmetic analytic link).analyticObstruction
        ((productComplementInvolution (Rate := Rate) (Analytic := Analytic)).analytic x) := by
  exact (productCommonObstructionBridge arithmetic analytic link).arithmetic_iff_analytic_at x

end AffineRelaxation
end SaturationMonoid
