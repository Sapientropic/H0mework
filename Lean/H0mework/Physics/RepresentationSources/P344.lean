import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.CouplingSources.P290
import H0mework.Arithmetic.PrimeShadow.P343

/-!
# Proposition 344: the SM block facets and the color three-cycle

P343 turned the proposed Standard-Model route into an exact obstruction gate:
SM/facet physics must supply an allowed-sector classifier before "no allowed
obstructed prime-edge cycle" can be identified with Goldbach.

This file lowers the geometric picture one finite layer.  The concrete P286
block carrier `3+2+1+1` is represented as an explicit seven-facet block type:

* three color facets;
* two weak facets;
* one hypercharge facet;
* one anti-hypercharge facet.

It also proves that the three-agent time cycle is canonically equivalent to the
color block.  Thus the slogan "the three-agent ring is the color cycle" is now
a Lean object.  What is still not proved here is the Standard-Model
representation/action theorem that derives P343's `allowed` predicate or its
obstruction classifier from QCD confinement / gauge invariance.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace StandardModelConstraint

open GaugeProjection
open GaugeProjection.ConcreteBlockDiagonal

/-! ## Explicit seven-facet Standard-Model block carrier -/

/-- The four block kinds inside the `3+2+1+1` Standard-Model carrier. -/
inductive SMBlockFacet where
  | color : Fin 3 -> SMBlockFacet
  | weak : Fin 2 -> SMBlockFacet
  | hypercharge : SMBlockFacet
  | antiHypercharge : SMBlockFacet
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Convert the explicit block-facet carrier to P286's nested sum index. -/
def smBlockFacetToIndex : SMBlockFacet -> SMBlockIndex
  | SMBlockFacet.color i => Sum.inl i
  | SMBlockFacet.weak i => Sum.inr (Sum.inl i)
  | SMBlockFacet.hypercharge => Sum.inr (Sum.inr (Sum.inl 0))
  | SMBlockFacet.antiHypercharge => Sum.inr (Sum.inr (Sum.inr 0))

/-- Convert P286's nested sum index back to the explicit block-facet carrier. -/
def smBlockIndexToFacet : SMBlockIndex -> SMBlockFacet
  | Sum.inl i => SMBlockFacet.color i
  | Sum.inr (Sum.inl i) => SMBlockFacet.weak i
  | Sum.inr (Sum.inr (Sum.inl _)) => SMBlockFacet.hypercharge
  | Sum.inr (Sum.inr (Sum.inr _)) => SMBlockFacet.antiHypercharge

@[simp]
theorem smBlockIndexToFacet_toIndex (x : SMBlockFacet) :
    smBlockIndexToFacet (smBlockFacetToIndex x) = x := by
  cases x <;> simp [smBlockFacetToIndex, smBlockIndexToFacet]

@[simp]
theorem smBlockFacetToIndex_toFacet (i : SMBlockIndex) :
    smBlockFacetToIndex (smBlockIndexToFacet i) = i := by
  rcases i with i | i
  · simp [smBlockFacetToIndex, smBlockIndexToFacet]
  · rcases i with i | i
    · simp [smBlockFacetToIndex, smBlockIndexToFacet]
    · rcases i with i | i <;>
        fin_cases i <;>
          simp [smBlockFacetToIndex, smBlockIndexToFacet]

/-- THEOREM 1: the explicit block-facet carrier is equivalent to P286's
`3+2+1+1` nested-sum carrier. -/
def smBlockFacetEquivSMBlockIndex : SMBlockFacet ≃ SMBlockIndex where
  toFun := smBlockFacetToIndex
  invFun := smBlockIndexToFacet
  left_inv := smBlockIndexToFacet_toIndex
  right_inv := smBlockFacetToIndex_toFacet

/-- THEOREM 2: the explicit block-facet carrier is equivalent to `Fin 7`. -/
def smBlockFacetEquivFin7 : SMBlockFacet ≃ Fin 7 :=
  smBlockFacetEquivSMBlockIndex.trans smBlockIndexEquivFin7

/-- THEOREM 3: the explicit block-facet carrier has seven elements. -/
theorem smBlockFacet_card_eq_seven :
    Fintype.card SMBlockFacet = 7 := by
  classical
  exact Fintype.card_congr smBlockFacetEquivFin7

/-- The color block predicate. -/
def IsColorFacet : SMBlockFacet -> Prop
  | SMBlockFacet.color _ => True
  | _ => False

instance : DecidablePred IsColorFacet := by
  intro x
  cases x with
  | color _ => exact isTrue trivial
  | weak _ => exact isFalse (by intro h; cases h)
  | hypercharge => exact isFalse (by intro h; cases h)
  | antiHypercharge => exact isFalse (by intro h; cases h)

/-- The weak block predicate. -/
def IsWeakFacet : SMBlockFacet -> Prop
  | SMBlockFacet.weak _ => True
  | _ => False

instance : DecidablePred IsWeakFacet := by
  intro x
  cases x with
  | color _ => exact isFalse (by intro h; cases h)
  | weak _ => exact isTrue trivial
  | hypercharge => exact isFalse (by intro h; cases h)
  | antiHypercharge => exact isFalse (by intro h; cases h)

/-- The hypercharge-pair/singlet predicate. -/
def IsHyperchargePairFacet : SMBlockFacet -> Prop
  | SMBlockFacet.hypercharge => True
  | SMBlockFacet.antiHypercharge => True
  | _ => False

instance : DecidablePred IsHyperchargePairFacet := by
  intro x
  cases x with
  | color _ => exact isFalse (by intro h; cases h)
  | weak _ => exact isFalse (by intro h; cases h)
  | hypercharge => exact isTrue trivial
  | antiHypercharge => exact isTrue trivial

/-- The gauged fundamental predicate: color or weak. -/
def IsGaugedFundamentalFacet (x : SMBlockFacet) : Prop :=
  IsColorFacet x ∨ IsWeakFacet x

/-- THEOREM 4: the color block is equivalent to `Fin 3`. -/
def colorFacetEquivFin3 : {x : SMBlockFacet // IsColorFacet x} ≃ Fin 3 where
  toFun x :=
    match x with
    | ⟨SMBlockFacet.color i, _⟩ => i
    | ⟨SMBlockFacet.weak _, h⟩ => False.elim h
    | ⟨SMBlockFacet.hypercharge, h⟩ => False.elim h
    | ⟨SMBlockFacet.antiHypercharge, h⟩ => False.elim h
  invFun i := ⟨SMBlockFacet.color i, trivial⟩
  left_inv := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x <;> simp [IsColorFacet] at hx ⊢
  right_inv := by
    intro i
    rfl

/-- THEOREM 5: the color block has cardinality `3`. -/
theorem colorFacet_card_eq_three :
    Fintype.card {x : SMBlockFacet // IsColorFacet x} = 3 := by
  classical
  exact Fintype.card_congr colorFacetEquivFin3

/-- THEOREM 6: the weak block is equivalent to `Fin 2`. -/
def weakFacetEquivFin2 : {x : SMBlockFacet // IsWeakFacet x} ≃ Fin 2 where
  toFun x :=
    match x with
    | ⟨SMBlockFacet.color _, h⟩ => False.elim h
    | ⟨SMBlockFacet.weak i, _⟩ => i
    | ⟨SMBlockFacet.hypercharge, h⟩ => False.elim h
    | ⟨SMBlockFacet.antiHypercharge, h⟩ => False.elim h
  invFun i := ⟨SMBlockFacet.weak i, trivial⟩
  left_inv := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x <;> simp [IsWeakFacet] at hx ⊢
  right_inv := by
    intro i
    rfl

/-- THEOREM 7: the weak block has cardinality `2`. -/
theorem weakFacet_card_eq_two :
    Fintype.card {x : SMBlockFacet // IsWeakFacet x} = 2 := by
  classical
  exact Fintype.card_congr weakFacetEquivFin2

/-- THEOREM 8: the hypercharge pair has cardinality `2`. -/
theorem hyperchargePairFacet_card_eq_two :
    Fintype.card {x : SMBlockFacet // IsHyperchargePairFacet x} = 2 := by
  classical
  let e : {x : SMBlockFacet // IsHyperchargePairFacet x} ≃ Fin 2 := {
    toFun := fun x =>
      match x with
      | ⟨SMBlockFacet.color _, h⟩ => False.elim h
      | ⟨SMBlockFacet.weak _, h⟩ => False.elim h
      | ⟨SMBlockFacet.hypercharge, _⟩ => 0
      | ⟨SMBlockFacet.antiHypercharge, _⟩ => 1
    invFun := fun i =>
      if h : i = 0 then ⟨SMBlockFacet.hypercharge, trivial⟩
      else ⟨SMBlockFacet.antiHypercharge, trivial⟩
    left_inv := by
      intro x
      rcases x with ⟨x, hx⟩
      cases x <;> simp [IsHyperchargePairFacet] at hx ⊢
    right_inv := by
      intro i
      fin_cases i <;> simp
  }
  exact Fintype.card_congr e

/-! ## Three-agent time is the color block -/

/-- The canonical equivalence from the three-agent time skeleton to `Fin 3`. -/
def threeCycleTimeEquivFin3 : ThreeCycleTime ≃ Fin 3 where
  toFun
    | ThreeCycleTime.t0 => 0
    | ThreeCycleTime.t1 => 1
    | ThreeCycleTime.t2 => 2
  invFun i :=
    if h0 : i = 0 then ThreeCycleTime.t0
    else if h1 : i = 1 then ThreeCycleTime.t1
    else ThreeCycleTime.t2
  left_inv := by
    intro t
    cases t <;> simp
  right_inv := by
    intro i
    fin_cases i <;> simp

/-- THEOREM 9: the three-agent time skeleton is equivalent to the color block.
This is the precise finite statement behind "the three-agent ring is the color
cycle". -/
def threeCycleTimeEquivColorFacet :
    ThreeCycleTime ≃ {x : SMBlockFacet // IsColorFacet x} :=
  threeCycleTimeEquivFin3.trans colorFacetEquivFin3.symm

/-- Embed a three-cycle time point as a color facet. -/
def threeCycleColorFacet (t : ThreeCycleTime) : SMBlockFacet :=
  (threeCycleTimeEquivColorFacet t).1

/-- THEOREM 10: the three-cycle color-facet embedding is injective. -/
theorem threeCycleColorFacet_injective :
    Function.Injective threeCycleColorFacet := by
  intro a b h
  exact threeCycleTimeEquivColorFacet.injective
    (Subtype.ext h)

/-- THEOREM 11: every embedded three-cycle point is a color facet. -/
theorem threeCycleColorFacet_isColor (t : ThreeCycleTime) :
    IsColorFacet (threeCycleColorFacet t) :=
  (threeCycleTimeEquivColorFacet t).2

/-- A compact certificate for the finite SM block/facet carrier and color
three-cycle identification. -/
structure P344SMBlockFacetColorCycleCertificate : Prop where
  block_equiv_p286 :
    Nonempty (SMBlockFacet ≃ SMBlockIndex)
  block_equiv_fin7 :
    Nonempty (SMBlockFacet ≃ Fin 7)
  block_card :
    Fintype.card SMBlockFacet = 7
  color_card :
    Fintype.card {x : SMBlockFacet // IsColorFacet x} = 3
  weak_card :
    Fintype.card {x : SMBlockFacet // IsWeakFacet x} = 2
  hypercharge_pair_card :
    Fintype.card {x : SMBlockFacet // IsHyperchargePairFacet x} = 2
  three_cycle_color_equiv :
    Nonempty (ThreeCycleTime ≃ {x : SMBlockFacet // IsColorFacet x})
  three_cycle_color_injective :
    Function.Injective threeCycleColorFacet
  three_cycle_lands_in_color :
    ∀ t : ThreeCycleTime, IsColorFacet (threeCycleColorFacet t)

/-- THEOREM 12: the canonical SM block/facet and color-cycle certificate. -/
theorem p344SMBlockFacetColorCycleCertificate :
    P344SMBlockFacetColorCycleCertificate where
  block_equiv_p286 := ⟨smBlockFacetEquivSMBlockIndex⟩
  block_equiv_fin7 := ⟨smBlockFacetEquivFin7⟩
  block_card := smBlockFacet_card_eq_seven
  color_card := colorFacet_card_eq_three
  weak_card := weakFacet_card_eq_two
  hypercharge_pair_card := hyperchargePairFacet_card_eq_two
  three_cycle_color_equiv := ⟨threeCycleTimeEquivColorFacet⟩
  three_cycle_color_injective := threeCycleColorFacet_injective
  three_cycle_lands_in_color := threeCycleColorFacet_isColor

end StandardModelConstraint
end SaturationMonoid
