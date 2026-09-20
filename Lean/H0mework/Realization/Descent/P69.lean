/-
  Proposition 69: a Čech-style cochain skeleton.

  Proposition 68 supplied the section-valued equalizer/descent law.  This file
  adds the first real cohomological bone: additive 0/1/2 cochains, coboundary
  maps, and the theorem `d1 ∘ d0 = 0`.

  Boundary: this is still a skeleton.  It is not a topological site, not a
  quotient group construction for H¹, and not yet connected to a concrete
  runtime gluing cocycle.  It does give the exact algebraic target that a
  future `GluingFailureSupport` -> H¹ theorem must instantiate.
-/

import H0mework.Realization.Fields.SectionCover

/-! ## Additive Čech cover skeleton -/

/-- A minimal additive cover skeleton with one coefficient group `A`.

The maps are oriented restrictions:

* `localToPairLeft i j` restricts a section on `i` to overlap `ij`;
* `localToPairRight i j` restricts a section on `j` to overlap `ij`;
* `pairToTriple01/02/12` restrict pair overlaps to the triple overlap `ijk`.

The three coherence laws say that a local section reaches the triple overlap
the same way along either pairwise path. -/
structure CechAdditiveCover (Index A : Type*) [AddCommGroup A] where
  localToPairLeft : Index -> Index -> AddMonoidHom A A
  localToPairRight : Index -> Index -> AddMonoidHom A A
  pairToTriple01 : Index -> Index -> Index -> AddMonoidHom A A
  pairToTriple02 : Index -> Index -> Index -> AddMonoidHom A A
  pairToTriple12 : Index -> Index -> Index -> AddMonoidHom A A
  coh0 :
    forall i j k x,
      pairToTriple02 i j k (localToPairLeft i k x) =
        pairToTriple01 i j k (localToPairLeft i j x)
  coh1 :
    forall i j k x,
      pairToTriple12 i j k (localToPairLeft j k x) =
        pairToTriple01 i j k (localToPairRight i j x)
  coh2 :
    forall i j k x,
      pairToTriple12 i j k (localToPairRight j k x) =
        pairToTriple02 i j k (localToPairRight i k x)

namespace CechAdditiveCover

variable {Index A : Type*} [AddCommGroup A]

/-- The 0-coboundary: right restriction minus left restriction on each pair
overlap. -/
def d0 (C : CechAdditiveCover Index A) (s : Index -> A) :
    Index -> Index -> A :=
  fun i j =>
    C.localToPairRight i j (s j) - C.localToPairLeft i j (s i)

/-- The 1-coboundary with the usual alternating sign pattern on triple
overlaps. -/
def d1 (C : CechAdditiveCover Index A) (c : Index -> Index -> A) :
    Index -> Index -> Index -> A :=
  fun i j k =>
    C.pairToTriple12 i j k (c j k) -
      C.pairToTriple02 i j k (c i k) +
        C.pairToTriple01 i j k (c i j)

/-- Pairwise compatibility of a local family, expressed as equality on every
pair overlap. -/
def PairwiseCompatible (C : CechAdditiveCover Index A) (s : Index -> A) : Prop :=
  forall i j,
    C.localToPairRight i j (s j) = C.localToPairLeft i j (s i)

/-- A 1-cocycle is a 1-cochain killed by `d1`. -/
def OneCocycle (C : CechAdditiveCover Index A)
    (c : Index -> Index -> A) : Prop :=
  d1 C c = 0

/-- A 1-coboundary is in the image of `d0`. -/
def OneCoboundary (C : CechAdditiveCover Index A)
    (c : Index -> Index -> A) : Prop :=
  exists s : Index -> A, d0 C s = c

/-- A first-cohomology obstruction at this skeleton level: a cocycle that is
not a coboundary.  This is a predicate, not yet a quotient group. -/
def H1Obstruction (C : CechAdditiveCover Index A)
    (c : Index -> Index -> A) : Prop :=
  OneCocycle C c /\ Not (OneCoboundary C c)

/-! ## Core laws -/

/-- THEOREM 1: local pairwise compatibility is exactly vanishing
0-coboundary. -/
theorem d0_eq_zero_iff_pairwiseCompatible
    (C : CechAdditiveCover Index A) (s : Index -> A) :
    d0 C s = 0 <-> PairwiseCompatible C s := by
  constructor
  · intro h i j
    have hij : C.localToPairRight i j (s j) -
        C.localToPairLeft i j (s i) = 0 := by
      exact congrFun (congrFun h i) j
    exact sub_eq_zero.mp hij
  · intro h
    funext i j
    exact sub_eq_zero.mpr (h i j)

/-- THEOREM 2: the Čech coboundary squares to zero. -/
theorem d1_d0_eq_zero
    (C : CechAdditiveCover Index A) (s : Index -> A) :
    d1 C (d0 C s) = 0 := by
  funext i j k
  simp [d0, d1, map_sub, C.coh0, C.coh1, C.coh2]

/-- THEOREM 3: every 1-coboundary is a 1-cocycle. -/
theorem oneCoboundary_is_oneCocycle
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (hb : OneCoboundary C c) :
    OneCocycle C c := by
  rcases hb with ⟨s, rfl⟩
  exact d1_d0_eq_zero C s

/-- THEOREM 4: an H¹ obstruction is, in particular, not a coboundary. -/
theorem h1Obstruction_not_coboundary
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (h : H1Obstruction C c) :
    Not (OneCoboundary C c) := h.2

/-- THEOREM 5: a 1-cochain cannot be both an H¹ obstruction and a coboundary.
-/
theorem not_h1Obstruction_of_coboundary
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (hb : OneCoboundary C c) :
    Not (H1Obstruction C c) := by
  intro h
  exact h.2 hb

end CechAdditiveCover

/-!
  Summary:
  - `d0_eq_zero_iff_pairwiseCompatible` connects section-valued overlap
    equality to additive cochains.
  - `d1_d0_eq_zero` proves the first real cohomological law missing from the
    earlier H¹-like language.
  - `H1Obstruction` is now a precise target predicate: a cocycle that is not a
    coboundary.  Future work can connect a concrete gluing failure generator to
    this predicate, or honestly fail if no such additive presentation exists.
-/
