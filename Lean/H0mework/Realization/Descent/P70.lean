/-
  Proposition 70: H¹ as cocycles modulo coboundaries.

  Proposition 69 built the Čech-style cochain skeleton and proved
  `d1 ∘ d0 = 0`.  This file takes the next quotient step:

    * cocycles are packaged as a subtype;
    * two cocycles are cohomologous when their difference is a coboundary;
    * H¹ is the quotient of cocycles by that equivalence relation;
    * a coboundary has zero class;
    * the P69 `H1Obstruction` predicate is exactly nonzero class.

  Boundary: this is a quotient object with the right equivalence relation, not
  yet the full `AddCommGroup` quotient API.  It is enough to state the exact
  target for a future runtime theorem: a concrete gluing generator must produce
  a nonzero class in this quotient, not only a Prop-valued support witness.
-/

import H0mework.Realization.Descent.P69

namespace CechAdditiveCover

variable {Index A : Type*} [AddCommGroup A]

/-- The subtype of 1-cocycles. -/
abbrev OneCocycleSubtype (C : CechAdditiveCover Index A) :=
  { c : Index -> Index -> A // OneCocycle C c }

/-- The zero 1-cocycle. -/
def zeroOneCocycle (C : CechAdditiveCover Index A) :
    OneCocycleSubtype C where
  val := 0
  property := by
    show d1 C (0 : Index -> Index -> A) = 0
    funext i j k
    simp [d1]

/-- The zero 1-cochain is a coboundary. -/
theorem zero_oneCoboundary (C : CechAdditiveCover Index A) :
    OneCoboundary C (0 : Index -> Index -> A) := by
  refine ⟨0, ?_⟩
  funext i j
  simp [d0]

/-- The negative of a coboundary is a coboundary. -/
theorem oneCoboundary_neg
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (hb : OneCoboundary C c) :
    OneCoboundary C (-c) := by
  rcases hb with ⟨s, rfl⟩
  refine ⟨-s, ?_⟩
  funext i j
  simp [d0]
  abel

/-- The sum of two coboundaries is a coboundary. -/
theorem oneCoboundary_add
    (C : CechAdditiveCover Index A)
    (c d : Index -> Index -> A)
    (hc : OneCoboundary C c) (hd : OneCoboundary C d) :
    OneCoboundary C (c + d) := by
  rcases hc with ⟨s, rfl⟩
  rcases hd with ⟨t, rfl⟩
  refine ⟨s + t, ?_⟩
  funext i j
  simp [d0]
  abel

/-- Two cocycles are cohomologous when their difference is a coboundary. -/
def Cohomologous (C : CechAdditiveCover Index A)
    (x y : OneCocycleSubtype C) : Prop :=
  OneCoboundary C (x.1 - y.1)

/-- THEOREM 1: cohomology of cocycles is an equivalence relation. -/
theorem cohomologous_equivalence (C : CechAdditiveCover Index A) :
    Equivalence (Cohomologous C) := by
  constructor
  · intro x
    have hzero :
        (x.1 - x.1 : Index -> Index -> A) =
          (0 : Index -> Index -> A) := by
      funext i j
      simp
    change OneCoboundary C (x.1 - x.1)
    rw [hzero]
    exact zero_oneCoboundary C
  · intro x y hxy
    have hneg :
        (y.1 - x.1 : Index -> Index -> A) =
          -(x.1 - y.1) := by
      funext i j
      change y.1 i j - x.1 i j = -(x.1 i j - y.1 i j)
      abel
    change OneCoboundary C (y.1 - x.1)
    rw [hneg]
    exact oneCoboundary_neg C (x.1 - y.1) hxy
  · intro x y z hxy hyz
    have hsum :
        (x.1 - z.1 : Index -> Index -> A) =
          (x.1 - y.1) + (y.1 - z.1) := by
      funext i j
      change x.1 i j - z.1 i j =
        (x.1 i j - y.1 i j) + (y.1 i j - z.1 i j)
      abel
    change OneCoboundary C (x.1 - z.1)
    rw [hsum]
    exact oneCoboundary_add C (x.1 - y.1) (y.1 - z.1) hxy hyz

/-- Setoid of cocycles modulo coboundaries. -/
def cohomologySetoid (C : CechAdditiveCover Index A) :
    Setoid (OneCocycleSubtype C) where
  r := Cohomologous C
  iseqv := cohomologous_equivalence C

/-- The H¹ quotient object: 1-cocycles modulo 1-coboundaries. -/
abbrev H1Quotient (C : CechAdditiveCover Index A) :=
  Quotient (cohomologySetoid C)

/-- The class of a 1-cocycle. -/
def h1Class (C : CechAdditiveCover Index A)
    (c : OneCocycleSubtype C) : H1Quotient C :=
  @Quotient.mk'' _ (cohomologySetoid C) c

/-- The zero H¹ class. -/
def h1Zero (C : CechAdditiveCover Index A) : H1Quotient C :=
  h1Class C (zeroOneCocycle C)

/-- THEOREM 2: a coboundary cocycle has zero H¹ class. -/
theorem h1Class_eq_zero_of_coboundary
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (hc : OneCocycle C c) (hb : OneCoboundary C c) :
    h1Class C ⟨c, hc⟩ = h1Zero C := by
  change
    @Quotient.mk'' _ (cohomologySetoid C) ⟨c, hc⟩ =
      @Quotient.mk'' _ (cohomologySetoid C) (zeroOneCocycle C)
  apply Quotient.sound'
  have hsub : (c - (0 : Index -> Index -> A)) = c := by
    funext i j
    simp
  change OneCoboundary C (c - (0 : Index -> Index -> A))
  rw [hsub]
  exact hb

/-- THEOREM 3: zero H¹ class implies the represented cocycle is a coboundary.
-/
theorem oneCoboundary_of_h1Class_eq_zero
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (hc : OneCocycle C c)
    (hzero : h1Class C ⟨c, hc⟩ = h1Zero C) :
    OneCoboundary C c := by
  have hzero' :
      @Quotient.mk'' _ (cohomologySetoid C) ⟨c, hc⟩ =
        @Quotient.mk'' _ (cohomologySetoid C) (zeroOneCocycle C) := by
    simpa [h1Class, h1Zero]
      using hzero
  have hrel :
      Cohomologous C ⟨c, hc⟩ (zeroOneCocycle C) :=
    Quotient.exact hzero'
  have hsub : c - (0 : Index -> Index -> A) = c := by
    funext i j
    simp
  change OneCoboundary C (c - (0 : Index -> Index -> A)) at hrel
  rw [hsub] at hrel
  exact hrel

/-- THEOREM 4: zero H¹ class is exactly the coboundary condition. -/
theorem h1Class_eq_zero_iff_coboundary
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (hc : OneCocycle C c) :
    h1Class C ⟨c, hc⟩ = h1Zero C <->
      OneCoboundary C c := by
  constructor
  · exact oneCoboundary_of_h1Class_eq_zero C c hc
  · exact h1Class_eq_zero_of_coboundary C c hc

/-- THEOREM 5: P69's `H1Obstruction` predicate is exactly nonzero H¹ class,
provided the cochain is already a cocycle. -/
theorem h1Obstruction_iff_class_ne_zero
    (C : CechAdditiveCover Index A) (c : Index -> Index -> A)
    (hc : OneCocycle C c) :
    H1Obstruction C c <->
      h1Class C ⟨c, hc⟩ ≠ h1Zero C := by
  constructor
  · intro h hzero
    exact h.2 ((h1Class_eq_zero_iff_coboundary C c hc).mp hzero)
  · intro hne
    exact ⟨hc, fun hb =>
      hne ((h1Class_eq_zero_iff_coboundary C c hc).mpr hb)⟩

end CechAdditiveCover

/-!
  Summary:
  - `H1Quotient` is the quotient of cocycles by the coboundary equivalence.
  - `h1Class_eq_zero_iff_coboundary` turns "is a coboundary" into "has zero
    cohomology class".
  - `h1Obstruction_iff_class_ne_zero` upgrades the P69 obstruction predicate:
    an H¹ obstruction is now exactly a nonzero cohomology class.

  Remaining boundary:
  - This is a quotient object, not yet an `AddCommGroup` quotient instance.
  - No concrete AIppocampus gluing generator has yet been mapped into a
    nonzero class in this quotient.
-/
