import H0mework.Foundation.Source.Complement
import H0mework.Realization.Claims.P474
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Initiality of the minimal complement-observation carrier

The domain-free carrier and canonical map live in the constructive
`ComplementObservationCarrierKernel`.  This adapter installs their
category-theoretic initiality and the historical ring realization.

The canonical two-point complement orbit is initial in this category.  Its
unique map into every coherent carrier is injective, so no coherent carrier is
subsingleton.  A final bridge identifies its realization in a nontrivial ring
with the existing `{0, 1}` complement-closed subset from P469/P474.

This is an independent structural foundation.  It does not generate a source,
an actual action, a no-third-sink law, an arithmetic atom pair, or any
Borromean/Goldbach materialization premise.
-/

namespace SaturationMonoid
namespace ComplementObservation

open CategoryTheory
open CategoryTheory.Limits
open AffineRelaxation

universe u

/-- Complement-observation carriers and their structure-preserving maps form
a category. -/
instance complementObservationCarrierCategory :
    Category (ComplementObservationCarrier.{u}) where
  Hom := ComplementObservationHom
  id C :=
    { toFun := id
      map_null := rfl
      map_complement := fun _ => rfl }
  comp first second :=
    { toFun := fun point => second.toFun (first.toFun point)
      map_null := by rw [first.map_null, second.map_null]
      map_complement := by
        intro point
        rw [first.map_complement, second.map_complement] }
  id_comp := by
    intro C D f
    apply ComplementObservationHom.ext
    rfl
  comp_id := by
    intro C D f
    apply ComplementObservationHom.ext
    rfl
  assoc := by
    intro B C D E f g h
    apply ComplementObservationHom.ext
    rfl

/-- Every structure-preserving map out of the canonical pair is the canonical
map.  Function extensionality belongs to this presentation adapter, not the
constructive source-anchor kernel. -/
theorem canonicalPairHom_unique
    (C : ComplementObservationCarrier.{u})
    (f : canonicalComplementPair ⟶ C) :
    f = canonicalPairHom C := by
  apply ComplementObservationHom.ext
  funext point
  rcases point with ⟨point⟩
  cases point with
  | false =>
      exact f.map_null
  | true =>
      have mapsComplement := f.map_complement (ULift.up false)
      calc
        f.toFun (ULift.up true) =
            C.complement (f.toFun (ULift.up false)) := by
          simpa [canonicalComplementPair] using mapsComplement
        _ = C.complement C.null :=
          congrArg C.complement f.map_null
        _ = (canonicalPairHom C).toFun (ULift.up true) := rfl

/-- Category-notation adapter for the constructive unique homomorphism. -/
instance canonicalComplementPairHomUnique
    (C : ComplementObservationCarrier.{u}) :
    Unique (canonicalComplementPair ⟶ C) where
  default := canonicalPairHom C
  uniq := fun f => canonicalPairHom_unique C f

/-- The canonical complement pair is initial.  `IsInitial` is data in
`Type`, so this declaration is a definition rather than a proposition-valued
theorem. -/
noncomputable def canonical_complement_pair_initial :
    IsInitial
      (canonicalComplementPair : ComplementObservationCarrier.{u}) :=
  IsInitial.ofUnique _

/-- Realize the abstract observation contract on the P469/P474 endpoint
subset of a nontrivial ring. -/
def ringEndpointComplementObservationCarrier
    (K : Type u) [Ring K] [Nontrivial K] :
    ComplementObservationCarrier.{u} where
  Carrier := {point : K // point ∈ nullEverythingPair K}
  null := ⟨0, by simp [nullEverythingPair]⟩
  complement := fun point =>
    ⟨complement point.1, nullEverythingPair_complementClosed point.2⟩
  complement_involutive := by
    intro point
    apply Subtype.ext
    exact complement_involutive point.1
  null_ne_complement_null := by
    intro equality
    have valueEquality : (0 : K) = complement (0 : K) :=
      congrArg Subtype.val equality
    have zeroEqualsOne : (0 : K) = 1 := by
      simpa only [complement, sub_zero] using valueEquality
    exact (zero_ne_one : (0 : K) ≠ 1) zeroEqualsOne

/-- In a nontrivial ring, the underlying range of the canonical initial map is
exactly P469's `{0, 1}` endpoint subset. -/
theorem ringEndpointCanonicalPair_range_eq_nullEverythingPair
    (K : Type u) [Ring K] [Nontrivial K] :
    Set.range
        (fun point =>
          ((canonicalPairHom
            (ringEndpointComplementObservationCarrier K)).toFun point).1) =
      nullEverythingPair K := by
  ext point
  constructor
  · rintro ⟨canonicalPoint, rfl⟩
    rcases canonicalPoint with ⟨canonicalPoint⟩
    cases canonicalPoint <;>
      simp [canonicalPairHom, ringEndpointComplementObservationCarrier,
        canonicalComplementPair, nullEverythingPair, complement]
  · intro endpointMembership
    rcases endpointMembership with nullCase | everythingCase
    · subst point
      exact ⟨ULift.up false, rfl⟩
    · subst point
      refine ⟨ULift.up true, ?_⟩
      simp [canonicalPairHom, ringEndpointComplementObservationCarrier,
        canonicalComplementPair, complement]

/-- P474's subset-minimality is the concrete ring realization of the
canonical pair range: every complement-closed subset containing zero contains
that range. -/
theorem ringEndpointCanonicalPair_range_minimal_from_null
    (K : Type u) [Ring K] [Nontrivial K]
    {S : Set K}
    (complementClosed : ComplementClosed S)
    (nullMem : (0 : K) ∈ S) :
    Set.range
        (fun point =>
          ((canonicalPairHom
            (ringEndpointComplementObservationCarrier K)).toFun point).1) ⊆
      S := by
  rw [ringEndpointCanonicalPair_range_eq_nullEverythingPair]
  exact
    nullEverythingPair_subset_of_complementClosed_mem_zero
      complementClosed nullMem

end ComplementObservation
end SaturationMonoid
