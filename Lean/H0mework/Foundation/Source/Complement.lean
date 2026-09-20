import Mathlib.Logic.Function.Basic

/-!
# Constructive complement-observation carrier kernel

The O0 registry used by source anchors consists only of a distinguished point,
an involutive complement, their separation, and structure-preserving maps.  It
does not depend on the historical Proposition chain or on a ring realization.

Category-theoretic initiality and the `{0, 1}` ring adapter live in
`ComplementObservationCarrierInitiality`; authority kernels import this file.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ComplementObservation

universe u

/-- A registered observation carrier with a nondegenerate involutive
complement orbit based at `null`. -/
structure ComplementObservationCarrier where
  Carrier : Type u
  null : Carrier
  complement : Carrier → Carrier
  complement_involutive : Function.Involutive complement
  null_ne_complement_null : null ≠ complement null

/-- A structure-preserving map of complement-observation carriers. -/
structure ComplementObservationHom
    (C D : ComplementObservationCarrier.{u}) where
  toFun : C.Carrier → D.Carrier
  map_null : toFun C.null = D.null
  map_complement :
    ∀ point, toFun (C.complement point) = D.complement (toFun point)

@[ext]
theorem ComplementObservationHom.ext
    {C D : ComplementObservationCarrier.{u}}
    {left right : ComplementObservationHom C D}
    (toFun_eq : left.toFun = right.toFun) :
    left = right := by
  cases left
  cases right
  cases toFun_eq
  rfl

/-- The canonical two-point complement orbit. -/
def canonicalComplementPair : ComplementObservationCarrier.{u} where
  Carrier := ULift.{u} Bool
  null := ⟨false⟩
  complement := fun point => ⟨!point.down⟩
  complement_involutive := by
    rintro ⟨point⟩
    cases point <;> rfl
  null_ne_complement_null := by
    intro equality
    have downEquality : false = true := congrArg ULift.down equality
    cases downEquality

/-- The canonical structure-preserving map from the two-point orbit into an
arbitrary coherent complement-observation carrier. -/
def canonicalPairHom
    (C : ComplementObservationCarrier.{u}) :
    ComplementObservationHom canonicalComplementPair C where
  toFun := fun point =>
    if point.down then C.complement C.null else C.null
  map_null := rfl
  map_complement := by
    intro point
    rcases point with ⟨point⟩
    cases point with
    | false => rfl
    | true => exact (C.complement_involutive C.null).symm

/-- A coherent complement-observation carrier cannot collapse to a
subsingleton because its registered endpoint and complement are distinct. -/
theorem no_subsingleton_complement_observation_carrier
    (C : ComplementObservationCarrier.{u}) :
    ¬ Subsingleton C.Carrier := by
  intro subsingleton
  exact C.null_ne_complement_null (Subsingleton.elim _ _)

/-- The unique canonical-pair map embeds the two registered endpoints into
every coherent carrier. -/
theorem canonical_pair_hom_injective
    (C : ComplementObservationCarrier.{u}) :
    Function.Injective (canonicalPairHom C).toFun := by
  intro left right equality
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  cases left <;> cases right
  · rfl
  · exact (C.null_ne_complement_null equality).elim
  · exact (C.null_ne_complement_null equality.symm).elim
  · rfl

/-- The canonical complement pair has a registered point. -/
theorem canonical_complement_pair_exists :
    Nonempty
      (canonicalComplementPair : ComplementObservationCarrier.{u}).Carrier :=
  ⟨(canonicalComplementPair : ComplementObservationCarrier.{u}).null⟩

end ComplementObservation
end SaturationMonoid
