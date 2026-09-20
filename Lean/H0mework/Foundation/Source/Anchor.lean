import H0mework.Foundation.Source.Complement

/-!
# Minimal registrable source anchors and anchor conservation

Sourcehood is not a privilege granted by a higher source.  It is a strict
responsibility boundary.  A lifecycle vocabulary first fixes one coherent O0
complement registry.  Every source admitted to that vocabulary must then name
a non-self-complementary identity in that registry, together with its scope
and debt lineage.

The canonical two-point complement pair supplies the minimal registry.  Once
an event is indexed by an anchor, ordinary lifecycle receipts may not change
it.  A change of anchor requires an explicit structure-preserving transport.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle

open ComplementObservation

universe u

/-- O0 registration contract for one source inside a fixed complement
registry.  Unlike a naked identity token, the registered identity has a
distinguished complement in the same carrier and must be distinct from it. -/
structure MinimalRegistrableSourceAnchor
    (Observation : ComplementObservationCarrier.{u})
    (Scope Lineage : Type u) : Type u where
  identity : Observation.Carrier
  identity_ne_complement_identity :
    identity ≠ Observation.complement identity
  scope : Scope
  lineage : Lineage

namespace MinimalRegistrableSourceAnchor

variable {Observation : ComplementObservationCarrier.{u}}
variable {Scope Lineage : Type u}

def complementIdentity
    (anchor : MinimalRegistrableSourceAnchor Observation Scope Lineage) :
    Observation.Carrier :=
  Observation.complement anchor.identity

theorem identity_ne_complementIdentity
    (anchor : MinimalRegistrableSourceAnchor Observation Scope Lineage) :
    anchor.identity ≠ anchor.complementIdentity :=
  anchor.identity_ne_complement_identity

/-- The distinguished `null` point of any coherent registry installs a source
anchor. -/
def registered
    (Observation : ComplementObservationCarrier.{u})
    (scope : Scope) (lineage : Lineage) :
    MinimalRegistrableSourceAnchor Observation Scope Lineage where
  identity := Observation.null
  identity_ne_complement_identity := Observation.null_ne_complement_null
  scope := scope
  lineage := lineage

/-- The canonical two-point registry supplies the least O0-compliant anchor
for any chosen scope and lineage. -/
def canonical (scope : Scope) (lineage : Lineage) :
    MinimalRegistrableSourceAnchor canonicalComplementPair Scope Lineage :=
  registered canonicalComplementPair scope lineage

/-- Every coherent registry receives the unique structure-preserving map from
the canonical two-point orbit.  This is a registration readout, not a source
or event producer. -/
def canonicalRegistration
    (Observation : ComplementObservationCarrier.{u}) :
    ComplementObservationHom canonicalComplementPair Observation :=
  canonicalPairHom Observation

theorem canonicalRegistration_injective
    (Observation : ComplementObservationCarrier.{u}) :
    Function.Injective (canonicalRegistration Observation).toFun :=
  canonical_pair_hom_injective Observation

end MinimalRegistrableSourceAnchor

/-- Explicit same-registry anchor transport.  The whole carrier map commutes
with complement, maps the exact old source identity to the new identity, and
preserves scope and debt lineage.  This is the only ordinary route by which a
receipt may change its anchor presentation. -/
structure SourceAnchorTransport
    {Observation : ComplementObservationCarrier.{u}}
    {Scope Lineage : Type u}
    (source target :
      MinimalRegistrableSourceAnchor Observation Scope Lineage) : Type u where
  toFun : Observation.Carrier → Observation.Carrier
  injective : Function.Injective toFun
  map_identity : toFun source.identity = target.identity
  map_complement :
    ∀ point, toFun (Observation.complement point) =
      Observation.complement (toFun point)
  scope_eq : source.scope = target.scope
  lineage_eq : source.lineage = target.lineage

namespace SourceAnchorTransport

variable {Observation : ComplementObservationCarrier.{u}}
variable {Scope Lineage : Type u}
variable
  {source target : MinimalRegistrableSourceAnchor Observation Scope Lineage}

def refl
    (source : MinimalRegistrableSourceAnchor Observation Scope Lineage) :
    SourceAnchorTransport source source where
  toFun := id
  injective := Function.injective_id
  map_identity := rfl
  map_complement := fun _ => rfl
  scope_eq := rfl
  lineage_eq := rfl

def trans
    {middle : MinimalRegistrableSourceAnchor Observation Scope Lineage}
    (first : SourceAnchorTransport source middle)
    (second : SourceAnchorTransport middle target) :
    SourceAnchorTransport source target where
  toFun := fun point => second.toFun (first.toFun point)
  injective := second.injective.comp first.injective
  map_identity := by rw [first.map_identity, second.map_identity]
  map_complement := by
    intro point
    rw [first.map_complement, second.map_complement]
  scope_eq := first.scope_eq.trans second.scope_eq
  lineage_eq := first.lineage_eq.trans second.lineage_eq

theorem map_complementIdentity
    (transport : SourceAnchorTransport source target) :
    transport.toFun source.complementIdentity = target.complementIdentity := by
  calc
    transport.toFun source.complementIdentity =
        Observation.complement (transport.toFun source.identity) :=
      transport.map_complement source.identity
    _ = Observation.complement target.identity :=
      congrArg Observation.complement transport.map_identity
    _ = target.complementIdentity := rfl

end SourceAnchorTransport

/-- U8-style source revision receipt between possibly different O0
registries.  Revision is not an ordinary lifecycle receipt: it must expose a
whole-carrier map, exact identity commuting, a scope non-expansion witness, an
exact translation of the old debt lineage, and an explicit semantic-change
record.  Concrete domains still have to generate each field from their actual
meta-update; this structure does not manufacture a revision. -/
structure SourceAnchorMetaUpdate
    {SourceScope TargetScope SourceLineage TargetLineage Change : Type u}
    {SourceObservation TargetObservation :
      ComplementObservationCarrier.{u}}
    (scopePermitted : SourceScope → TargetScope → Prop)
    (source : MinimalRegistrableSourceAnchor
      SourceObservation SourceScope SourceLineage)
    (target : MinimalRegistrableSourceAnchor
      TargetObservation TargetScope TargetLineage) : Type (u + 1) where
  observation : ComplementObservationHom SourceObservation TargetObservation
  observation_injective : Function.Injective observation.toFun
  identity_eq : observation.toFun source.identity = target.identity
  scope_nonexpanding : scopePermitted source.scope target.scope
  translateLineage : SourceLineage → TargetLineage
  lineage_eq : translateLineage source.lineage = target.lineage
  semanticChange : Change

namespace SourceAnchorMetaUpdate

variable {SourceScope TargetScope SourceLineage TargetLineage Change : Type u}
variable {SourceObservation TargetObservation :
  ComplementObservationCarrier.{u}}
variable {scopePermitted : SourceScope → TargetScope → Prop}
variable
  {source : MinimalRegistrableSourceAnchor
    SourceObservation SourceScope SourceLineage}
  {target : MinimalRegistrableSourceAnchor
    TargetObservation TargetScope TargetLineage}

theorem map_complementIdentity
    (update : SourceAnchorMetaUpdate (Change := Change)
      scopePermitted source target) :
    update.observation.toFun source.complementIdentity =
      target.complementIdentity := by
  calc
    update.observation.toFun source.complementIdentity =
        TargetObservation.complement
          (update.observation.toFun source.identity) :=
      update.observation.map_complement source.identity
    _ = TargetObservation.complement target.identity :=
      congrArg TargetObservation.complement update.identity_eq
    _ = target.complementIdentity := rfl

end SourceAnchorMetaUpdate

end ResponsibilityLifecycle
end SaturationMonoid
