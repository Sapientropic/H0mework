import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherPatchInventory MotherLedgerRoot
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

abbrev Projection (material : M) := {code : B // bit material 0 code}

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeLedgerSource N V}
    (coordinates : Coordinates source.source) (material : M)

abbrev Active (projection : Projection material) (point : Point source.source) :=
  {code : B // r3 material 1 projection.val (coordinates.occurrence point) code}

abbrev Inactive (projection : Projection material) (point : Point source.source) :=
  {code : B // r3 material 2 projection.val (coordinates.occurrence point) code}

abbrev Payload (projection : Projection material) (point : Point source.source)
    (active : Active coordinates material projection point) :=
  {code : B // r4 material 3 projection.val (coordinates.occurrence point) active.val code}

def classificationGraph (projection : Projection material) (point : Point source.source) :
    Active coordinates material projection point ⊕ Inactive coordinates material projection point → Prop
  | .inl active => r3 material 4 projection.val (coordinates.occurrence point) active.val
  | .inr inactive => r3 material 5 projection.val (coordinates.occurrence point) inactive.val

structure Check : Prop where
  classify : ∀ (projection : Projection material) (point : Point source.source),
    ∃! result, classificationGraph coordinates material projection point result
  project : ∀ (projection : Projection material) (point : Point source.source)
    (active : Active coordinates material projection point),
    ∃! payload : Payload coordinates material projection point active,
      r4 material 6 projection.val (coordinates.occurrence point) active.val payload.val

/-- The classifier keeps the complete selected active/inactive member. The
projector is formed at every active member, including those not classified. -/
def projectionLaw (checked : Check coordinates material) : SourceNativeProjectionLaw source where
  Projection := Projection material
  ActiveAt := fun projection {current} event => Active coordinates material projection ⟨current, event⟩
  InactiveAt := fun projection {current} event => Inactive coordinates material projection ⟨current, event⟩
  classify := fun projection {current} event => Classical.choose (checked.classify projection ⟨current, event⟩)
  PayloadAt := fun projection {current} event active => Payload coordinates material projection ⟨current, event⟩ active
  project := fun projection {current} event active => Classical.choose (checked.project projection ⟨current, event⟩ active)

abbrev ProjectionValue := Σ root : RootValue, SourceNativeProjectionLaw root.2.2.source

def formProjectionParts (parent material : M) : Option ProjectionValue :=
  (formRoot parent).pbind (fun root formed =>
    let coordinates := rootCoordinates parent root formed
    if checked : Check coordinates material then some ⟨root, projectionLaw coordinates material checked⟩
    else none)

def formProjection (material : M) : Option ProjectionValue :=
  let parts := MotherHigherLawValue.split material
  formProjectionParts parts.1 parts.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
