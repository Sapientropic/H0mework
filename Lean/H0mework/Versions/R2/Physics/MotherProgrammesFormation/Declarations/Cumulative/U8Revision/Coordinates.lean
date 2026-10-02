import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev ChangeTotal (N : WorldRelationNetwork.{0}) := Σ support first last, N.SemanticChangeAt support first last

structure Coordinates (N : WorldRelationNetwork.{0}) where
  network : MotherActionTranslation.Coordinates (rank := rank) N
  change : ChangeTotal N ↪ B

def changeTotalEquiv {N G : WorldRelationNetwork.{0}} (p : MotherNetworkOrigin.Presentation N G) :
    ChangeTotal N ≃ ChangeTotal G :=
  (Equiv.sigmaCongrRight (fun support =>
    (Equiv.sigmaCongrRight (fun first =>
      (Equiv.sigmaCongrRight (fun last => p.semanticChangeAt support first last)).trans
        (Equiv.sigmaCongrLeft (β := fun last => G.SemanticChangeAt (p.support support) (p.claim first) last) p.claim))).trans
      (Equiv.sigmaCongrLeft (β := fun first => Σ last, G.SemanticChangeAt (p.support support) first last) p.claim))).trans
    (Equiv.sigmaCongrLeft (β := fun support => Σ first last, G.SemanticChangeAt support first last) p.support)

private def canonicalChange (material : M) (checked : MotherArenaNetwork.Check material) :
    ChangeTotal (MotherArenaSource.network material checked) ↪ B :=
  MotherArenaObligation.sigmaEmbedding ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
    (fun _ => MotherArenaObligation.sigmaEmbedding ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
      (fun _ => MotherArenaObligation.sigmaEmbedding ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
        (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)))

def changeOfNetwork (material : M) (N : WorldRelationNetwork.{0})
    (formed : MotherArenaNetwork.formNetwork material = some N) : ChangeTotal N ↪ B := by
  let checked := MotherArenaSource.network_check formed
  have same : MotherArenaSource.network material checked = N :=
    Option.some.inj ((MotherArenaSource.network_formed material checked).symm.trans formed)
  exact Eq.mp (congrArg (fun network => ChangeTotal network ↪ B) same) (canonicalChange material checked)

/-- The extra semantic-change fibre is read from the actual full network;
no new carrier or embedding assumption is introduced. -/
def coordinatesOfRoot {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    (material : M) (output : MotherAuthorityCoordinates.Output)
    (formed : MotherArenaTheory.formTheory material = some output)
    (presentation : MotherAuthorityRoot.Presentation root output.1.1 output.1.2 output.2) : Coordinates (rank := rank) N where
  network := MotherActionTranslation.coordinatesOfRoot material output formed presentation
  change := (changeTotalEquiv presentation.network).toEmbedding.trans
    (changeOfNetwork (MotherArenaHigher.split rank (MotherAuthorityCoordinates.nativeMaterial material)).1 _
      (MotherArenaAdmission.source_network_formed _ _ (MotherAuthorityCoordinates.native_formed material output formed)))

variable {N : WorldRelationNetwork.{0}} (coordinates : Coordinates (rank := rank) N)

def holdsMember (support : N.Support) (claim : N.Claim) : N.HoldsAt support claim ↪ B :=
  ((Function.Embedding.sigmaMk (β := N.HoldsAt support) claim).trans
    (Function.Embedding.sigmaMk (β := fun support => Σ claim, N.HoldsAt support claim) support)).trans coordinates.network.holds

def changeMember (support : N.Support) (first last : N.Claim) : N.SemanticChangeAt support first last ↪ B :=
  (((Function.Embedding.sigmaMk (β := N.SemanticChangeAt support first) last).trans
    (Function.Embedding.sigmaMk (β := fun first => Σ last, N.SemanticChangeAt support first last) first)).trans
    (Function.Embedding.sigmaMk (β := fun support => Σ first last, N.SemanticChangeAt support first last) support)).trans coordinates.change

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
