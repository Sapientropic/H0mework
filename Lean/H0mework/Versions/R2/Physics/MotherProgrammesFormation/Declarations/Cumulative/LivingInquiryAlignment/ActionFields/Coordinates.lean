import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Translation
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityCoordinates.Restriction

/-! These addresses are read from actual generated network fields and pulled
back through the already paid complete network presentation. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionTranslation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

private def natAddress (rank : Ordinal.{0}) : Nat ↪ MotherArenaHigher.Base rank where
  toFun := fun value => (MotherArenaHigher.baseReadEquiv rank).symm (fun _ _ => (value : ℝ))
  inj' := by
    intro first last same
    have sampled := congrFun (congrFun (congrArg (MotherArenaHigher.baseReadEquiv rank) same) (.inl ())) 0
    simp only [Equiv.apply_symm_apply] at sampled
    exact Nat.cast_injective sampled

private def kindNumber : WorldDispositionKind → Nat
  | .transfer => 0
  | .supportSettlement => 1
  | .lawSurfaceExtension => 2

private def kindAddress (rank : Ordinal.{0}) : WorldDispositionKind ↪ MotherArenaHigher.Base rank where
  toFun := fun kind => natAddress rank (kindNumber kind)
  inj' := by
    intro first last same
    have number := (natAddress rank).injective same
    cases first <;> cases last <;> simp_all only [kindNumber, reduceCtorEq, Nat.reduceEqDiff]

private def canonical (material : M) (checked : MotherArenaNetwork.Check material) :
    Coordinates (rank := rank) (MotherArenaSource.network material checked) where
  support := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  anchor := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  incidence := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  lineage := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  responsibility := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  claim := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  entry := fun _ => MotherArenaObligation.sigmaEmbedding
    ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
    (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
  holds := MotherArenaObligation.sigmaEmbedding
    ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
    (fun _ => MotherArenaObligation.sigmaEmbedding
      ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
      (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩))
  disposition := MotherArenaObligation.sigmaEmbedding
    ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
    (fun _ => MotherArenaObligation.sigmaEmbedding (kindAddress rank)
      (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩))

def coordinatesOfNetwork (material : M) (N : WorldRelationNetwork.{0})
    (formed : MotherArenaNetwork.formNetwork material = some N) : Coordinates (rank := rank) N := by
  let checked := MotherArenaSource.network_check formed
  have same : MotherArenaSource.network material checked = N :=
    Option.some.inj ((MotherArenaSource.network_formed material checked).symm.trans formed)
  exact Eq.mp (congrArg (Coordinates (rank := rank)) same) (canonical material checked)

def holdsTotalEquiv {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G) :
    HoldsTotal N ≃ HoldsTotal G :=
  (Equiv.sigmaCongrRight (fun support =>
    (Equiv.sigmaCongrRight (fun claim => n.holdsAt support claim)).trans
      (Equiv.sigmaCongrLeft n.claim))).trans
    (Equiv.sigmaCongrLeft (β := fun support => Σ claim, G.HoldsAt support claim) n.support)

def dispositionTotalEquiv {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G) :
    DispositionTotal N ≃ DispositionTotal G :=
  (Equiv.sigmaCongrRight (fun support => Equiv.sigmaCongrRight
    (fun kind => n.dispositionAt support kind))).trans
    (Equiv.sigmaCongrLeft (β := fun support => Σ kind, G.DispositionAt support kind) n.support)

def Coordinates.pullback {N G : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N G)
    (actual : Coordinates (rank := rank) G) : Coordinates (rank := rank) N where
  support := n.support.toEmbedding.trans actual.support
  anchor := n.anchor.toEmbedding.trans actual.anchor
  incidence := n.incidence.toEmbedding.trans actual.incidence
  lineage := n.lineage.toEmbedding.trans actual.lineage
  responsibility := n.responsibility.toEmbedding.trans actual.responsibility
  claim := n.claim.toEmbedding.trans actual.claim
  entry := fun support => (n.ledger support).toEmbedding.trans (actual.entry (n.support support))
  holds := (holdsTotalEquiv n).toEmbedding.trans actual.holds
  disposition := (dispositionTotalEquiv n).toEmbedding.trans actual.disposition

def coordinatesOfRoot {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    (material : M) (output : MotherAuthorityCoordinates.Output)
    (formed : MotherArenaTheory.formTheory material = some output)
    (presentation : MotherAuthorityRoot.Presentation root output.1.1 output.1.2 output.2) :
    Coordinates (rank := rank) N :=
  Coordinates.pullback presentation.network
    (coordinatesOfNetwork (MotherArenaHigher.split rank (MotherAuthorityCoordinates.nativeMaterial material)).1
      _ (MotherArenaAdmission.source_network_formed _ _ (MotherAuthorityCoordinates.native_formed material output formed)))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionTranslation
