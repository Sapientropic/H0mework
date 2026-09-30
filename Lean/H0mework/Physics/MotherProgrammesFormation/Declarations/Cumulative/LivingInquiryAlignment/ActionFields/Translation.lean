import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.TranslationBasis

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionTranslation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}} {OldN NewN : WorldRelationNetwork.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev HoldsTotal (N : WorldRelationNetwork.{0}) := Σ support claim, N.HoldsAt support claim
abbrev DispositionTotal (N : WorldRelationNetwork.{0}) := Σ support kind, N.DispositionAt support kind

structure Rest (basis : Basis OldN NewN) where
  ledger : (support : OldN.Support) → ConstructiveRetract
    (OpenResponsibilityAt OldN support) (OpenResponsibilityAt NewN (basis.support.forward support))
  holds : (point : HoldsTotal OldN) →
    NewN.HoldsAt (basis.support.forward point.1) (basis.claim.forward point.2.1)
  disposition : (point : DispositionTotal OldN) →
    NewN.DispositionAt (basis.support.forward point.1) point.2.1

def restOf (original : TypedSemanticWorldNetworkTranslationAt OldN NewN) : Rest (basisOf original) where
  ledger := original.oldOpenLedger
  holds := fun point => original.oldHoldsSurvives point.1 point.2.1 point.2.2
  disposition := fun point => original.oldDispositionSurvives point.1 point.2.1 point.2.2

variable (old : Coordinates (rank := rank) OldN) (new : Coordinates (rank := rank) NewN)

def holdsMember (basis : Basis OldN NewN) (point : HoldsTotal OldN) :
    NewN.HoldsAt (basis.support.forward point.1) (basis.claim.forward point.2.1) ↪ B :=
  ((Function.Embedding.sigmaMk (β := NewN.HoldsAt (basis.support.forward point.1))
    (basis.claim.forward point.2.1)).trans (Function.Embedding.sigmaMk
      (β := fun support => Σ claim, NewN.HoldsAt support claim) (basis.support.forward point.1))).trans new.holds

def dispositionMember (basis : Basis OldN NewN) (point : DispositionTotal OldN) :
    NewN.DispositionAt (basis.support.forward point.1) point.2.1 ↪ B :=
  ((Function.Embedding.sigmaMk (β := NewN.DispositionAt (basis.support.forward point.1))
    point.2.1).trans (Function.Embedding.sigmaMk
      (β := fun support => Σ kind, NewN.DispositionAt support kind) (basis.support.forward point.1))).trans new.disposition

def formRest (basis : Basis OldN NewN) (material : M) : Option (Rest basis) :=
  let first := MotherArenaHigher.split rank material
  let second := MotherArenaHigher.split rank first.2
  (MotherActionRetract.form old.support old.entry (fun support => new.entry (basis.support.forward support)) first.1).bind (fun ledger =>
  (MotherArenaReceipts.NativeSection.form old.holds (holdsMember new basis) second.1).bind (fun holds =>
  (MotherArenaReceipts.NativeSection.form old.disposition (dispositionMember new basis) second.2).map (fun disposition =>
    ⟨ledger, holds, disposition⟩)))

theorem every_rest (basis : Basis OldN NewN) (original : Rest basis) :
    ∃ material : M, formRest old new basis material = some original := by
  obtain ⟨ledgerM, ledgerFormed⟩ := MotherActionRetract.every_retract old.support old.entry
    (fun support => new.entry (basis.support.forward support)) original.ledger
  obtain ⟨holdsM, holdsFormed⟩ := MotherArenaReceipts.NativeSection.every_section old.holds
    (holdsMember new basis) original.holds
  obtain ⟨dispositionM, dispositionFormed⟩ := MotherArenaReceipts.NativeSection.every_section old.disposition
    (dispositionMember new basis) original.disposition
  refine ⟨MotherArenaHigher.pack rank (ledgerM, MotherArenaHigher.pack rank (holdsM, dispositionM)), ?_⟩
  simp only [formRest, MotherArenaHigher.split_pack, ledgerFormed, holdsFormed,
    dispositionFormed, Option.bind_some, Option.map_some]

structure Check (basis : Basis OldN NewN) (rest : Rest basis) : Prop where
  anchor : ∀ support, basis.anchor.forward (OldN.anchorAt support) = NewN.anchorAt (basis.support.forward support)
  incidence : ∀ support, basis.incidence.forward (OldN.incidenceAt support) = NewN.incidenceAt (basis.support.forward support)
  lineage : ∀ support, basis.lineage.forward (OldN.lineageAt support) = NewN.lineageAt (basis.support.forward support)
  claim : ∀ support entry, basis.claim.forward (OpenResponsibilityAt.claim entry) =
    OpenResponsibilityAt.claim ((rest.ledger support).forward entry)
  budget : ∀ support entry, OpenResponsibilityAt.progressBudget ((rest.ledger support).forward entry) =
    OpenResponsibilityAt.progressBudget entry

def assemble (basis : Basis OldN NewN) (rest : Rest basis) (check : Check basis rest) :
    TypedSemanticWorldNetworkTranslationAt OldN NewN where
  support := basis.support
  anchor := basis.anchor
  incidence := basis.incidence
  lineage := basis.lineage
  responsibility := basis.responsibility
  claim := basis.claim
  anchor_commutes := check.anchor
  incidence_commutes := check.incidence
  lineage_commutes := check.lineage
  oldOpenLedger := rest.ledger
  oldOpenClaim_commutes := check.claim
  oldOpenProgressBudget_commutes := check.budget
  oldHoldsSurvives := fun support claim holds => rest.holds ⟨support, claim, holds⟩
  oldDispositionSurvives := fun support kind disposition => rest.disposition ⟨support, kind, disposition⟩

def form (material : M) : Option (TypedSemanticWorldNetworkTranslationAt OldN NewN) :=
  let parts := MotherArenaHigher.split rank material
  (formBasis old new parts.1).bind (fun basis =>
  (formRest old new basis parts.2).bind (fun rest =>
    if check : Check basis rest then some (assemble basis rest check) else none))

theorem every_translation (original : TypedSemanticWorldNetworkTranslationAt OldN NewN) :
    ∃ material : M, form old new material = some original := by
  obtain ⟨basisM, basisFormed⟩ := every_basis old new (basisOf original)
  obtain ⟨restM, restFormed⟩ := every_rest old new (basisOf original) (restOf original)
  have check : Check (basisOf original) (restOf original) :=
    ⟨original.anchor_commutes, original.incidence_commutes, original.lineage_commutes,
      original.oldOpenClaim_commutes, original.oldOpenProgressBudget_commutes⟩
  refine ⟨MotherArenaHigher.pack rank (basisM, restM), ?_⟩
  simp only [form, MotherArenaHigher.split_pack, basisFormed, Option.bind_some, restFormed, dif_pos check]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionTranslation
