import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Retract

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionTranslation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}

local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure Coordinates (N : WorldRelationNetwork.{0}) where
  support : N.Support ↪ B
  anchor : N.Anchor ↪ B
  incidence : N.Incidence ↪ B
  lineage : N.Lineage ↪ B
  responsibility : N.Responsibility ↪ B
  claim : N.Claim ↪ B
  entry : ∀ support, OpenResponsibilityAt N support ↪ B
  holds : (Σ support claim, N.HoldsAt support claim) ↪ B
  disposition : (Σ support kind, N.DispositionAt support kind) ↪ B

structure Basis (OldN NewN : WorldRelationNetwork.{0}) where
  support : ConstructiveRetract OldN.Support NewN.Support
  anchor : ConstructiveRetract OldN.Anchor NewN.Anchor
  incidence : ConstructiveRetract OldN.Incidence NewN.Incidence
  lineage : ConstructiveRetract OldN.Lineage NewN.Lineage
  responsibility : ConstructiveRetract OldN.Responsibility NewN.Responsibility
  claim : ConstructiveRetract OldN.Claim NewN.Claim

def basisOf {OldN NewN : WorldRelationNetwork.{0}}
    (original : TypedSemanticWorldNetworkTranslationAt OldN NewN) : Basis OldN NewN :=
  ⟨original.support, original.anchor, original.incidence, original.lineage, original.responsibility, original.claim⟩

def unitAddress (rank : Ordinal.{0}) : Unit ↪ MotherArenaHigher.Base rank :=
  ⟨fun _ => MotherArenaHigher.point rank (.inl ()), fun _ _ _ => Subsingleton.elim _ _⟩

def formOne {A C : Type} (left : A ↪ B) (right : C ↪ B) (material : M) :
    Option (ConstructiveRetract A C) :=
  (MotherActionRetract.form (unitAddress rank) (fun _ => left) (fun _ => right) material).map (fun values => values ())

theorem every_one {A C : Type} (left : A ↪ B) (right : C ↪ B) (original : ConstructiveRetract A C) :
    ∃ material : M, formOne left right material = some original := by
  obtain ⟨material, formed⟩ := MotherActionRetract.every_retract
    (unitAddress rank) (fun _ => left) (fun _ => right) (fun _ => original)
  exact ⟨material, by simp only [formOne, formed, Option.map_some]⟩

variable {OldN NewN : WorldRelationNetwork.{0}}
    (old : Coordinates (rank := rank) OldN) (new : Coordinates (rank := rank) NewN)

def formBasis (material : M) : Option (Basis OldN NewN) :=
  let first := MotherArenaHigher.split rank material
  let second := MotherArenaHigher.split rank first.2
  let third := MotherArenaHigher.split rank second.2
  let fourth := MotherArenaHigher.split rank third.2
  let fifth := MotherArenaHigher.split rank fourth.2
  (formOne old.support new.support first.1).bind (fun support =>
  (formOne old.anchor new.anchor second.1).bind (fun anchor =>
  (formOne old.incidence new.incidence third.1).bind (fun incidence =>
  (formOne old.lineage new.lineage fourth.1).bind (fun lineage =>
  (formOne old.responsibility new.responsibility fifth.1).bind (fun responsibility =>
  (formOne old.claim new.claim fifth.2).map (fun claim =>
    ⟨support, anchor, incidence, lineage, responsibility, claim⟩))))))

theorem every_basis (original : Basis OldN NewN) :
    ∃ material : M, formBasis old new material = some original := by
  obtain ⟨supportM, supportFormed⟩ := every_one old.support new.support original.support
  obtain ⟨anchorM, anchorFormed⟩ := every_one old.anchor new.anchor original.anchor
  obtain ⟨incidenceM, incidenceFormed⟩ := every_one old.incidence new.incidence original.incidence
  obtain ⟨lineageM, lineageFormed⟩ := every_one old.lineage new.lineage original.lineage
  obtain ⟨responsibilityM, responsibilityFormed⟩ := every_one old.responsibility new.responsibility original.responsibility
  obtain ⟨claimM, claimFormed⟩ := every_one old.claim new.claim original.claim
  refine ⟨MotherArenaHigher.pack rank (supportM, MotherArenaHigher.pack rank (anchorM,
    MotherArenaHigher.pack rank (incidenceM, MotherArenaHigher.pack rank (lineageM,
      MotherArenaHigher.pack rank (responsibilityM, claimM))))), ?_⟩
  simp only [formBasis, MotherArenaHigher.split_pack, supportFormed, anchorFormed, incidenceFormed,
    lineageFormed, responsibilityFormed, claimFormed, Option.bind_some, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionTranslation
