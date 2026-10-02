import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffPayload.Codes

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeAuthoritySource N V} {events : EventFamily source}
    (next : EventPoint events → NextRoot N)
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev InitialOccurrence (point : EventPoint events) :=
  (next point).2.toRoot.actual.OccurrenceAt (next point).2.toRoot.source.initial

abbrev TargetEntry (point : EventPoint events) :=
  OpenResponsibilityAt N ((next point).2.toRoot.supportAt (next point).2.toRoot.source.initial)

abbrev TargetPoint := Σ point : EventPoint events, TargetEntry next point

abbrev DebtAt (point : TargetPoint next) :=
  Debt (source.restructuringSource.source.toRootSource.account.supportOf point.1.1.occurrence) point.2

structure Coordinates where
  point : EventPoint events ↪ B
  event : ∀ index, events index ↪ B
  initialOccurrence : ∀ point, InitialOccurrence next point ↪ B
  entry : ∀ support, OpenResponsibilityAt N support ↪ B

structure Values where
  occurrencePresentation : ∀ point : EventPoint events,
    ConstructivePresentation (InitialOccurrence next point) (events point.1)
  targetDebtOrigin : ∀ point : TargetPoint next, DebtAt next point

variable (coordinates : Coordinates (rank := rank) next)

def targetAddress : TargetPoint next ↪ B :=
  MotherArenaObligation.sigmaEmbedding coordinates.point
    (fun point => coordinates.entry ((next point).2.toRoot.supportAt (next point).2.toRoot.source.initial))

def debtMemberAddress (point : TargetPoint next) : DebtAt next point ↪ B :=
  debtAddress coordinates.entry
    (source.restructuringSource.source.toRootSource.account.supportOf point.1.1.occurrence) point.2

/-- Typed inner graph factory. Its source schemas and coordinates come from
the already formed source/event/root outputs; the only value input is mother
material. Original CP and debt functions never enter this function. -/
def formValues (material : M) : Option (Values next) :=
  let parts := MotherArenaHigher.split rank material
  (MotherArenaAdmission.formPresentationSection coordinates.point coordinates.initialOccurrence
    (fun point => coordinates.event point.1) parts.1).bind (fun presentations =>
      (MotherArenaReceipts.NativeSection.form (targetAddress next coordinates)
        (debtMemberAddress next coordinates) parts.2).map (fun debts => ⟨presentations, debts⟩))

theorem every_values (values : Values next) :
    ∃ material : M, formValues next coordinates material = some values := by
  obtain ⟨presentationMaterial, presentationsFormed⟩ :=
    MotherArenaAdmission.every_presentation_section coordinates.point coordinates.initialOccurrence
      (fun point => coordinates.event point.1) values.occurrencePresentation
  obtain ⟨debtMaterial, debtsFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (targetAddress next coordinates) (debtMemberAddress next coordinates) values.targetDebtOrigin
  refine ⟨MotherArenaHigher.pack rank (presentationMaterial, debtMaterial), ?_⟩
  simp only [formValues, MotherArenaHigher.split_pack, presentationsFormed, Option.bind_some,
    debtsFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
