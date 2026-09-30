import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.RestructuringRestriction.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.RecoveryConsumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.TheoryTransport.Restriction
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ProjectionRestriction.Native

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

/-- The inverse source equality supplies the actual dependent indices;
every field value is the output of its complete native restriction. -/
def assemble (old : SourceNativeAuthoritySource N V)
    (source : SourceNativeRestructuringLedgerSource N V) (sourceEq : source = old.restructuringSource)
    (admission : SourceNativeCompleteEventInventoryAdmission old.restructuringSource)
    (surface : TheoryState N) (projection : SourceNativeProjectionLaw old.restructuringSource.toLedgerSource) :
    SourceNativeAuthoritySource N V where
  restructuringSource := source
  eventInventoryAdmission := Equiv.cast (congrArg SourceNativeCompleteEventInventoryAdmission sourceEq.symm) admission
  lawSurface := surface
  projectionLaw := Equiv.cast (congrArg (fun value : SourceNativeRestructuringLedgerSource N V =>
    SourceNativeProjectionLaw value.toLedgerSource) sourceEq.symm) projection

theorem assemble_eq (old : SourceNativeAuthoritySource N V)
    (source : SourceNativeRestructuringLedgerSource N V) (sourceEq : source = old.restructuringSource)
    (admission : SourceNativeCompleteEventInventoryAdmission old.restructuringSource) (admissionEq : admission = old.eventInventoryAdmission)
    (surface : TheoryState N) (surfaceEq : surface = old.lawSurface)
    (projection : SourceNativeProjectionLaw old.restructuringSource.toLedgerSource) (projectionEq : projection = old.projectionLaw) :
    assemble old source sourceEq admission surface projection = old := by
  cases sourceEq
  cases admissionEq
  cases surfaceEq
  cases projectionEq
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
