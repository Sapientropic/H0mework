import H0mework.Foundation.Inquiry.ObstructionLineage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Presentations

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {U7 : U7ProducerCalculus N}
    (source : U7ActualSuccessorSource N U7)
    {support : N.Support} {obstruction : N.ObstructionAt support} {demand : U7.DemandAt obstruction}
    (event : source.EventAt obstruction demand)

/-- The original source receipts determine every data-valued row outcome.
Only the redirect's original conservation equations remain to be checked. -/
def formCompilation (disposition : U7ObstructionDispositionAt N U7 obstruction demand) :
    Option (GeneratedU7ObstructionEvolutionAt source event) :=
  match disposition with
  | .settled receipt => some ⟨.settled receipt, ⟨⟨receipt⟩, rfl⟩⟩
  | .requiresTheoryAudit extension => some ⟨.requiresTheoryAudit extension, PUnit.unit⟩
  | @U7ObstructionDispositionAt.redirected _ _ _ _ _ successor transition =>
      if conserved : OpenResponsibilityAt.claim (U7ActualSuccessorSource.demandEntry event) =
          OpenResponsibilityAt.claim (U7ActualSuccessorSource.demandEntry (source.emit successor)) ∧
          OpenResponsibilityAt.progressBudget (U7ActualSuccessorSource.demandEntry (source.emit successor)) ≤
            OpenResponsibilityAt.progressBudget (U7ActualSuccessorSource.demandEntry event) then
        some ⟨.redirected transition,
          ⟨.transferred transition.worldReceipt rfl conserved.1 conserved.2, rfl⟩⟩
      else none

theorem formCompilation_recovers (compiled : GeneratedU7ObstructionEvolutionAt source event) :
    formCompilation source event compiled.disposition = some compiled := by
  rcases compiled with ⟨disposition, row⟩
  cases disposition with
  | settled receipt =>
      rcases row with ⟨⟨chosen⟩, same⟩
      cases same
      rfl
  | requiresTheoryAudit extension =>
      cases row
      rfl
  | @redirected successor transition =>
      rcases row with ⟨evolution, selected⟩
      cases evolution with
      | carried supportEq entryEq => cases selected
      | maintained anchor incidence lineage responsibility claim budget => cases selected
      | transferred receipt lineage claim budget =>
          dsimp only at selected
          cases selected
          exact dif_pos ⟨claim, budget⟩

/-- The projection to a disposition retains the full original U7 compiled
value because the actual receipt determines its accompanying whole-row data. -/
theorem disposition_injective :
    Function.Injective (fun compiled : GeneratedU7ObstructionEvolutionAt source event => compiled.disposition) := by
  intro first last same
  have restored := formCompilation_recovers source event first
  exact Option.some.inj (restored.symm.trans
    ((congrArg (formCompilation source event) same).trans (formCompilation_recovers source event last)))

abbrev EventTotal := Σ support, Σ obstruction : N.ObstructionAt support,
  Σ demand : U7.DemandAt obstruction, source.EventAt obstruction demand

abbrev DispositionAt (point : EventTotal source) :=
  U7ObstructionDispositionAt N U7 point.2.1 point.2.2.1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7
