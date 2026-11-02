import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital.InitialPeriod
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital.Permission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Failure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Source.ProgrammeControl
open Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (origin : Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)

/-- Both cases belong to the registered original event. The positive case
has actual material payments; the negative carries the precise obstruction. -/
theorem the_original_initial_source_materializes_public_life_or_its_exact_obstruction :
    match InitialAdmission.select origin with
    | .admitted admission =>
        Exit.Necessity.AllNeedsPaid (Physical.Public.interpreter input) (firstBody origin admission).1
          (originalMembers origin) (firstBody origin admission).2 ∧
        ¬ Nonempty (Kernel.CapitalRelationKernel (Physical.Public.interpreter input)
          (firstBody origin admission).1 (firstBody origin admission).2) ∧
        (Enactment.Admitted.firstSuccessor origin admission).targetCurrent = Enactment.Admitted.bodyNext origin ∧
        (Enactment.Admitted.bodyNext origin).account = origin.native.account origin.visit.current ∧
        (∀ entry, ((Enactment.Admitted.initialLedger origin admission).forward entry).1 = entry.1 ∧
          ((Enactment.Admitted.initialLedger origin admission).forward entry).claim = entry.claim ∧
          ((Enactment.Admitted.initialLedger origin admission).forward entry).progressBudget = entry.progressBudget)
    | .obstructed failed =>
        InitialAdmission.Failure.publicObstruction origin failed = failed ∧
        (InitialAdmission.Failure.generated origin failed).answer =
          Macro.Raw.reportAt origin.native origin.data origin.reader origin.germ ∧
        (InitialAdmission.Failure.generated origin failed).target.targetRoot =
          Macro.Raw.Target.targetRoot origin.native origin.data origin.reader origin.basis origin.visit origin.germ := by
  cases result : InitialAdmission.select origin with
  | admitted admission =>
      exact ⟨the_actual_initial_public_body_pays_all_original_life_and_maintenance origin admission,
        Functions.open_permissions_have_no_capital_kernel _ (fun _ _ _ => rfl) _ _,
        Enactment.Admitted.first_successor_is_the_actual_public_body origin admission, rfl,
        Enactment.Admitted.initial_ledger_preserves_every_original_row origin admission⟩
  | obstructed failed => exact ⟨rfl, rfl, rfl⟩

#print axioms the_original_initial_source_materializes_public_life_or_its_exact_obstruction

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital
