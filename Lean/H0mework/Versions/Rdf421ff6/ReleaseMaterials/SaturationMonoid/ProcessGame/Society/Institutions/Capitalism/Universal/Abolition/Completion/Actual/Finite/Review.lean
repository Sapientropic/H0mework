import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital.Initial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital.Obstruction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Boundary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Source.ProgrammeControl Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => Macro.Runtime.ActivatedFrame (review := review)
  input depth count prefixLimit renewalLimit sourceDepth sourceCount
local notation "O" => Macro.Runtime.Frame (review := review)
  input depth count prefixLimit renewalLimit sourceDepth sourceCount

/-- This is a property of the existing mixed runtime boundary, not another
transition system. The original compiler pays public life or emits its exact
source obstruction; an already public boundary cannot restore private control. -/
def ReviewConclusion (state : F) (boundary : state.BoundaryAt) : Prop :=
  match boundary with
  | .original current raw =>
      let origin := current.controlOrigin raw.germ
      match InitialAdmission.select origin with
      | .admitted admission =>
          state.next.isPublic = true ∧
          Exit.Necessity.AllNeedsPaid (Physical.Public.interpreter input) (Capital.firstBody origin admission).1
            (Capital.originalMembers origin) (Capital.firstBody origin admission).2 ∧
          ¬ Nonempty (Kernel.CapitalRelationKernel (Physical.Public.interpreter input)
            (Capital.firstBody origin admission).1 (Capital.firstBody origin admission).2) ∧
          (Enactment.Admitted.bodyNext origin).account = origin.native.account origin.visit.current ∧
          (∀ entry, ((Enactment.Admitted.initialLedger origin admission).forward entry).1 = entry.1 ∧
            ((Enactment.Admitted.initialLedger origin admission).forward entry).claim = entry.claim ∧
            ((Enactment.Admitted.initialLedger origin admission).forward entry).progressBudget = entry.progressBudget)
      | .obstructed failed =>
          InitialAdmission.Failure.publicObstruction origin failed = failed ∧
          (InitialAdmission.Inquiry.state current.package (.finite current.visit) current.authority).compileInquiry
              (.raw raw.germ) = .actualAction (InitialAdmission.Failure.generated origin failed) ∧
          (InitialAdmission.Failure.generated origin failed).target.targetRoot =
            Macro.Raw.Target.targetRoot origin.native origin.data origin.reader origin.basis origin.visit origin.germ ∧
          (∀ entry, (((InitialAdmission.Failure.generated origin failed).target.initialOpenLedger).forward entry).1 = entry.1 ∧
            (((InitialAdmission.Failure.generated origin failed).target.initialOpenLedger).forward entry).claim = entry.claim ∧
            (((InitialAdmission.Failure.generated origin failed).target.initialOpenLedger).forward entry).progressBudget = entry.progressBudget)
  | .enacted origin admission current done =>
      (∀ word, ¬ Nonempty (Kernel.CapitalRelationKernel state.next.interpreter state.next.actualState.raw word)) ∧
      current.next.account = current.account ∧
      Macro.Public.Inquiry.compileUnit origin admission current.source current.reader (.finite current.visit)
        current.actual current.authority =
          .actualAction (Macro.Public.Inquiry.rawCore origin admission current.source current.reader (.finite current.visit)
            current.actual current.authority done)

theorem the_actual_boundary_generates_its_review_conclusion
    (state : F) (boundary : state.BoundaryAt) : ReviewConclusion state boundary := by
  cases boundary with
  | original current raw =>
      dsimp only [ReviewConclusion]
      cases chosen : InitialAdmission.select (current.controlOrigin raw.germ) with
      | admitted admission =>
          have paid := Capital.the_original_initial_source_materializes_public_life_or_its_exact_obstruction
            (current.controlOrigin raw.germ)
          rw [chosen] at paid
          refine ⟨?_, paid.1, paid.2.1, paid.2.2.2.1, paid.2.2.2.2⟩
          dsimp only [Macro.Runtime.ActivatedFrame.next]
          split
          · rename_i work selected
            cases selected.symm.trans raw.selected
          · rename_i germ selected
            have same : germ = raw.germ := Macro.Raw.QueryAt.raw.inj (selected.symm.trans raw.selected)
            cases same
            split
            · rfl
            · rename_i failed rejected
              change InitialAdmission.select (current.controlOrigin raw.germ) = .obstructed failed at rejected
              rw [chosen] at rejected
              cases rejected
      | obstructed failed =>
          have actual := Macro.Runtime.ActivatedFrame.original_boundary_is_consumed_by_the_actual_compiler current raw
          rw [chosen] at actual
          exact ⟨rfl, actual.1, rfl,
            Capital.an_obstruction_cannot_erase_a_bearer_claim_or_unspent_budget (current.controlOrigin raw.germ) failed⟩
  | enacted origin admission current done =>
      refine ⟨fun word => Functions.open_permissions_have_no_capital_kernel _
        (fun _ _ _ => rfl) _ word, ?_,
        Macro.Runtime.ActivatedFrame.enacted_boundary_is_consumed_by_the_actual_compiler origin admission current done⟩
      rw [Macro.Public.Runtime.Frame.next, dif_neg done]
      exact current.raw_reentry_keeps_the_literal_complete_account done

#print axioms the_actual_boundary_generates_its_review_conclusion

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite
