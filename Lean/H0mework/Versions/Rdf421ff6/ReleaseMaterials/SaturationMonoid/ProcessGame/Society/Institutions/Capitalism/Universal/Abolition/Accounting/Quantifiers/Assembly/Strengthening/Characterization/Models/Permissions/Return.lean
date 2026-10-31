import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Classification

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Return

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
noncomputable section

def dispose : Request Bool Unit Bool Unit Unit := ⟨false,[],false,[],.use false [((),1)] .external⟩
def body : RawEvent Bool Unit Bool Unit Unit := Permissions.body ++ [dispose]
def item (clock : ℚ) (round : Nat) (index : Fin 4) :=
  itemAt (law true false) (state clock round) body
    ⟨index.val,by simpa only [body,Permissions.body,Kernel.Consumers.StoredAccess.body,
      List.length_append,List.length_cons,List.length_nil] using index.isLt⟩

def proposal (clock : ℚ) (round : Nat) : Proposal (law true false) (state clock round) body where
  access := {
    access := item clock round 0
    necessity := item clock round 2
    mode := .acquired
    accessHolder := true
    recipient := true
    port := false
    accessGood := ()
    necessityGood := ()
    delivery := [] }
  reciprocity := .returnFlow () () [⟨item clock round 1,(false,())⟩]
  disposal := {position := item clock round 3,request := dispose,good := ()}

def evidence (clock : ℚ) (round : Nat) : ActualSurplus.Evidence (law true false) (state clock round) body :=
  .routedConsumption (item clock round 3) () [⟨item clock round 1,(false,())⟩]

theorem source_checks (clock : ℚ) (round : Nat) :
    (proposal clock round).Checks (law true false) (state clock round) body ∧
      ActualSurplus.rawChecks (law true false) (state clock round) body (proposal clock round) (evidence clock round) := by
  simp [proposal,evidence,Proposal.Checks,AccessProposal.Checks,AccessProposal.RequiredUsePaid,
    AccessProposal.Accessed,ReciprocityProposal.Checks,DisposalProposal.Checks,
    DisposalProposal.holder,DisposalProposal.initialHolder,DisposalProposal.DisposalKind,
    DisposalProposal.allocationChecks,DisposalProposal.AllocationChain,
    ActualSurplus.rawChecks,ActualSurplus.outputBasis,ActualSurplus.evidenceChecks,
    ActualSurplus.financialAlignment,ActualSurplus.controlAlong,ActualSurplus.flowLegAllowed,
    ActualSurplus.performedAt,AccessProposal.controller,Follows,PrivatePhase,item,itemAt,law,body,dispose,
    Permissions.body,Kernel.Consumers.StoredAccess.law,Kernel.Consumers.StoredAccess.body,
    Kernel.Consumers.StoredAccess.current,state,RawLaw.rawItems,RawLaw.execute,RawLaw.step,
    RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawLaw.ClaimGuard,
    RawLaw.debit,RawLaw.credit,RawLaw.requiredPorts,RawLaw.paidStep,RawLaw.next,RawLaw.nextClaims,
    RawLaw.actualDebit,RawLaw.actualCredit,flowAt,locate,amount,NonnegativeBundle,RawPolicy.eval]

def generated (clock : ℚ) (round : Nat) : ActualSurplus.Witness (law true false) (state clock round) body :=
  (ActualSurplus.compileProposal (law true false) (state clock round) body
    (proposal clock round) (evidence clock round)).get (by
      simp only [ActualSurplus.compileProposal,compile,dif_pos (source_checks clock round).1,
        Option.bind_some,ActualSurplus.compile,dif_pos (source_checks clock round).2];rfl)

theorem actual_appropriation_is_source_generated_at_every_clock (clock : ℚ) (round : Nat) :
    ActualSurplus.compileProposal (law true false) (state clock round) body
      (proposal clock round) (evidence clock round) = some (generated clock round) := by
  simp only [generated,ActualSurplus.compileProposal,compile,dif_pos (source_checks clock round).1,
    Option.bind_some,ActualSurplus.compile,dif_pos (source_checks clock round).2,Option.get_some]

theorem actual_return_and_disposal_do_not_erase_necessary_living :
    Exit.Necessity.AllNeedsPaid (law true false) (state 0 0) [false,true] body ∧
      (law true false).totalDebit ((law true false).rawItems (state 0 0) body) false () = 2 ∧
      ((law true false).next (state 0 0) body).stock false () = 1 := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Return
