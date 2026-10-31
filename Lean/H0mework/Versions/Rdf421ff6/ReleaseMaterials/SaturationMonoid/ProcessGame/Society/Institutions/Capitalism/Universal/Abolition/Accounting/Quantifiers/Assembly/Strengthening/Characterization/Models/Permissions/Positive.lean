import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
noncomputable section

theorem source_checks (clock : ℚ) (round : Nat) :
    (proposal true false clock round).Checks (law true false) (state clock round) body := by
  simp [proposal,Proposal.Checks,AccessProposal.Checks,AccessProposal.RequiredUsePaid,
    AccessProposal.Accessed,ReciprocityProposal.Checks,DisposalProposal.Checks,
    DisposalProposal.holder,DisposalProposal.initialHolder,DisposalProposal.DisposalKind,
    DisposalProposal.allocationChecks,DisposalProposal.AllocationChain,
    AccessProposal.controller,Follows,PrivatePhase,item,itemAt,law,body,
    Kernel.Consumers.StoredAccess.law,Kernel.Consumers.StoredAccess.body,
    Kernel.Consumers.StoredAccess.current,state,RawLaw.rawItems,RawLaw.execute,
    RawLaw.step,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawLaw.ClaimGuard,RawLaw.debit,RawLaw.credit,RawLaw.requiredPorts,
    RawLaw.paidStep,RawLaw.next,RawLaw.nextClaims,RawLaw.actualDebit,RawLaw.actualCredit,
    flowAt,locate,amount,NonnegativeBundle,RawPolicy.eval]

def generated (clock : ℚ) (round : Nat) : CapitalRelationKernel (law true false) (state clock round) body :=
  (compile (law true false) (state clock round) body (proposal true false clock round)).get
    (by simp only [compile,dif_pos (source_checks clock round)]; rfl)

theorem every_clock_has_its_own_source_generated_capital (clock : ℚ) (round : Nat) :
    compile (law true false) (state clock round) body (proposal true false clock round) =
      some (generated clock round) := by
  simp only [generated,compile,dif_pos (source_checks clock round),Option.get_some]

theorem the_sufficient_failure_keeps_the_actual_original_need :
    ((law true false).next (state 0 0) body).stock true () = 0 ∧
    Exit.Necessity.AllNeedsPaid (law true false) (state 0 0) [false,true] body := by
  constructor
  · decide +kernel
  · decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions
