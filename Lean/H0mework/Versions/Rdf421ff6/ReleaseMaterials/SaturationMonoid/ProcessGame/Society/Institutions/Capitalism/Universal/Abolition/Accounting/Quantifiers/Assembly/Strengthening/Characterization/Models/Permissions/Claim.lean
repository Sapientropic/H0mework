import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Classification

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Claim

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
noncomputable section

def issue : Request Bool Unit Bool Unit Unit := ⟨true,[false],false,[],.issue () true false 1⟩
def body : RawEvent Bool Unit Bool Unit Unit :=
  [⟨false,[],false,[],.transfer false true [((),1)]⟩,issue,
    ⟨true,[],true,[],.use true [((),1)] .necessity⟩]

def item (clock : ℚ) (round : Nat) (index : Fin 3) :=
  itemAt (law true false) (state clock round) body
    ⟨index.val,by simpa only [body,List.length_cons,List.length_nil] using index.isLt⟩

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
  reciprocity := .claim (item clock round 1)
  disposal := {
    position := item clock round 0
    request := ⟨false,[],false,[],.use false [((),1)] .external⟩
    good := () }

theorem source_checks (clock : ℚ) (round : Nat) :
    (proposal clock round).Checks (law true false) (state clock round) body := by
  simp [proposal,Proposal.Checks,AccessProposal.Checks,AccessProposal.RequiredUsePaid,
    AccessProposal.Accessed,ReciprocityProposal.Checks,ReciprocityProposal.ClaimMatches,
    DisposalProposal.Checks,DisposalProposal.holder,DisposalProposal.initialHolder,
    DisposalProposal.DisposalKind,DisposalProposal.allocationChecks,DisposalProposal.AllocationChain,
    AccessProposal.controller,Follows,PrivatePhase,item,itemAt,law,body,issue,
    Kernel.Consumers.StoredAccess.law,Kernel.Consumers.StoredAccess.current,state,
    RawLaw.rawItems,RawLaw.execute,RawLaw.step,RawLaw.Valid,RawLaw.SignerMatches,
    RawLaw.operationAllowed,RawLaw.ClaimGuard,RawLaw.debit,RawLaw.credit,RawLaw.requiredPorts,
    RawLaw.paidStep,RawLaw.next,RawLaw.nextClaims,RawLaw.actualCredit,
    flowAt,locate,amount,NonnegativeBundle,RawPolicy.eval]

def generated (clock : ℚ) (round : Nat) : CapitalRelationKernel (law true false) (state clock round) body :=
  (compile (law true false) (state clock round) body (proposal clock round)).get
    (by simp only [compile,dif_pos (source_checks clock round)]; rfl)

theorem actual_original_issue_restores_the_claim_supported_relation (clock : ℚ) (round : Nat) :
    compile (law true false) (state clock round) body (proposal clock round) = some (generated clock round) ∧
    (generated clock round).financialOrigin (law true false) (state clock round) body = some (item clock round 1) := by
  constructor
  · simp only [generated,compile,dif_pos (source_checks clock round),Option.get_some]
  · have same : (generated clock round).proposal = proposal clock round := by
      simp only [generated,compile,dif_pos (source_checks clock round),Option.get_some]
    unfold CapitalRelationKernel.financialOrigin
    rw [same]
    rfl

theorem the_original_claim_is_not_removed_to_pay_the_original_need :
    ((law true false).next (state 0 0) body).claims () true false = 1 ∧
      Exit.Necessity.AllNeedsPaid (law true false) (state 0 0) [false,true] body := by
  constructor <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Claim
