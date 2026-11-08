import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplyControls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyLift
open Institutions.Capitalism.Universal.Source.Program
open Repayment.Recovery (Good)
abbrev OldParty := Delegation.Funded.Party
abbrev OldPort := Delegation.Funded.Port
abbrev OldState := Mandate.State OldParty Bool
abbrev NewState := Mandate.State WholeCursorLaw.Party Bool
abbrev OldCurrent := RecycledQuorumMaterial.Current
abbrev OldAction := RecycledQuorumMaterial.Action
abbrev oldLaw := FuelMandateLaw.law true
abbrev newLaw := WholeCursorLaw.law

def command : Mandate.Command OldParty → Mandate.Command WholeCursorLaw.Party
  | .propose actor => .propose (.inl actor)
  | .accept => .accept | .renew => .renew | .exit => .exit | .revoke => .revoke | .review => .review

def state (old : OldState) : NewState :=
  ⟨old.technology,old.version,old.holder.map Sum.inl,old.offered.map Sum.inl,old.last.map command⟩

def current (old : OldCurrent) (outside : Good → ℚ) : WholeCursorLaw.Current where
  stock := fun actor good => match actor with | .inl actor => old.stock actor good | .inr _ => outside good
  claims := fun instrument debtor creditor => match debtor,creditor with
    | .inl debtor,.inl creditor => old.claims instrument debtor creditor | _,_ => 0
  technology := state old.technology
  clock := old.clock
  round := old.round

def operation : Operation OldParty Good OldState Unit → Operation WholeCursorLaw.Party Good NewState Unit
  | .produce actor => .produce (.inl actor)
  | .transfer sender receiver goods => .transfer (.inl sender) (.inl receiver) goods
  | .use actor goods purpose => .use (.inl actor) goods purpose
  | .issue code debtor creditor quantity => .issue code (.inl debtor) (.inl creditor) quantity
  | .assign code debtor sender receiver quantity => .assign code (.inl debtor) (.inl sender) (.inl receiver) quantity
  | .settle code debtor creditor quantity => .settle code (.inl debtor) (.inl creditor) quantity
  | .revise actor target => .revise (.inl actor) (state target)
  | .present => .present

def request (old : OldAction) : WholeCursorLaw.Action :=
  ⟨.inl old.signer,old.consents.map Sum.inl,.inl old.purpose,old.gates.map Sum.inl,operation old.operation⟩

def flow (old : Flow OldParty Good) : Flow WholeCursorLaw.Party Good :=
  old.map fun item => ((.inl item.1.1,item.1.2),item.2)

theorem flowAt_inl (old : Flow OldParty Good) (actor : OldParty) (good : Good) :
    flowAt (flow old) (.inl actor) good = flowAt old actor good := by
  induction old with
  | nil => rfl
  | cons item tail ih =>
      rcases item with ⟨⟨owner,kind⟩,quantity⟩
      simpa [flow,flowAt,amount] using congrArg (fun q => (if (owner,kind) = (actor,good) then quantity else 0)+q) ih

theorem flowAt_outside (old : Flow OldParty Good) (good : Good) :
    flowAt (flow old) (.inr ()) good = 0 := by
  induction old with
  | nil => rfl
  | cons item tail ih => simpa [flow,flowAt,amount] using ih

theorem flow_locate (actor : OldParty) (goods : Bundle Good) :
    flow (locate actor goods) = locate (.inl actor) goods := by simp [flow,locate,List.map_map]

theorem mapM_some {α : Type} (xs : List α) : xs.mapM (fun x => some x) = some xs := by
  induction xs <;> simp_all

theorem decoded (old : OldAction) :
    WholeCursorLaw.request? (Mandate.eraseRequest (request old)) = some (Mandate.eraseRequest old) := by
  rcases old with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> simp [request,operation,Mandate.eraseRequest,Mandate.eraseOperation,
    WholeCursorLaw.request?,WholeCursorLaw.operation?,WholeCursorLaw.party?,WholeCursorLaw.port?,List.mapM_map,Function.comp_def,state,mapM_some]

theorem debit (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.debit (current old outside) (request action) = flow (oldLaw.debit old action) := by
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> simp [RawLaw.debit,request,operation,current,state,newLaw,oldLaw,
    WholeCursorLaw.law,WholeCursorLaw.base,Mandate.law,flow,locate,List.map_map,Function.comp_def,WholeCursorLaw.scope,Repayment.Recovery.scope]

theorem credit (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.credit (current old outside) (request action) = flow (oldLaw.credit old action) := by
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> simp [RawLaw.credit,request,operation,current,state,newLaw,oldLaw,
    WholeCursorLaw.law,WholeCursorLaw.base,Mandate.law,flow,locate,List.map_map,Function.comp_def,WholeCursorLaw.scope,Repayment.Recovery.scope]

theorem required (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.requiredPorts (current old outside) (request action) = (oldLaw.requiredPorts old action).map Sum.inl := by
  rw [RawLaw.requiredPorts,debit,RawLaw.requiredPorts]
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> simp [request,operation,flow,current,state,newLaw,oldLaw,
    WholeCursorLaw.law,WholeCursorLaw.base,Mandate.law,List.map_map,Function.comp_def,
    WholeCursorLaw.scope,Repayment.Recovery.scope]

theorem allowed (old : OldState) (port : OldPort) (actor : OldParty) :
    newLaw.allowed (state old) (.inl port) (.inl actor) = oldLaw.allowed old port actor := by
  cases port <;> simp [newLaw,oldLaw,WholeCursorLaw.law,WholeCursorLaw.base,Mandate.law,state,
    WholeCursorLaw.scope,Repayment.Recovery.scope,WholeCursorLaw.task,Repayment.Recovery.task,
    Delegation.members,List.mem_map]

theorem controller (old : OldState) (port : OldPort) :
    newLaw.controller (state old) (.inl port) = .inl (oldLaw.controller old port) := by
  cases port <;> cases h : old.holder <;> simp [newLaw,oldLaw,WholeCursorLaw.law,WholeCursorLaw.base,
    Mandate.law,state,WholeCursorLaw.scope,Repayment.Recovery.scope,h]

theorem some_actor (value : Option OldParty) (actor : OldParty) :
    value.map (Sum.inl : OldParty → WholeCursorLaw.Party) = some (.inl actor) ↔ value = some actor := by
  cases value <;> simp

theorem command_injective : Function.Injective command := by
  intro a b same
  cases a <;> cases b <;> simp_all [command]

theorem state_injective : Function.Injective state := by
  intro a b same
  cases a; cases b
  simp only [state,Mandate.State.mk.injEq] at same ⊢
  exact ⟨same.1,same.2.1,Option.map_injective Sum.inl_injective same.2.2.1,
    Option.map_injective Sum.inl_injective same.2.2.2.1,
    Option.map_injective command_injective same.2.2.2.2⟩

theorem advance (old : OldCurrent) (outside : Good → ℚ) (cmd : Mandate.Command OldParty) :
    Mandate.advance WholeCursorLaw.scope (current old outside) (command cmd) =
      state (Mandate.advance Repayment.Recovery.scope old cmd) := by
  cases cmd <;> simp [Mandate.advance,state,command,current,WholeCursorLaw.scope,Repayment.Recovery.scope,WholeCursorLaw.task,Repayment.Recovery.task]
  split <;> rfl

theorem canRun (old : OldCurrent) (outside : Good → ℚ) (actor : OldParty) (cmd : Mandate.Command OldParty) :
    Mandate.CanRun WholeCursorLaw.scope (current old outside) (.inl actor) (command cmd) ↔
      Mandate.CanRun Repayment.Recovery.scope old actor cmd := by
  cases cmd <;> simp [Mandate.CanRun,current,state,command,WholeCursorLaw.scope,Repayment.Recovery.scope,
    Delegation.members,WholeCursorLaw.task,Repayment.Recovery.task,WholeCursorLaw.producer,some_actor]

theorem taskUse (action : OldAction) :
    Mandate.TaskUse WholeCursorLaw.scope (request action) ↔ Mandate.TaskUse Repayment.Recovery.scope action := by
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> simp [Mandate.TaskUse,request,operation,WholeCursorLaw.scope,Repayment.Recovery.scope,
    WholeCursorLaw.task,Repayment.Recovery.task,WholeCursorLaw.producer]

theorem basePolicy (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    WholeCursorLaw.base.operationAllowed (Mandate.eraseCurrent (current old outside))
        (Mandate.eraseRequest (request action)) =
      (FuelMandateLaw.base true).operationAllowed (Mandate.eraseCurrent old) (Mandate.eraseRequest action) := by
  change (match WholeCursorLaw.request? (Mandate.eraseRequest (request action)) with
    | some original => (FuelMandateLaw.base true).operationAllowed
        (WholeCursorLaw.restrict (Mandate.eraseCurrent (current old outside))) original
    | none => _) = _
  rw [decoded]
  rfl

theorem newBasePorts (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    WholeCursorLaw.base.requiredPorts (Mandate.eraseCurrent (current old outside)) (Mandate.eraseRequest (request action)) =
      newLaw.requiredPorts (current old outside) (request action) := by
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> rfl

theorem oldBasePorts (old : OldCurrent) (action : OldAction) :
    (FuelMandateLaw.base true).requiredPorts (Mandate.eraseCurrent old) (Mandate.eraseRequest action) =
      oldLaw.requiredPorts old action := by
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> rfl

theorem restrictions (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    (WholeCursorLaw.scope.service ∈ WholeCursorLaw.base.requiredPorts
        (Mandate.eraseCurrent (current old outside)) (Mandate.eraseRequest (request action)) ∨
      Mandate.TaskUse WholeCursorLaw.scope (request action) →
        (current old outside).technology.holder = some (request action).signer ∧
          WholeCursorLaw.scope.task.earliest ≤ (current old outside).clock ∧
          (current old outside).clock ≤ WholeCursorLaw.scope.task.deadline) ↔
    (Repayment.Recovery.scope.service ∈ (FuelMandateLaw.base true).requiredPorts
        (Mandate.eraseCurrent old) (Mandate.eraseRequest action) ∨
      Mandate.TaskUse Repayment.Recovery.scope action → old.technology.holder = some action.signer ∧
        Repayment.Recovery.scope.task.earliest ≤ old.clock ∧ old.clock ≤ Repayment.Recovery.scope.task.deadline) := by
  rw [newBasePorts,required,oldBasePorts,taskUse]
  simp [WholeCursorLaw.scope,Repayment.Recovery.scope,WholeCursorLaw.task,Repayment.Recovery.task,
    current,state,request,some_actor]

theorem policy (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.operationAllowed (current old outside) (request action) = oldLaw.operationAllowed old action := by
  have bp := basePolicy old outside action
  have gate := restrictions old outside action
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op
  case revise actor target =>
    simp only [newLaw,oldLaw,WholeCursorLaw.law,FuelMandateLaw.law,RawLaw.operationAllowed,
      Mandate.law,RawPolicy.eval,request,operation]
    cases last : target.last with
    | none => simp [state,last]
    | some cmd =>
      have marked : (state target).last = some (command cmd) := by simp [state,last]
      rw [marked]
      simp only [advance]
      simp only [state_injective.eq_iff,canRun,Sum.inl.injEq,List.map_eq_nil_iff]
      simp [WholeCursorLaw.scope,Repayment.Recovery.scope,last]
  all_goals
    apply Bool.eq_iff_iff.mpr
    have both := and_congr (iff_of_eq (congrArg (fun v : Bool => v = true) bp)) gate
    simpa only [newLaw,oldLaw,WholeCursorLaw.law,FuelMandateLaw.law,RawLaw.operationAllowed,
      Mandate.law,RawPolicy.eval,request,operation,Bool.and_eq_true,decide_eq_true_eq] using both

theorem nonnegative (items : Flow OldParty Good) :
    NonnegativeBundle _ (flow items) ↔ NonnegativeBundle _ items := by
  simp only [NonnegativeBundle,flow,List.forall_mem_map]

theorem affordable (old : OldCurrent) (outside : Good → ℚ) (items : Flow OldParty Good) :
    (∀ item ∈ flow items, flowAt (flow items) item.1.1 item.1.2 ≤ (current old outside).stock item.1.1 item.1.2) ↔
      ∀ item ∈ items, flowAt items item.1.1 item.1.2 ≤ old.stock item.1.1 item.1.2 := by
  change (∀ item ∈ items.map (fun item => ((Sum.inl item.1.1,item.1.2),item.2)), _) ↔ _
  rw [List.forall_mem_map]
  simp only [flowAt_inl,current]

theorem signer (action : OldAction) : RawLaw.SignerMatches (request action) ↔ RawLaw.SignerMatches action := by
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> simp [RawLaw.SignerMatches,request,operation]

theorem guard (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.ClaimGuard (current old outside) (request action) ↔ oldLaw.ClaimGuard old action := by
  rcases action with ⟨signer,consents,purpose,gates,op⟩
  cases op <;> try rfl
  case use bearer goods purpose => cases purpose <;> rfl

-- Admission and refusal are derived from this existing law; neither is supplied by the caller.
theorem valid (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.Valid (current old outside) (request action) ↔ oldLaw.Valid old action := by
  simp only [RawLaw.Valid,required,debit,credit,policy,nonnegative,affordable,signer,guard]
  have permissions : (∀ port ∈ (oldLaw.requiredPorts old action).map (Sum.inl : OldPort → WholeCursorLaw.Port),
      newLaw.allowed (current old outside).technology port (request action).signer = true ∨
        newLaw.controller (current old outside).technology port ∈ (request action).consents) ↔
      ∀ port ∈ oldLaw.requiredPorts old action, oldLaw.allowed old.technology port action.signer = true ∨
        oldLaw.controller old.technology port ∈ action.consents := by
    rw [List.forall_mem_map]
    simp only [current,request,allowed,controller,List.mem_map,Sum.inl.injEq,exists_eq_right]
  rw [permissions]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyLift
