import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Governance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- Canonical public-key bytes name a new actor; they do not select an old holder. -/
def principal (key : String) : Party := 4 + key.toUTF8.foldl (fun n byte => n * 256 + byte.toNat) 0

theorem principal_is_external (key : String) : 4 ≤ principal key := Nat.le_add_right 4 _

def birth (key : String) : Action := ⟨principal key,[],native .common,[],.present⟩

theorem birth_is_admissible (before : AuditCurrent) (key : String) : auditLaw.Valid before (birth key) := by
  simp [birth,auditLaw,Mandate.law,baseLaw,RawLaw.Valid,RawLaw.SignerMatches,
    RawLaw.operationAllowed,RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,
    RawLaw.ClaimGuard,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,
    Mandate.TaskUse,erasePort,Cell.law,native,scope,NonnegativeBundle]

theorem birth_does_not_grant_authority (before : AuditCurrent) (key : String) :
    auditLaw.step before (birth key) = before :=
  auditLaw.presentation_preserves_material_and_claims _ _ rfl

abbrev Births := List (Nat × String)
abbrev Replies := List (Nat × Response.Objection)

def bornWord (births : Births) (cut : Nat) : List Action :=
  (births.filter (fun item => item.1 == cut)).map fun item => birth item.2

def emit (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies)
    (before : AuditCurrent) : List Action :=
  let cut := before.round - initial.round
  (match replies.find? (fun item => item.1 == cut) with
  | some (_,objection) => match Response.expectedAt queries larger objection.observedCut with
    | none => []
    | some expected => Response.word before expected objection
  | none => Scoped.emit queries larger before) ++ bornWord births cut

def input (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) :
    ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit :=
  { Scoped.input queries larger with emission? := some (emit queries larger births replies) }

def current (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) : Nat → AuditCurrent :=
  Nat.rec initial (fun n before => auditLaw.next before
    (if n = 0 then [] else emit queries larger births replies before))

theorem current_succ (queries : Nat → Query) (larger : Bool) (births : Births) (replies : Replies) (n : Nat) :
    current queries larger births replies (n+1) = auditLaw.next (current queries larger births replies n)
      (if n = 0 then [] else emit queries larger births replies (current queries larger births replies n)) := rfl

attribute [irreducible] current

theorem current_is_own_root_current (queries : Nat → Query) (larger : Bool)
    (births : Births) (replies : Replies) (n : Nat) :
    ProgrammeSource.rawCurrent (input queries larger births replies)
      (ProgrammeHistory.visitAt (input queries larger births replies) n).current = current queries larger births replies n := by
  induction n with
  | zero => unfold current; rfl
  | succ n ih =>
    change ProgrammeSource.rawCurrent (input queries larger births replies)
      (ProgrammeSource.next (input queries larger births replies)
        (ProgrammeHistory.visitAt (input queries larger births replies) n).current) = _
    rw [ProgrammeSource.actual_raw_next,ih,current_succ]
    cases n with
    | zero => rfl
    | succ n =>
      congr 1
      simp only [Nat.succ_ne_zero,if_false]
      rw [← ih]
      change ProgrammeSource.rawEvent (input queries larger births replies)
        (ProgrammeSource.next (input queries larger births replies)
          (ProgrammeHistory.visitAt (input queries larger births replies) n).current) =
        emit queries larger births replies (ProgrammeSource.rawCurrent (input queries larger births replies)
          (ProgrammeSource.next (input queries larger births replies)
            (ProgrammeHistory.visitAt (input queries larger births replies) n).current))
      generalize (ProgrammeHistory.visitAt (input queries larger births replies) n).current = prior
      cases prior <;> rfl

private theorem execute_births (before : AuditCurrent) (index : Nat) (births : Births) :
    (auditLaw.execute before index (births.map (fun item => birth item.2))).final = before := by
  induction births generalizing before index with
  | nil => rfl
  | cons head tail ih =>
    change (auditLaw.execute (auditLaw.step before (birth head.2)) (index+1) _).final = before
    rw [birth_does_not_grant_authority,ih]

private theorem next_append_births (before : AuditCurrent) (word : List Action) (births : Births) :
    auditLaw.next before (word ++ births.map (fun item => birth item.2)) = auditLaw.next before word := by
  simp only [RawLaw.next,auditLaw.execute_append,execute_births]

theorem emission_preserves_all_original_claims (queries : Nat → Query) (larger : Bool)
    (births : Births) (replies : Replies) (before : AuditCurrent) :
    (auditLaw.next before (emit queries larger births replies before)).claims = before.claims := by
  dsimp only [emit,bornWord]
  rw [next_append_births]
  split
  · split
    · rfl
    · exact Response.response_preserves_all_original_claims _ _ _
  · exact every_emitted_word_preserves_original_claims _ _ _

theorem registration_preserves_every_original_current (queries : Nat → Query) (larger : Bool)
    (births : Births) (n : Nat) : current queries larger births [] n = Scoped.current queries larger n := by
  induction n with
  | zero => rw [Scoped.current_zero]; unfold current; rfl
  | succ n ih =>
    rw [current_succ,Scoped.current_succ,ih]
    split
    · rfl
    · unfold emit
      simp only [List.find?_nil]
      simp only [RawLaw.next,auditLaw.execute_append,bornWord,execute_births]

structure Role (before : AuditCurrent) (actions : List Action) (key : String) where
  private mk ::
  item : { item // item ∈ auditLaw.rawItems before actions }
  request : item.val.request = birth key
  accepted : auditLaw.Valid item.val.before item.val.request

def roles (before : AuditCurrent) (actions : List Action) (key : String) : List (Role before actions key) :=
  (auditLaw.rawItems before actions).attach.filterMap fun item =>
    match operation : item.val.request.operation with
    | .present =>
      if bound : item.val.request.signer = principal key ∧ item.val.request.consents = [] ∧
          item.val.request.purpose = native .common ∧ item.val.request.gates = [] then
        let same : item.val.request = birth key := by
          rcases item with ⟨⟨index,before,⟨signer,consents,purpose,gates,action⟩⟩,member⟩
          simp only at bound operation
          rcases bound with ⟨rfl,rfl,rfl,rfl⟩
          subst action
          rfl
        some ⟨item,same,by rw [same]; exact birth_is_admissible _ _⟩
      else none
    | _ => none

theorem role_has_original_birth_and_no_delegation {before : AuditCurrent} {actions : List Action}
    {key : String} (role : Role before actions key) :
    role.item.val.request.signer = principal key ∧
    auditLaw.step role.item.val.before role.item.val.request = role.item.val.before := by
  rw [role.request]
  exact ⟨rfl,birth_does_not_grant_authority _ _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Governance
