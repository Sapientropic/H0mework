import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Carrier

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

/-- A genuine successor input spends one or two units of an economic stock. -/
def privateUse (larger : Bool) : AuditRequest :=
  ⟨3,[],.common,[],.use 3 [(.feed,if larger then 2 else 1)] .external⟩

def deliveryFee : AuditRequest := ⟨0,[],.common,[],.use 0 [(.labor,1)] .external⟩
def readWord (actor : Party) : List AuditRequest := [accessRequest actor,deliveryFee]

def emit (larger : Bool) (current : AuditCurrent) : List AuditRequest :=
  match current.round - initial.round with
  | 1 => preparation
  | 2 => authorization current 1
  | 3 => [privateUse larger]
  | 4 => readWord 1
  | 5 => handoff current
  | 6 => [accessRequest 1]
  | 7 | 8 => readWord 2
  | _ => []

def input (larger : Bool) : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Unit :=
  { law := auditLaw, initial := initial, instructions := [], emission? := some (emit larger) }

def current (larger : Bool) : Nat → AuditCurrent
  | 0 => initial
  | n + 1 => auditLaw.next (current larger n) (if n = 0 then [] else emit larger (current larger n))

theorem current_is_own_root_current (larger : Bool) (ordinal : Nat) :
    ProgrammeSource.rawCurrent (input larger) (ProgrammeHistory.visitAt (input larger) ordinal).current =
      current larger ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      change ProgrammeSource.rawCurrent (input larger)
        (ProgrammeSource.next (input larger) (ProgrammeHistory.visitAt (input larger) ordinal).current) = _
      rw [ProgrammeSource.actual_raw_next, ih]
      cases ordinal with
      | zero => rfl
      | succ ordinal =>
          have word : ProgrammeSource.rawEvent (input larger)
              (ProgrammeHistory.visitAt (input larger) (ordinal + 1)).current =
              emit larger (current larger (ordinal + 1)) := by
            change ProgrammeSource.rawEvent (input larger) (ProgrammeSource.next (input larger)
              (ProgrammeHistory.visitAt (input larger) ordinal).current) = _
            rw [← ih]
            change ProgrammeSource.rawEvent (input larger) (ProgrammeSource.next (input larger)
              (ProgrammeHistory.visitAt (input larger) ordinal).current) =
                emit larger (ProgrammeSource.rawCurrent (input larger) (ProgrammeSource.next (input larger)
                  (ProgrammeHistory.visitAt (input larger) ordinal).current))
            generalize (ProgrammeHistory.visitAt (input larger) ordinal).current = prior
            cases prior <;> rfl
          exact congrArg (auditLaw.next _) word

theorem emitted_costs_are_actually_affordable (larger : Bool) (ordinal : Fin 9)
    (notRevoked : ordinal.val ≠ 6) :
    ∀ item ∈ auditLaw.rawItems (current larger ordinal.val) (emit larger (current larger ordinal.val)),
      auditLaw.Valid item.before item.request := by
  cases larger <;> rcases ordinal with ⟨ordinal,bound⟩ <;>
    interval_cases ordinal <;> first | contradiction | decide +kernel +revert

theorem old_auditor_is_really_revoked (larger : Bool) :
    ¬ auditLaw.Valid (current larger 6) (accessRequest 1) ∧
    auditLaw.step (current larger 6) (accessRequest 1) = current larger 6 := by
  have denied : ¬ auditLaw.Valid (current larger 6) (accessRequest 1) := by cases larger <;> decide +kernel
  exact ⟨denied,auditLaw.rejected_preserves_current _ _ denied⟩

theorem actual_grants_are_nonempty (larger : Bool) :
    (Mandate.grantsAt Cell.law scope (current larger 2) (emit larger (current larger 2))).isEmpty = false ∧
    (Mandate.grantsAt Cell.law scope (current larger 5) (emit larger (current larger 5))).isEmpty = false := by
  cases larger <;> decide +kernel

theorem handoff_needs_no_previous_auditor_signature (larger : Bool) :
    (emit larger (current larger 5)).map Request.signer = [0,0,2] ∧
    (current larger 6).technology.holder = some 2 ∧
    (current larger 6).technology.version = 5 := by
  cases larger <;> decide +kernel

theorem private_successors_have_different_future_capacity :
    (current false 4).stock 3 .feed = 39 ∧ (current true 4).stock 3 .feed = 38 ∧
    auditLaw.Valid (current false 4) ⟨3,[],.common,[],.transfer 3 0 [(.feed,39)]⟩ ∧
    ¬ auditLaw.Valid (current true 4) ⟨3,[],.common,[],.transfer 3 0 [(.feed,39)]⟩ := by
  decide +kernel

theorem actual_audit_costs (larger : Bool) :
    (current larger 9).stock 0 .labor = 2 ∧
    (current larger 9).stock 1 .labor = 1 ∧
    (current larger 9).stock 2 .labor = 0 ∧
    (current larger 9).stock 3 .labor = 6 := by
  cases larger <;> decide +kernel

private theorem silent_pair (first second : AuditRequest) (a : ClaimSilent first) (b : ClaimSilent second) :
    ∀ action ∈ [first,second], ClaimSilent action := by
  intro action inside
  rcases List.mem_cons.mp inside with rfl | rest
  · exact a
  · exact List.mem_singleton.mp rest ▸ b

private theorem silent_single (only : AuditRequest) (silent : ClaimSilent only) :
    ∀ action ∈ [only], ClaimSilent action := by
  intro action inside
  exact List.mem_singleton.mp inside ▸ silent

theorem emitted_word_preserves_claims (larger : Bool) (before : AuditCurrent) :
    (auditLaw.next before (emit larger before)).claims = before.claims := by
  apply silent_execute
  unfold emit
  split
  · exact silent_pair _ _ (by trivial) (by trivial)
  · exact authorization_silent _ _
  · exact silent_single _ (by trivial)
  · exact silent_pair _ _ (by trivial) (by trivial)
  · intro action inside
    rcases List.mem_cons.mp inside with rfl | rest
    · trivial
    · exact authorization_silent _ _ action rest
  · exact silent_single _ (by trivial)
  · exact silent_pair _ _ (by trivial) (by trivial)
  · exact silent_pair _ _ (by trivial) (by trivial)
  · simp

theorem every_audit_successor_keeps_original_claims (larger : Bool) (ordinal : Nat) :
    (current larger ordinal).claims = initial.claims := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      cases ordinal with
      | zero => exact ih
      | succ ordinal => exact (emitted_word_preserves_claims _ _).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
