import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.IssueTrace
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {fuel : ℚ} {inputs : List (List Action)}

abbrev financialItems (fuel : ℚ) (inputs : List (List Action)) (visit : Nat) :=
  Registered.traceItems (input fuel inputs) (ProgrammeHistory.visitAt (input fuel inputs) visit).current

theorem common_prefix_keeps_each_financial_instruction (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1)) :
    financialItems fuel (branchInputs cut word) (birth.val + 1) = financialItems fuel inputs (birth.val + 1) := by
  change law.rawItems (Runtime.mandateCurrentAt fuel (branchInputs cut word) birth.val)
    (Runtime.mandateWordAt fuel (branchInputs cut word) birth.val) =
    law.rawItems (Runtime.mandateCurrentAt fuel inputs birth.val) (Runtime.mandateWordAt fuel inputs birth.val)
  rw [(original_current_and_word_at_each_birth cut word birth).1,
    (original_current_and_word_at_each_birth cut word birth).2]

def financialIndex (cut : Cut fuel inputs) (word : List Action) (birth : Fin (cut.depth + 1))
    (index : Fin (financialItems fuel inputs (birth.val + 1)).length) :
    Fin (financialItems fuel (branchInputs cut word) (birth.val + 1)).length :=
  ⟨index.val, by rw [common_prefix_keeps_each_financial_instruction cut word birth]; exact index.isLt⟩

theorem financialIndex_same_instruction (cut : Cut fuel inputs) (word : List Action) (birth : Fin (cut.depth + 1))
    (index : Fin (financialItems fuel inputs (birth.val + 1)).length) :
    (financialItems fuel (branchInputs cut word) (birth.val + 1)).get (financialIndex cut word birth index) =
      (financialItems fuel inputs (birth.val + 1)).get index := by
  have same := congrArg (fun items => items[index.val]?) (common_prefix_keeps_each_financial_instruction cut word birth)
  have bound : index.val < (financialItems fuel (branchInputs cut word) (birth.val + 1)).length :=
    (financialIndex cut word birth index).isLt
  rw [List.getElem?_eq_getElem bound, List.getElem?_eq_getElem index.isLt] at same
  exact Option.some.inj same

abbrev financialOrigin (fuel : ℚ) (inputs : List (List Action)) (visit : Nat)
    (index : Fin (financialItems fuel inputs visit).length) :=
  Financial.traceOriginAt (input fuel inputs) (ProgrammeHistory.visitAt (input fuel inputs) visit) index

def financialSlotIndex (fuel : ℚ) (inputs : List (List Action)) (visit : Nat)
    (index : Fin (financialItems fuel inputs visit).length) :=
  Financial.IssueTrace.traceIndex (input fuel inputs) visit _ rfl index

theorem financialSlotIndex_origin (fuel : ℚ) (inputs : List (List Action)) (visit : Nat)
    (index : Fin (financialItems fuel inputs visit).length) :
    Financial.IssueTrace.origin (input fuel inputs) visit (financialSlotIndex fuel inputs visit index) =
      financialOrigin fuel inputs visit index :=
  Financial.IssueTrace.traceIndex_origin (input fuel inputs) visit _ rfl index

structure IssueTransport (cut : Cut fuel inputs) (word : List Action) (birth : Fin (cut.depth + 1))
    (index : Fin (financialItems fuel inputs (birth.val + 1)).length)
    (original : Financial.IssuedClaim (input fuel inputs)) where
  private mk ::
  replacement : Financial.IssuedClaim (input fuel (branchInputs cut word))
  original_origin : original.origin = financialOrigin fuel inputs (birth.val + 1) index
  replacement_origin : replacement.origin = financialOrigin fuel (branchInputs cut word) (birth.val + 1)
    (financialIndex cut word birth index)
  same_instruction : replacement.instruction = original.instruction
  same_contract : replacement.instrument = original.instrument ∧ replacement.debtor = original.debtor ∧
    replacement.holder = original.holder ∧ replacement.quantity = original.quantity
  original_slot : Financial.IssueTrace.IssuedSlot (input fuel inputs) (birth.val + 1)
    (financialSlotIndex fuel inputs (birth.val + 1) index) original
  replacement_slot : Financial.IssueTrace.IssuedSlot (input fuel (branchInputs cut word)) (birth.val + 1)
    (financialSlotIndex fuel (branchInputs cut word) (birth.val + 1) (financialIndex cut word birth index)) replacement

private theorem readout_reindex {old new : Financial.InstructionOrigin (input fuel inputs)}
    (same : new = old) (claim : Financial.IssuedClaim (input fuel inputs))
    (exactOrigin : claim.origin = old)
    (emitted : Financial.readIssue (input fuel inputs) old = .issued claim exactOrigin) :
    Financial.readIssue (input fuel inputs) new = .issued claim (exactOrigin.trans same.symm) := by
  cases same
  exact emitted

noncomputable def transportIssue (cut : Cut fuel inputs) (word : List Action) (birth : Fin (cut.depth + 1))
    (index : Fin (financialItems fuel inputs (birth.val + 1)).length)
    (original : Financial.IssuedClaim (input fuel inputs))
    (exactOrigin : original.origin = financialOrigin fuel inputs (birth.val + 1) index)
    (emitted : Financial.readIssue (input fuel inputs) (financialOrigin fuel inputs (birth.val + 1) index) =
      .issued original exactOrigin) : IssueTransport cut word birth index original := by
  have oldDecoded : (financialOrigin fuel inputs (birth.val + 1) index).instruction? (input fuel inputs) =
      some original.instruction := by rw [← exactOrigin]; exact original.instruction_exact
  have sameInstruction : (financialItems fuel inputs (birth.val + 1)).get index = original.instruction :=
    Option.some.inj ((Financial.traceOriginAt_instruction _ _ _).symm.trans oldDecoded)
  have newDecoded : (financialOrigin fuel (branchInputs cut word) (birth.val + 1)
      (financialIndex cut word birth index)).instruction? (input fuel (branchInputs cut word)) = some original.instruction := by
    rw [Financial.traceOriginAt_instruction, financialIndex_same_instruction, sameInstruction]
  have generated := Financial.BalanceConservation.issue_readout_issued (input fuel (branchInputs cut word)) _
    original.instruction newDecoded original.instrument original.debtor original.holder original.quantity
    original.issue_exact original.accepted
  cases readout : Financial.readIssue (input fuel (branchInputs cut word))
      (financialOrigin fuel (branchInputs cut word) (birth.val + 1) (financialIndex cut word birth index)) with
  | issued replacement replacementOrigin =>
      have same := Option.some.inj (replacement.instruction_exact.symm.trans (by
        rw [replacementOrigin]; exact newDecoded))
      have contract := Operation.issue.inj (replacement.issue_exact.symm.trans
        ((congrArg (fun instruction => instruction.request.operation) same).trans original.issue_exact))
      have oldAt : original.origin = Financial.IssueTrace.origin (input fuel inputs) (birth.val + 1)
          (financialSlotIndex fuel inputs (birth.val + 1) index) :=
        exactOrigin.trans (financialSlotIndex_origin fuel inputs _ index).symm
      have oldRead : Financial.readIssue (input fuel inputs) (Financial.IssueTrace.origin (input fuel inputs) (birth.val + 1)
          (financialSlotIndex fuel inputs (birth.val + 1) index)) = .issued original oldAt :=
        readout_reindex (financialSlotIndex_origin fuel inputs _ index) original exactOrigin emitted
      have newAt : replacement.origin = Financial.IssueTrace.origin (input fuel (branchInputs cut word)) (birth.val + 1)
          (financialSlotIndex fuel (branchInputs cut word) (birth.val + 1) (financialIndex cut word birth index)) :=
        replacementOrigin.trans (financialSlotIndex_origin fuel (branchInputs cut word) _ _).symm
      have newRead : Financial.readIssue (input fuel (branchInputs cut word))
          (Financial.IssueTrace.origin (input fuel (branchInputs cut word)) (birth.val + 1)
            (financialSlotIndex fuel (branchInputs cut word) (birth.val + 1) (financialIndex cut word birth index))) =
          .issued replacement newAt :=
        readout_reindex (financialSlotIndex_origin fuel (branchInputs cut word) _ _) replacement replacementOrigin readout
      exact ⟨replacement, exactOrigin, replacementOrigin, same, contract,
        Financial.IssueTrace.generate _ _ _ original oldAt oldRead,
        Financial.IssueTrace.generate _ _ _ replacement newAt newRead⟩
  | nonfinancial =>
      have impossible : False := by obtain ⟨claim, sameOrigin, emitted, _⟩ := generated; rw [readout] at emitted; cases emitted
      exact impossible.elim
  | rejected instruction decoded refused =>
      have impossible : False := by obtain ⟨claim, sameOrigin, emitted, _⟩ := generated; rw [readout] at emitted; cases emitted
      exact impossible.elim
  | missingBirth party notBorn =>
      have impossible : False := by obtain ⟨claim, sameOrigin, emitted, _⟩ := generated; rw [readout] at emitted; cases emitted
      exact impossible.elim

noncomputable def attemptIssueTransport (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1)) (index : Fin (financialItems fuel inputs (birth.val + 1)).length) :
    Option (Sigma fun original : Financial.IssuedClaim (input fuel inputs) => IssueTransport cut word birth index original) :=
  match emitted : Financial.readIssue (input fuel inputs) (financialOrigin fuel inputs (birth.val + 1) index) with
  | .issued original exactOrigin => some ⟨original, transportIssue cut word birth index original exactOrigin emitted⟩
  | .nonfinancial | .rejected .. | .missingBirth .. => none

theorem every_source_issue_generates_its_actual_transport (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1)) (index : Fin (financialItems fuel inputs (birth.val + 1)).length)
    (original : Financial.IssuedClaim (input fuel inputs))
    (exactOrigin : original.origin = financialOrigin fuel inputs (birth.val + 1) index)
    (emitted : Financial.readIssue (input fuel inputs) (financialOrigin fuel inputs (birth.val + 1) index) =
      .issued original exactOrigin) :
    attemptIssueTransport cut word birth index =
      some ⟨original, transportIssue cut word birth index original exactOrigin emitted⟩ := by
  unfold attemptIssueTransport
  split
  next actual sameOrigin reading =>
    have same := reading.symm.trans emitted
    have claimEq : actual = original := by cases same; rfl
    cases claimEq
    rfl
  next reading => rw [emitted] at reading; cases reading
  next instruction decoded refused reading => rw [emitted] at reading; cases reading
  next party notBorn reading => rw [emitted] at reading; cases reading

namespace IssueTransport

variable {cut : Cut fuel inputs} {word : List Action} {birth : Fin (cut.depth + 1)}
  {index : Fin (financialItems fuel inputs (birth.val + 1)).length}
  {original : Financial.IssuedClaim (input fuel inputs)}
  (transport : IssueTransport cut word birth index original)

include transport

theorem original_before_is_the_actual_item :
    Financial.BalanceConservation.ledgerClaims (input fuel inputs)
      (Financial.IssueTrace.before (input fuel inputs) (birth.val + 1)
        (financialSlotIndex fuel inputs (birth.val + 1) index)).current = original.instruction.before.claims :=
  Financial.IssueTrace.before_claims _ (zero_financial_genesis _ _) _ _ _ (by
    rw [financialSlotIndex_origin, ← transport.original_origin]; exact original.instruction_exact)

theorem replacement_before_is_the_same_actual_item :
    Financial.BalanceConservation.ledgerClaims (input fuel (branchInputs cut word))
      (Financial.IssueTrace.before (input fuel (branchInputs cut word)) (birth.val + 1)
        (financialSlotIndex fuel (branchInputs cut word) (birth.val + 1) (financialIndex cut word birth index))).current =
      original.instruction.before.claims :=
  Financial.IssueTrace.before_claims _ (zero_financial_genesis _ _) _ _ _ (by
    rw [financialSlotIndex_origin, ← transport.replacement_origin, ← transport.same_instruction]
    exact transport.replacement.instruction_exact)

theorem original_is_in_the_common_cut :
    ((Financial.accountAt (input fuel inputs) (cut.depth + 2)).current.slots.map (Financial.slotClaim _))[(Financial.IssueTrace.before (input fuel inputs) (birth.val + 1)
        (financialSlotIndex fuel inputs (birth.val + 1) index)).current.slots.length]? = some original := by
  have actual := transport.original_slot.retained (cut.depth - birth.val)
  have ordinal : birth.val + 1 + 1 + (cut.depth - birth.val) = cut.depth + 2 := by omega
  simpa only [ordinal] using actual

theorem replacement_survives_every_actual_next (later : Nat) :
    ((Financial.accountAt (input fuel (branchInputs cut word)) (cut.depth + 3 + later)).current.slots.map (Financial.slotClaim _))[(Financial.IssueTrace.before (input fuel (branchInputs cut word)) (birth.val + 1)
        (financialSlotIndex fuel (branchInputs cut word) (birth.val + 1) (financialIndex cut word birth index))).current.slots.length]? =
      some transport.replacement := by
  have actual := transport.replacement_slot.retained (cut.depth - birth.val + 1 + later)
  have ordinal : birth.val + 1 + 1 + (cut.depth - birth.val + 1 + later) = cut.depth + 3 + later := by omega
  simpa only [ordinal] using actual

end IssueTransport

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure
