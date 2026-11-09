import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Consumers.Joint.Primitive

set_option autoImplicit false
set_option maxRecDepth 8192

open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence
open private original_body_is_single from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Consumers.Source

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (primitiveScript endAt inventory)
open Reparation.Consumers (warCut)
open Conflict.Consumers.Evolving (R W life destroy front)
open Allocation
open Allocation.Consumers (beforeFirst initialPaid)

noncomputable section

abbrev Item := ExecutionItem Bool Bool Bool Unit Unit
abbrev Law := Physical.Public.interpreter warCut.native.input

private theorem front_debits_their_own_signers (item : Item)
    (actual : item ∈ inventory warCut (primitiveScript beforeFirst))
    (entry : (Bool × Bool) × ℚ) (charged : entry ∈ Law.actualDebit item.before item.request) :
    entry.1.1 = item.request.signer := by
  rw [Quantities.Execution.primitive_inventory initialPaid.trace 0] at actual
  obtain ⟨original, listed, rfl⟩ := List.mem_map.mp actual
  have requests : original.request ∈ beforeFirst := by
    rw [← Law.inventory_requests_exact warCut.raw 0 beforeFirst]
    exact List.mem_map_of_mem listed
  change original.request ∈ [life false, life true, destroy] at requests
  simp only [List.mem_cons, List.not_mem_nil, or_false] at requests
  change entry ∈ Law.actualDebit original.before original.request at charged
  change entry.1.1 = original.request.signer
  unfold RawLaw.actualDebit at charged
  split at charged
  · rcases requests with first | second | third
    · simp [first, life, RawLaw.debit, locate] at charged ⊢
      rw [charged]
    · simp [second, life, RawLaw.debit, locate] at charged ⊢
      rw [charged]
    · simp [third, destroy, RawLaw.debit, locate] at charged ⊢
      rw [charged]
  · exact (List.not_mem_nil charged).elim

private theorem no_foreign_loss_when_every_debit_is_own
    (history : Script Bool Bool Bool Unit Unit)
    (safe : ∀ item ∈ inventory warCut history, ∀ entry ∈ Law.actualDebit item.before item.request,
      entry.1.1 = item.request.signer) :
    originalLosses warCut id history = [] := by
  induction history using List.reverseRecOn with
  | nil => rw [originalLosses, List.reverseRecOn_nil]
  | append_singleton past input prior =>
    rw [Quantities.Execution.inventory_append] at safe
    rw [losses_snoc, prior (fun item present => safe item (List.mem_append_left _ present)), List.nil_append]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro origin present
    obtain ⟨damage, _, rfl⟩ := List.mem_map.mp present
    have named := original_key damage
    unfold keysAt at named
    obtain ⟨entry, debited, addressed⟩ := List.mem_map.mp named
    have law : Boundary.Actual.materialLaw (endAt warCut past) = Law :=
      congrArg Physical.Public.interpreter (Quantities.Execution.endAt_input warCut past)
    rw [law] at debited
    have own := safe damage.item (List.mem_append_right _ damage.source_item) entry debited
    have controlled := damage.actual_foreign_debit.1
    exact controlled.1 ((congrArg Prod.fst addressed).symm.trans (own.trans controlled.2.1))

theorem the_front_installs_no_aggression_row :
    (run warCut id (primitiveScript beforeFirst)).stack.balances = [] :=
  List.map_eq_nil_iff.mp
    ((the_live_ledger_contains_exactly_the_original_losses warCut id _).trans
      (no_foreign_loss_when_every_debit_is_own _ front_debits_their_own_signers))

private theorem damage_at_a_single_transfer_has_its_only_address (earlier : W) (request : R)
    (paid : Conflict.Root.Paid warCut (earlier ++ [request]))
    (payer payee good : Bool) (amount : ℚ)
    (transfer : request.operation = .transfer payer payee [(good, amount)])
    (damage : Boundary.Actual.DamageAt (endAt warCut (primitiveScript earlier)) (bodyInput request) id) :
    damage.key = (payer, request.signer, good) := by
  let cut := endAt warCut (primitiveScript earlier)
  let original : Item := ⟨0, cut.raw, request⟩
  have present := damage.source_item
  rw [original_body_is_single earlier request paid] at present
  have body : damage.item = original := List.mem_singleton.mp present
  have valid := damage.actual_foreign_debit.2.1
  rw [body] at valid
  have named := original_key damage
  unfold keysAt at named
  rw [body, RawLaw.actualDebit, if_pos valid] at named
  change damage.key ∈
    (((Boundary.Actual.materialLaw cut).debit cut.raw request).map fun part => (part.1.1, request.signer, part.1.2)) at named
  simpa only [RawLaw.debit, transfer, locate, List.map_cons, List.map_nil, List.mem_singleton] using named

theorem a_single_transfer_files_exactly_its_one_damage (earlier : W) (request : R)
    (paid : Conflict.Root.Paid warCut (earlier ++ [request]))
    (payer payee good : Bool) (amount : ℚ)
    (transfer : request.operation = .transfer payer payee [(good, amount)])
    (expected : Boundary.Actual.DamageAt (endAt warCut (primitiveScript earlier)) (bodyInput request) id)
    (address : expected.key = (payer, request.signer, good)) :
    openings warCut id (primitiveScript earlier) (bodyInput request) =
      [⟨primitiveScript earlier, bodyInput request, expected⟩] := by
  let losses := Boundary.Actual.damages (endAt warCut (primitiveScript earlier)) (bodyInput request) id
  have all : ∀ observed ∈ losses, observed = expected := by
    intro observed _
    have width : (Boundary.Actual.items (endAt warCut (primitiveScript earlier)) (bodyInput request)).length = 1 :=
      congrArg List.length (original_body_is_single earlier request paid)
    have observedPosition := observed.position.isLt.trans_eq width
    have expectedPosition := expected.position.isLt.trans_eq width
    apply Subtype.ext
    exact Prod.ext (Fin.ext (by omega))
      ((damage_at_a_single_transfer_has_its_only_address earlier request paid payer payee good amount transfer observed).trans address.symm)
  have inside : expected ∈ losses := Boundary.Actual.every_actual_debit_is_assessed expected
  have distinct : losses.Nodup := Boundary.Actual.each_damage_address_occurs_once _ _ _
  have exactly : losses = [expected] := by
    cases seen : losses with
    | nil => exact (List.not_mem_nil (seen ▸ inside)).elim
    | cons first remaining =>
      have same := all first (seen.symm ▸ List.mem_cons_self)
      have last : remaining = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro candidate later
        have duplicate := all candidate (seen.symm ▸ List.mem_cons_of_mem _ later)
        exact (List.nodup_cons.mp (seen ▸ distinct)).1 ((duplicate.trans same.symm) ▸ later)
      rw [same, last]
  change losses.map (Occurrence.mk (primitiveScript earlier) (bodyInput request)) = _
  rw [exactly]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint
