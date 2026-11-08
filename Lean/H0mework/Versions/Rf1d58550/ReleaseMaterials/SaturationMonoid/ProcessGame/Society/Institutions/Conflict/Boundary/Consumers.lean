import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Defence
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Source
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving
open Space

noncomputable section

private abbrev opening : C := Conflict.Consumers.Evolving.source

private def coordinates (law : RawLaw Bool Bool Bool Unit Unit)
    (origin : ProgrammeFace.Origin Bool Bool Bool Unit Unit)
    (certificate : (crossingCompiler law origin id).AnyBoundaryCertificate) :
    Nat × Bool × Bool × Bool × ℚ :=
  let row := debitAt law origin certificate.crossing
  (row.1.index, row.1.request.signer, row.2.1, row.2.2, loss law row)

private theorem exact_old_levy :
    (spaceAt opening conflict id).boundaryCertificates.map (coordinates opening.native.input.law (opening.raw, conflict)) =
      [(3, true, false, false, 6)] := by
  change (sourceCrossings opening.native.input.law (opening.raw, conflict) id).boundaryCertificates.map
    (coordinates opening.native.input.law (opening.raw, conflict)) = _
  rw [sourceInput, sourceRead]
  decide +kernel

theorem the_old_positive_war_pays_a_literal_m11_foreign_capture :
    ∃ attack : AggressionAt opening conflict id, attack.item.index = 3 ∧ attack.attacker = true ∧
      attack.victim = false ∧ attack.good = false ∧ attack.quantity = 6 ∧
      {attack.item with index := 0} ∈ Quantities.Execution.inventory opening (Quantities.Execution.primitiveScript conflict) := by
  have member : (3, true, false, false, (6 : ℚ)) ∈
      (spaceAt opening conflict id).boundaryCertificates.map (coordinates opening.native.input.law (opening.raw, conflict)) := by
    rw [exact_old_levy]
    exact List.mem_cons_self
  obtain ⟨boundary, present, same⟩ := List.mem_map.mp member
  let attack := AggressionAt.ofPaidBoundary conflictPaid boundary present
  exact ⟨attack, congrArg Prod.fst same, congrArg (fun c => c.2.1) same,
    congrArg (fun c => c.2.2.1) same, congrArg (fun c => c.2.2.2.1) same,
    congrArg (fun c => c.2.2.2.2) same, attack.in_original_paid_inventory⟩

theorem a_paid_peace_does_not_create_a_foreign_capture :
    (spaceAt opening peace id).boundaryCertificates = [] := by
  apply List.length_eq_zero_iff.mp
  change (sourceCrossings opening.native.input.law (opening.raw, peace) id).boundaryCertificates.length = 0
  rw [sourceInput, sourceRead]
  decide +kernel

theorem the_post_conflict_cut_cannot_forge_the_old_exit_payments :
    ¬ ExitFloorAt opening (Root.terminal opening conflict) [false] [life false, life true] := by
  intro exit
  let current := Root.terminal opening conflict
  have sameInput : current.native.input = compact := conflictPaid.whole.sameInput.trans sourceInput
  have sameRaw : current.raw = (compact.law.execute oldRaw 0 conflict).final := by
    dsimp only [current]
    rw [conflictPaid.original_raw_exact, sourceInput, sourceRead]
  have authorized := exit.paid.authorized ⟨0, current.raw, life false⟩ List.mem_cons_self
  change current.native.input.law.Valid current.raw (life false) at authorized
  rw [sameInput, sameRaw] at authorized
  exact (by decide +kernel : ¬ compact.law.Valid (compact.law.execute oldRaw 0 conflict).final (life false)) authorized

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Consumers
