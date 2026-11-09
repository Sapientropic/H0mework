import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Run
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Guard

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_input primitiveScript)
open Reparation (Key)
open Reparation.Actual (Input ReceiptAnswers Occurrence Script)
open Reparation.Actual.Allocation (Position)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (front : Script Party Good Port Technology Instrument)
  (purpose : Port) (key : Key Party Good)

local notation "Here" => endAt seed (Occurrence.history loss ++ front)
local notation "Word" => Script Party Good Port Technology Instrument

theorem the_installed_technology_supplies_the_literal_receipt_stock
    {revision production : Request Party Good Port Technology Instrument}
    {operator producer : Party} {technology : Technology}
    (revises : revision.operation = .revise operator technology)
    (produces : production.operation = .produce producer)
    (actual : ProductionWrite answers loss front [revision, production])
    (paid : PaidInstallment loss answers (reserveAt loss (front ++ primitiveScript [revision, production]))
      (front ++ primitiveScript [revision, production]) purpose key
      (maximumInstallment loss answers (front ++ primitiveScript [revision, production]) key)) :
    let revised := Conflict.Root.terminal (Here) [revision]
    let law := seed.native.input.law
    revised.raw.technology = technology ∧
      ∀ person good,
        paid.delivery.receipt.item.before.stock person good +
          flowAt (law.actualDebit revised.raw production) person good =
        revised.raw.stock person good + flowAt (locate producer (law.technique technology producer).outputs) person good := by
  let revised := Conflict.Root.terminal (Here) [revision]
  let law := seed.native.input.law
  have produced := ProductionWrite.revision_then_production_has_new_native_credit actual revises produces
  have trace := actual.inventory
  rw [produced.2.1, endAt_input] at trace
  change [ExecutionItem.mk 0 (prefixRaw loss front) revision, ExecutionItem.mk 0 revised.raw production] =
    [ExecutionItem.mk 0 (prefixRaw loss front) revision,
      ExecutionItem.mk 0 (law.step (prefixRaw loss front) revision) production] at trace
  have revisedRaw : revised.raw = law.step (prefixRaw loss front) revision :=
    congrArg ExecutionItem.before (List.cons.inj (List.cons.inj trace).2).1
  have item := (the_payment_consumes_the_post_production_material_position loss answers front
    [revision, production] purpose key actual paid).1
  have before : paid.delivery.receipt.item.before = law.step revised.raw production := by
    rw [item]
    change law.step (law.step (prefixRaw loss front) revision) production = _
    rw [← revisedRaw]
  have credit := produced.2.2
  rw [endAt_input] at credit
  refine ⟨produced.1, fun person good => ?_⟩
  rw [before, law.material_step_balance, credit]

theorem the_generated_receipt_cannot_be_reused_at_a_later_material_position
    (body : RawEvent Party Good Port Technology Instrument)
    (paid : PaidInstallment loss answers (reserveAt loss (front ++ primitiveScript body))
      (front ++ primitiveScript body) purpose key
      (maximumInstallment loss answers (front ++ primitiveScript body) key))
    (later : Word) (input : Input Party Good Port Technology Instrument)
    (site : Position seed later input) (replies : ReceiptAnswers seed)
    (strict : (Occurrence.history loss ++ (front ++ primitiveScript body)).length < later.length) :
    Settlement.jointOffer replies later input site key ≠ some paid.delivery.receipt :=
  Settlement.the_same_joint_receipt_cannot_be_reused_at_a_later_tick answers _ _
    paid.delivery.position key paid.delivery.receipt paid.delivery.issued later input site replies strict

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve
