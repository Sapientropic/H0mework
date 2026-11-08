import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Stock
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Holding
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Witness

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Trace)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Request" => Source.Program.Request Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument

private def requestedUse (request : Request) (bearer : Party) (purpose : Use) (good : Good) : ℚ :=
  match request.operation with
  | .use _ _ kind => if purpose = kind then flowAt (Production.material request) bearer good else 0
  | _ => 0

/-- Project the literal requests onto the original bearer, purpose and material. -/
def forecastUse (word : Word) (bearer : Party) (purpose : Use) (good : Good) : ℚ :=
  (word.map fun request => requestedUse request bearer purpose good).sum

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem valid_use_has_the_forecast_amount (law : Law)
    (before : RawCurrent Party Good Technology Instrument) (request : Request)
    (paid : law.Valid before request) (bearer : Party) (purpose : Use) (good : Good) :
    flowAt (Optimality.Cost.actualPart law before request (.use purpose)) bearer good =
      requestedUse request bearer purpose good := by
  rw [Optimality.Cost.actualPart, if_pos paid]
  unfold Optimality.Cost.part requestedUse
  cases operation : request.operation with
  | use who bundle kind =>
    simp only [Optimality.Cost.Channel.use.injEq]
    split
    · rw [RawLaw.debit, Production.material, operation]
    · rfl
  | _ => simp [flowAt, amount]

private theorem paid_suffix_delivery (source : C) (word : Word)
    (paid : Trace source word (Execution.endAt source (Execution.primitiveScript word)))
    (bearer : Party) (purpose : Use) (good : Good) :
    let law := Physical.Public.interpreter source.native.input
    ((Execution.inventory source (Execution.primitiveScript word)).map fun item =>
      flowAt (Optimality.Cost.actualPart law item.before item.request (.use purpose)) bearer good).sum =
      forecastUse word bearer purpose good := by
  let law := Physical.Public.interpreter source.native.input
  let read := fun request : Request => requestedUse request bearer purpose good
  dsimp only
  rw [Execution.primitive_inventory paid 0]
  calc
    _ = (((law.execute source.raw 0 word).items.map ExecutionItem.request).map read).sum := by
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro item listed
      exact valid_use_has_the_forecast_amount law item.before item.request
        (Execution.admitted_items_of_original_trace paid 0 item listed) bearer purpose good
    _ = _ := by rw [RawLaw.inventory_requests_exact]; rfl

theorem paid_trace_adds_exactly_the_forecast_use (source : C) (past : Script) (word : Word)
    (paid : Trace (Execution.endAt source past) word
      (Execution.endAt (Execution.endAt source past) (Execution.primitiveScript word)))
    (bearer : Party) (purpose : Use) (good : Good) :
    Demand.delivered source (past ++ Execution.primitiveScript word) bearer purpose good =
      Demand.delivered source past bearer purpose good + forecastUse word bearer purpose good := by
  let now := Execution.endAt source past
  let law := Physical.Public.interpreter now.native.input
  have same : source.native.handlerFace.rootRead = law := by
    change Physical.Public.interpreter source.native.input =
      Physical.Public.interpreter (Execution.endAt source past).native.input
    rw [Execution.endAt_input]
  rw [Demand.delivered_is_from_original_inventory, Demand.delivered_is_from_original_inventory,
    Execution.inventory_append, List.map_append, List.sum_append, same]
  rw [paid_suffix_delivery now word paid bearer purpose good]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor
