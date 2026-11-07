import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

private theorem other_bearer_has_no_debit (goods : Bundle Good) (bearer person : Party)
    (good : Good) (different : bearer ≠ person) : flowAt (locate bearer goods) person good = 0 := by
  induction goods with
  | nil => rfl
  | cons entry rest ih =>
      have separate : (bearer, entry.1) ≠ (person, good) :=
        fun same => different (congrArg Prod.fst same)
      change (if (bearer, entry.1) = (person, good) then entry.2 else 0) +
        flowAt (locate bearer rest) person good = 0
      rw [if_neg separate, ih, add_zero]

omit [DecidableEq Instrument] in
private theorem use_part (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (person : Party) (purpose : Use) (good : Good) :
    flowAt (Optimality.Cost.actualPart law item.before item.request (.use purpose)) person good =
      match item.request.operation with
      | .use bearer _ kind =>
          if bearer = person ∧ kind = purpose then
            flowAt (law.actualDebit item.before item.request) person good else 0
      | _ => 0 := by
  unfold Optimality.Cost.actualPart
  by_cases paid : law.Valid item.before item.request
  · rw [if_pos paid]
    cases operation : item.request.operation <;> rw [Optimality.Cost.part, operation]
    case use bearer goods kind =>
      rw [RawLaw.actualDebit, if_pos paid]
      simp only [RawLaw.debit, operation, Optimality.Cost.Channel.use.injEq]
      by_cases useKind : purpose = kind
      · subst kind
        simp only [if_true, and_true]
        split
        · rfl
        · exact other_bearer_has_no_debit goods bearer person good (by assumption)
      · simp [useKind, Ne.symm useKind, flowAt, amount]
    all_goals simp [flowAt, amount]
  · rw [if_neg paid]
    cases item.request.operation <;> simp [RawLaw.actualDebit, paid, flowAt, amount]

variable [DecidableEq Port]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

theorem covers_iff_original_floor_of_paid_inventory {source : C}
    (script : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
    (word : RawEvent Party Good Port Technology Instrument)
    (index : ExecutionItem Party Good Port Technology Instrument → Nat)
    (actual : Execution.inventory source script =
      ((Physical.Public.interpreter source.native.input).rawItems source.raw word).map
        (fun item => {item with index := index item})) :
    Covers source script ↔
      Material.OriginalNeedFloor (Public.Scope.checkInput source.native.input)
        (Actual.origin source.native.input source.native.depth source.native.count)
        source.raw source.members word := by
  have same (bearer : Party) (purpose : Use) (good : Good) :
      delivered source script bearer purpose good =
      Material.actualUse (Public.Scope.checkInput source.native.input) source.raw word bearer purpose good := by
    rw [delivered_is_from_original_inventory, actual]
    unfold Material.actualUse
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro item _
    exact use_part source.native.handlerFace.rootRead {item with index := index item} bearer purpose good
  simp only [Covers, requirements, same, Material.OriginalNeedFloor]

theorem primitive_covers_iff_original_floor {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) :
    Covers source (Execution.primitiveScript word) ↔
      Material.OriginalNeedFloor (Public.Scope.checkInput source.native.input)
        (Actual.origin source.native.input source.native.depth source.native.count)
        source.raw source.members word :=
  covers_iff_original_floor_of_paid_inventory _ _ (fun _ => 0) (Execution.primitive_inventory actual 0)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand
