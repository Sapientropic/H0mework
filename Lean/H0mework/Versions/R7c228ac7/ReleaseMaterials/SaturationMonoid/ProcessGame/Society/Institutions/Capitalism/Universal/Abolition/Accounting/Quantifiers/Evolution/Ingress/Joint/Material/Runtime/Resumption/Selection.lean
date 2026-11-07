import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Future

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

attribute [local irreducible] Execution.Selected.items Planning.selected Planning.actualNext Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))
  (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

local notation "F" => nativeFrame seed claim enough
local notation "visit₀" => completedVisit seed claim
local notation "actual₀" => completedActual seed claim enough
local notation "authority₀" => completedAuthority seed claim enough
local notation "C" => Factory.Resumption.Action.preparedContext F visit₀ actual₀ authority₀
local notation "bare" => Factory.Resumption.Action.bareFrame F visit₀ C
local notation "visit₁" => Factory.Resumption.Action.nextVisit F visit₀ actual₀ authority₀ reader
local notation "actual₁" => Factory.Resumption.Action.nextActual F visit₀ actual₀ authority₀ reader
local notation "authority₁" => Factory.Resumption.Action.nextAuthority F visit₀ actual₀ authority₀ reader

theorem the_resumed_native_cursor_has_no_pending_work :
    ¬ Public.Inquiry.HasWork bare (actual₁).actual := by
  change ¬ ((Drain.completed seed claim).bodyPaid = false ∨
    (Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)
      (Drain.completed seed claim)).isSome = true)
  rw [(Drain.the_finite_source_loop_finishes_at_the_original_native_consumption seed claim).2.2,
    Drain.the_finite_source_budget_leaves_no_original_head seed claim]
  simp

variable {sourceDepth sourceCount : Nat} {review : Option (ReviewPhase.ContextAt seed.input)}
  (origin : Abolition.Functions.Revision.Context (input := seed.input) (review := review)
    seed.depth seed.count 0 0 sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)

def nextState := Public.Inquiry.state origin admission bare reader visit₁ actual₁ authority₁

theorem the_actual_next_compiler_is_the_original_native_selection :
    (nextState seed claim enough reader origin admission).compileInquiry PUnit.unit =
      Public.Inquiry.compileUnit origin admission bare reader visit₁ actual₁ authority₁ :=
  Factory.Resumption.Action.the_resumed_compiler_is_the_original_native_selection
    F visit₀ actual₀ authority₀ reader origin admission

def nextRawAction := Public.Inquiry.rawCore origin admission bare reader visit₁ actual₁ authority₁
  (the_resumed_native_cursor_has_no_pending_work seed claim enough reader)

theorem the_actual_next_compiler_selects_the_dynamic_source_action :
    (nextState seed claim enough reader origin admission).compileInquiry PUnit.unit =
      .actualAction (nextRawAction seed claim enough reader origin admission) := by
  change Public.Inquiry.compileUnit origin admission bare reader visit₁ actual₁ authority₁ = _
  exact dif_neg (the_resumed_native_cursor_has_no_pending_work seed claim enough reader)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
