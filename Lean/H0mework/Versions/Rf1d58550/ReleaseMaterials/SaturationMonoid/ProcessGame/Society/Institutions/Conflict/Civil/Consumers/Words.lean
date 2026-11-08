import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Stop
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Menu
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Primitive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualReadback

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving
open PublicFunction (PublicTaskSpec)

noncomputable section

abbrev opening : C := Conflict.Consumers.Evolving.source
local notation "script" => Quantities.Execution.primitiveScript

def investment : R := ⟨false, [], false, [], .use false [(false, 112)] .investment⟩
def intervention : W := [investment]
def calm : W := [settle, life true]
def exit : W := [life false]
def routedAttack : W := front ++ [settle, levy]
def command : List Bool := [true]
def task : PublicTaskSpec Bool Bool :=
  ⟨[⟨false, [(true, 1)], .necessity⟩], 0, 10, by decide +kernel⟩

theorem original_citizen_keeps_standing (word : W) (actor : Bool) : actor ∈ (Root.terminal opening word).members := by
  let endAt := Root.terminal opening word
  obtain ⟨same, depth, count⟩ := Quantities.Execution.the_actual_script_keeps_the_original_reader_indices opening (script word)
  obtain ⟨_, sourceDepth, sourceCount⟩ :=
    Quantities.Execution.the_actual_script_keeps_the_original_reader_indices Original.source (script [issue])
  have original := Innovation.Contribution.Pricing.Consumers.Actual.source_parameters
  change endAt.native.input = opening.native.input at same
  change endAt.native.depth = opening.native.depth at depth
  change endAt.native.count = opening.native.count at count
  change opening.native.depth = Original.source.native.depth at sourceDepth
  change opening.native.count = Original.source.native.count at sourceCount
  apply Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  change actor ∈ Actual.members endAt.native.input endAt.native.depth endAt.native.count
  rw [same, sourceInput, depth, sourceDepth, original.1, count, sourceCount, original.2.1]
  cases actor <;> decide +kernel

theorem paid_original_word (word : W)
    (consents : ∀ request ∈ word, request.consents = [])
    (signed : ∀ item ∈ (Physical.Public.interpreter compact).rawItems oldRaw word,
      compact.law.Valid item.before item.request)
    (food : ∀ person : Bool, 1 ≤ Material.actualUse (Macro.Public.Scope.checkInput compact) oldRaw word person .necessity true) :
    Root.Paid opening word := by
  have boundary := conflictPaid.trace.a_nonempty_execution_starts_at_the_actual_ready_boundary
    (by simp [conflict, Conflict.Consumers.Evolving.front])
  have auth : Root.Authorized opening word := by
    unfold Root.Authorized
    rw [sourceInput, sourceRead]
    exact signed
  have valid : ∀ item ∈ (Physical.Public.interpreter opening.native.input).rawItems opening.raw word,
      (Physical.Public.interpreter opening.native.input).Valid item.before item.request :=
    fun item present => PublicFunction.valid_physical opening.native.input.law item.before item.request (auth item present)
  obtain ⟨actual, finished, _⟩ :=
    Quantities.Execution.pay_checked_primitives opening word 0 boundary.1 boundary.2 consents valid
  refine ⟨auth, actual, Quantities.settle opening _ ⟨?_, finished⟩⟩
  apply (Quantities.Demand.primitive_covers_iff_original_floor actual).mpr
  intro cell listed
  obtain ⟨bearer, _present, required⟩ := List.mem_flatMap.mp listed
  rw [sourceInput] at required ⊢
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] at required
  have one : amount Bool [(true, 1)] true = 1 := by decide +kernel
  rw [List.mem_singleton.mp required, sourceRead]
  simpa only [one] using food bearer

theorem the_peace_exit_is_paid_after_the_citizen_invests :
    Root.Paid opening ((intervention ++ calm) ++ exit) :=
  paid_original_word _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem the_original_attack_cannot_requisition_the_spent_stock :
    ¬ Root.Paid opening (intervention ++ conflict) := by
  intro paid
  have auth := paid.authorized
  unfold Root.Authorized at auth
  rw [sourceInput, sourceRead] at auth
  exact (by decide +kernel : ¬ ∀ item ∈ (Physical.Public.interpreter compact).rawItems oldRaw
    (intervention ++ conflict), compact.law.Valid item.before item.request) auth

theorem a_differently_financed_attack_is_an_actual_bypass :
    Root.Paid opening (intervention ++ routedAttack) :=
  paid_original_word _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem the_investment_is_the_citizens_own_action : CivilAction opening command intervention := by
  refine ⟨by simp [intervention], ?_⟩
  intro item listed
  change item ∈ [⟨0, opening.raw, investment⟩] at listed
  rw [List.mem_singleton.mp listed]
  refine ⟨original_citizen_keeps_standing [] false, by simp [investment, command], rfl, ?_⟩
  intro lot inside _
  unfold RawLaw.actualDebit at inside
  split at inside
  · have same : lot = ((false, false), (112 : ℚ)) := by
      simpa only [RawLaw.debit, investment, locate, List.map_cons, List.map_nil, List.mem_singleton] using inside
    rw [same]
    rfl
  · exact (List.not_mem_nil inside).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Consumers
