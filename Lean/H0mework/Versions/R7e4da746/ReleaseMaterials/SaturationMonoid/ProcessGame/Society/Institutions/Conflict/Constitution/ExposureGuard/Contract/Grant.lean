import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Runtime.Selection
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Admission
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open ForcePeace.Renewal (IndependentNomination PaidCommand MaterialTrace)
open Quantities.Execution (endAt inventory)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Req" => Request Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
def Grants (request : Req) : Prop :=
  match request.operation with
  | .revise _ target =>
    match target.last with
    | some (.propose _) | some .accept | some .renew => True
    | _ => False
  | _ => False

instance (request : Req) : Decidable (Grants request) := by
  unfold Grants
  split <;> try infer_instance
  split <;> infer_instance

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem a_non_grant_preserves_independent_nomination (request : Req) (ordinary : ¬ Grants request) :
    IndependentNomination request := by
  by_contra failed
  obtain ⟨_, target, same, named⟩ :=
    ForcePeace.Renewal.not_independent_is_an_original_self_nomination request failed
  exact ordinary (by simp only [Grants, same, named])

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}

/-- Opening, accepting, or renewing the original power requires a fresh
answer from every exposed person at that actual paid item. -/
def grantRule : Rule seed := fun roster answers past input position =>
  let request := (originalItems (seed := seed) past input)[position].request
  IndependentNomination request ∧
    (Grants request → ∀ person ∈ roster, answers past input position person = true)

instance : DecidableRule (grantRule (seed := seed)) := fun _ _ _ _ _ => by
  unfold grantRule
  infer_instance

theorem a_non_grant_needs_only_its_original_material_authors
    (roster : List Party) (answers : OwnerAnswers seed) (past : Word) (input : Input)
    (position : Fin (originalItems (seed := seed) past input).length)
    (ordinary : ¬ Grants (originalItems (seed := seed) past input)[position].request) :
    grantRule roster answers past input position :=
  ⟨a_non_grant_preserves_independent_nomination _ ordinary, fun grant => (ordinary grant).elim⟩

theorem any_withholding_original_bearer_vetoes_a_grant
    (roster : List Party) (answers : OwnerAnswers seed) (past : Word) (input : Input)
    (position : Fin (originalItems (seed := seed) past input).length)
    (person : Party) (exposed : person ∈ roster)
    (passed : grantRule roster (withhold answers person) past input position) :
    ¬ Grants (originalItems (seed := seed) past input)[position].request := by
  intro grant
  have approval := passed.2 grant person exposed
  rw [withholding_uses_the_original_personal_lane] at approval
  cases approval

theorem a_refused_grant_names_the_original_withholding_bearer
    (roster : List Party) (answers : OwnerAnswers seed) (past : Word) (input : Input)
    (position : Fin (originalItems (seed := seed) past input).length)
    (denied : ¬ grantRule roster answers past input position) :
    let req := (originalItems (seed := seed) past input)[position].request
    ¬ IndependentNomination req ∨
      (Grants req ∧ ∃ person ∈ roster, answers past input position person = false) := by
  dsimp only
  by_cases independent : IndependentNomination (originalItems (seed := seed) past input)[position].request
  · right
    have openGrant : Grants (originalItems (seed := seed) past input)[position].request := by
      by_contra notGrant
      exact denied ⟨independent, fun grant => (notGrant grant).elim⟩
    refine ⟨openGrant, ?_⟩
    by_contra noRefusal
    exact denied ⟨independent, fun _ person original =>
      Bool.eq_true_of_not_eq_false (fun withheld => noRefusal ⟨person, original, withheld⟩)⟩
  · exact Or.inl independent

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
private theorem a_non_grant_does_not_propose (request : Req) (closed : ¬ Grants request) :
    Civil.Mandate.DoesNotPropose request := by
  unfold Civil.Mandate.DoesNotPropose
  cases operation : request.operation with
  | revise _ target =>
    intro candidate nominal
    exact closed (by simp only [Grants, operation, nominal])
  | _ => trivial

variable [DecidableEq Technology]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

/-- Any actual installed-law inventory without a new grant keeps both
original power slots released, including automatic review and code routes. -/
theorem an_actual_no_grant_word_keeps_the_original_mandate_released
    (cut : C) (word : Word) (installed : Emergency.Installed cut base scope)
    (released : Civil.Mandate.Released cut.raw) (lawful : Reparation.Actual.SourceAuthority cut word)
    (noGrant : ∀ item ∈ inventory cut word, ¬ Grants item.request) :
    Civil.Mandate.Released (endAt cut word).raw := by
  have fold {start final : M} {items : List Item} (trace : MaterialTrace base scope start items final)
      (closed : start.holder = none ∧ start.offered = none)
      (without : ∀ item ∈ items, ¬ Grants item.request) : final.holder = none ∧ final.offered = none := by
    induction trace with
    | nil => exact closed
    | @cons _ _ item _ atCurrent _ _ later =>
      have prior : Civil.Mandate.Released item.before := by
        unfold Civil.Mandate.Released
        rwa [atCurrent]
      exact later (Civil.Mandate.a_step_without_new_nomination_keeps_release base scope item.before
        item.request prior (a_non_grant_does_not_propose _ (without item List.mem_cons_self)))
        (fun next listed => without next (List.mem_cons_of_mem _ listed))
  exact fold (ForcePeace.Renewal.the_actual_inventory_carries_the_mandate_state base scope cut word installed lawful)
    released noGrant

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
