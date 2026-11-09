import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Dispatch
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Recurrence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument
local notation "Script" => Reparation.Actual.Script Party Good Port M Instrument

/-- Repeat the same admission at every original cut. Only emitted inputs
advance the dispatcher used by the next check. -/
def guardedHistory (cut : C) : Script → Script
  | [] => []
  | attempt :: later =>
    let emitted := (dispatchAdmission cut attempt).selected
    emitted ++ guardedHistory (endAt cut emitted) later

theorem every_guarded_history_has_source_authority (cut : C) (attempts : Script) :
    AdmittedHistory cut (guardedHistory cut attempts) := by
  induction attempts generalizing cut with
  | nil => simp [guardedHistory, AdmittedHistory, inventory]
  | cons input tail ih =>
    exact (dispatchAdmission cut input).selected_is_admissible.append (ih _)

theorem every_admitted_history_runs_without_substitution (cut : C) (history : Script)
    (admitted : AdmittedHistory cut history) : guardedHistory cut history = history := by
  induction history generalizing cut with
  | nil => rfl
  | cons input tail later =>
    obtain ⟨first, rest⟩ := AdmittedHistory.restrict (past := [input]) (suffix := tail) admitted
    simp only [guardedHistory, every_admissible_input_is_forwarded cut input first, later _ rest, List.singleton_append]

variable [DecidableEq Technology] {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

theorem LiveGrant.refutes_a_single_signer {items : List Item} {candidate actor : Party}
    (grant : LiveGrant base scope items candidate)
    (independent : ∀ item ∈ items, IndependentNomination item.request)
    (alone : ∀ item ∈ items, item.request.signer = actor) : False := by
  obtain ⟨proposal, acceptance, _, _, _, originalProposal, originalAcceptance, _, _, _, _, different⟩ :=
    grant.two_distinct_original_signers independent
  exact different ((alone proposal (List.mem_of_getElem? originalProposal)).trans
    (alone acceptance (List.mem_of_getElem? originalAcceptance)).symm)

theorem one_signer_cannot_restore_after_any_admitted_history (cut : C) (history : Script)
    (installed : Emergency.Installed cut base scope) (released : Civil.Mandate.Released cut.raw)
    (admitted : AdmittedHistory cut history) (actor : Party)
    (alone : ∀ item ∈ inventory cut history, item.request.signer = actor) :
    (endAt cut history).raw.technology.holder = none := by
  cases holder : (endAt cut history).raw.technology.holder with
  | none => rfl
  | some candidate =>
    have grant := the_actual_successor_holder_has_original_grant cut history installed released admitted.original_authority
      candidate holder
    exact (grant.refutes_a_single_signer (fun item listed => (admitted item listed).2) alone).elim

/-- Even a temporary restoration between two release cuts cannot give one
signer an admitted debit at the original protected address. -/
theorem one_signer_cannot_make_any_admitted_protected_debit (cut : C) (history : Script)
    (installed : Emergency.Installed cut base scope) (released : Civil.Mandate.Released cut.raw)
    (admitted : AdmittedHistory cut history) (actor : Party)
    (alone : ∀ item ∈ inventory cut history, item.request.signer = actor)
    (front : List Item) (item : Item) (back : List Item)
    (position : inventory cut history = front ++ item :: back) (debit : (Party × Good) × ℚ)
    (charged : debit ∈ (PublicFunction.physicalLaw cut.native.input.law).actualDebit item.before item.request)
    (protectedAddress : base.stockPort cut.raw.technology.technology debit.1.1 debit.1.2 = scope.service) : False := by
  have grant := (the_actual_protected_debit_has_original_grant cut history installed released
    admitted.original_authority front item back position debit charged protectedAddress).1
  have within (current : Item) (listed : current ∈ front) : current ∈ inventory cut history :=
    position.symm ▸ List.mem_append_left _ listed
  exact grant.refutes_a_single_signer (fun current listed => (admitted current (within current listed)).2)
    (fun current listed => alone current (within current listed))

theorem one_signer_cannot_make_any_admitted_protected_operation (cut : C) (history : Script)
    (installed : Emergency.Installed cut base scope) (released : Civil.Mandate.Released cut.raw)
    (admitted : AdmittedHistory cut history) (actor : Party)
    (alone : ∀ item ∈ inventory cut history, item.request.signer = actor)
    (front : List Item) (item : Item) (back : List Item)
    (position : inventory cut history = front ++ item :: back)
    (ordinary : Emergency.Ordinary item.request)
    (protectedUse : Emergency.UsesMandate base scope item.before item.request) : False := by
  have grant := (the_actual_protected_operation_has_an_earlier_live_grant cut history installed released
    admitted.original_authority front item back position ordinary protectedUse).1
  have within (current : Item) (listed : current ∈ front) : current ∈ inventory cut history :=
    position.symm ▸ List.mem_append_left _ listed
  exact grant.refutes_a_single_signer (fun current listed => (admitted current (within current listed)).2)
    (fun current listed => alone current (within current listed))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
