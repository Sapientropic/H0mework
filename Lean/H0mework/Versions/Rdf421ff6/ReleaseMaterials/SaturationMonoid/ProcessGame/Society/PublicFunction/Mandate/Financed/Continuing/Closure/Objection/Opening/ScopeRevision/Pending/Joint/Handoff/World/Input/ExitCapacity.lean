import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity.Material

/-! Source stocks choose a paid exit or an exact finite-word material
obstruction. Existing authority and every liability stay in the actual input. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable (epoch : Epoch)

instance (before : Current) : Decidable (Nonnegative before) :=
  decidable_of_iff (0 ≤ before.stock false .feedstock ∧ 0 ≤ before.stock false .service ∧
    0 ≤ before.stock true .feedstock ∧ 0 ≤ before.stock true .service) (by
      constructor
      · intro values actor good
        cases actor <;> cases good
        · exact values.1
        · exact values.2.1
        · exact values.2.2.1
        · exact values.2.2.2
      · intro values
        exact ⟨values false .feedstock,values false .service,values true .feedstock,values true .service⟩)

inductive Kind where
  | unheld | ready | materialShortfall | invalidStock
  deriving DecidableEq

inductive Result (before : Current) where
  | private unheld (absent : before.technology.holder = none)
  | private ready (healthy : Nonnegative before) (available : Envelope before)
      (payment : Paid epoch .exit before) (selected : choose epoch .exit before = some payment)
  | private shortfall (actor : Bool) (holder : before.technology.holder = some actor)
      (healthy : Nonnegative before) (absent : ¬ Envelope before)
      (allWords : ∀ word : List Action, ∀ signer,
        let after := ((Mandate.law base epoch.scope).execute before 0 word).final
        ¬ (Mandate.law base epoch.scope).Valid after (request epoch.scope after signer .exit))
  | private invalid (reason : ¬ Nonnegative before)

def generate (before : Current) : Result epoch before :=
  match holder : before.technology.holder with
  | none => .unheld holder
  | some actor => if healthy : Nonnegative before then
      if available : Envelope before then
        let present := source_material_envelope_generates_a_real_exit epoch before actor holder (healthy actor .service) available
        .ready healthy available ((choose epoch .exit before).get present) (Option.some_get present).symm
      else .shortfall actor holder healthy available
        (fun word signer => below_envelope_forbids_every_later_exit epoch before word healthy available signer)
    else .invalid healthy

def Result.kind {before : Current} : Result epoch before → Kind
  | .unheld .. => .unheld
  | .ready .. => .ready
  | .shortfall .. => .materialShortfall
  | .invalid .. => .invalidStock

theorem Result.material_shortfall_covers_every_finite_raw_word {before : Current}
    (result : Result epoch before) (blocked : result.kind epoch = .materialShortfall) :
    total before .service < 1 ∧ total before .feedstock < 1 ∧
    ∀ word : List Action, ∀ signer,
      let after := ((Mandate.law base epoch.scope).execute before 0 word).final
      ¬ (Mandate.law base epoch.scope).Valid after (request epoch.scope after signer .exit) := by
  cases result
  next absent => cases blocked
  next healthy available payment selected => cases blocked
  next actor holder healthy absent allWords =>
    have gap : total before .service < 1 ∧ total before .feedstock < 1 := by
      simpa only [Envelope,not_or,not_le] using absent
    exact ⟨gap.1,gap.2,allWords⟩
  next reason => cases blocked

variable {epoch} (inventory : Inventory epoch)

theorem actual_paid_exit_is_the_source_envelopes_own_execution
    (payment : Paid epoch .exit (current epoch inventory.inputs))
    (selected : choose epoch .exit (current epoch inventory.inputs) = some payment) :
    (Input.execution inventory .exit).after.technology.holder = none ∧
    (Input.execution inventory .exit).after.technology.offered = none ∧
    (Input.execution inventory .exit).after.claims =
      (Input.commandBefore epoch .exit (current epoch inventory.inputs) payment.choice).claims := by
  have effect := paid_exit_retires_the_actual_holder epoch _ payment
  have claims := paid_exit_keeps_all_pre_exit_claims epoch _ payment
  rw [(Input.execution inventory .exit).after_exact]
  change ((Mandate.law base epoch.scope).next (Input.execution inventory .exit).before
    (Input.execution inventory .exit).submitted).technology.holder = none ∧
    ((Mandate.law base epoch.scope).next (Input.execution inventory .exit).before
      (Input.execution inventory .exit).submitted).technology.offered = none ∧
    ((Mandate.law base epoch.scope).next (Input.execution inventory .exit).before
      (Input.execution inventory .exit).submitted).claims = _
  rw [(actual_word_and_cut inventory .exit).1,(actual_word_and_cut inventory .exit).2]
  rw [Input.emit,paid_word_is_the_actual_selected_candidate epoch _ _ payment selected]
  exact ⟨effect.2.1,effect.2.2,claims⟩

theorem Result.ready_has_its_original_selected_payment {before : Current} (result : Result epoch before)
    (ready : result.kind epoch = .ready) : ∃ payment, choose epoch .exit before = some payment := by
  cases result
  next absent => cases ready
  next healthy available payment selected => exact ⟨payment,selected⟩
  next actor holder healthy absent allWords => cases ready
  next reason => cases ready

def ActualExitEffect : Prop :=
  ∃ payment : Paid epoch .exit (current epoch inventory.inputs),
    choose epoch .exit (current epoch inventory.inputs) = some payment ∧
    (Input.execution inventory .exit).after.technology.holder = none ∧
    (Input.execution inventory .exit).after.technology.offered = none ∧
    (Input.execution inventory .exit).after.claims =
      (Input.commandBefore epoch .exit (current epoch inventory.inputs) payment.choice).claims

theorem generated_ready_is_actually_executed
    (ready : (generate epoch (current epoch inventory.inputs)).kind epoch = .ready) : ActualExitEffect inventory := by
  obtain ⟨payment,selected⟩ := Result.ready_has_its_original_selected_payment _ ready
  exact ⟨payment,selected,actual_paid_exit_is_the_source_envelopes_own_execution inventory payment selected⟩

structure Disposition where
  private mk ::
  capacity : Result epoch (current epoch inventory.inputs)
  capacity_exact : capacity = generate epoch (current epoch inventory.inputs)
  input : Input.Disposition inventory .exit
  input_exact : input = Input.produce inventory .exit
  effect : capacity.kind epoch = .ready → ActualExitEffect inventory

def produce : Disposition inventory :=
  ⟨generate epoch (current epoch inventory.inputs),rfl,Input.produce inventory .exit,rfl,
    generated_ready_is_actually_executed inventory⟩

def Disposition.financialRun (result : Disposition inventory) :
    (Financial.Family.process sources).Run inventory.finance.current result.input.nextInventory.finance.current := by
  rw [result.input.exact_after]
  exact Input.financialRun inventory .exit

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity
