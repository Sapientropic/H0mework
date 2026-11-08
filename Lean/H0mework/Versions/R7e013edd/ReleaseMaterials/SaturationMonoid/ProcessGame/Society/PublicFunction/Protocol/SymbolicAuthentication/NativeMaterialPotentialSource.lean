import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialSource
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action)
abbrev law := FuelMandateLaw.law true

def total (current : Current) (good : Good) : ℚ :=
  current.stock 0 good + current.stock 1 good + current.stock 2 good
def potential (current : Current) : ℚ :=
  6 * total current .feedstock + 2 * total current .service +
    3 * total current .waste + 3 * total current .energy
def bundleCost (goods : Bundle Good) : ℚ :=
  6 * amount Good goods .feedstock + 2 * amount Good goods .service +
    3 * amount Good goods .waste + 3 * amount Good goods .energy
def quote (request : Action) : ℚ := match request.operation with
  | .use _ goods _ => bundleCost goods
  | .revise _ _ => 2
  | _ => 0
def draw (current : Current) (request : Action) : ℚ := if law.Valid current request then quote request else 0
def spent (items : List (ExecutionItem Party Good Delegation.Funded.Port (Mandate.State Party Bool) Unit)) : ℚ :=
  (items.map fun item => draw item.before item.request).sum
def shortfall (current : Current) (word : List Action) : ℚ := max 0 ((word.map quote).sum - potential current)

private theorem flow_locate (sender party : Party) (goods : Bundle Good) (good : Good) :
    flowAt (locate sender goods) party good = if party = sender then amount Good goods good else 0 := by
  induction goods with
  | nil => simp [flowAt,locate,amount]
  | cons item tail ih =>
    rcases item with ⟨key,quantity⟩
    by_cases owner : party = sender
    · subst party
      simp [flowAt,locate,amount] at ih ⊢
      exact ih
    · have different : sender ≠ party := Ne.symm owner
      simp [flowAt,locate,amount,owner,different] at ih ⊢
      exact ih

@[simp] private theorem flow_empty (party : Party) (good : Good) : flowAt [] party good = 0 := rfl

theorem every_paid_original_operation_has_its_exact_material_balance (current : Current) (request : Action) :
    potential (law.paidStep current request) + quote request = potential current := by
  rcases request with ⟨signer,consents,purpose,gates,operation⟩
  cases operation with
  | produce actor =>
    fin_cases actor <;>
      simp [potential,total,quote,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,FuelMandateLaw.law,
        FuelMandateLaw.base,RenewedQuorumMaterial.base,Mandate.law,Repayment.Recovery.base,flowAt,locate,amount] <;> ring
  | transfer sender recipient goods =>
    fin_cases sender <;> fin_cases recipient <;>
      simp [potential,total,quote,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,flow_locate] <;> ring
  | settle instrument debtor creditor quantity =>
    fin_cases debtor <;> fin_cases creditor <;>
      simp [potential,total,quote,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,FuelMandateLaw.law,
        FuelMandateLaw.base,RenewedQuorumMaterial.base,Mandate.law,Repayment.Recovery.base,flowAt,locate,amount] <;> ring
  | use bearer goods kind =>
    fin_cases bearer <;>
      simp [potential,total,quote,bundleCost,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,flow_locate,
        flow_empty] <;> ring
  | revise actor technology =>
    fin_cases actor <;>
      simp [potential,total,quote,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,FuelMandateLaw.law,
        FuelMandateLaw.base,RenewedQuorumMaterial.base,Mandate.law,Repayment.Recovery.base,
        Repayment.Recovery.scope,flowAt,locate,amount] <;> ring
  | issue _ _ _ _ | assign _ _ _ _ _ | present => simp [potential,total,quote,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,flowAt,amount]

theorem arbitrary_attempts_have_the_exact_paid_balance (current : Current) (request : Action) :
    potential (law.step current request) + draw current request = potential current := by
  by_cases valid : law.Valid current request
  · simpa only [RawLaw.step,draw,if_pos valid] using every_paid_original_operation_has_its_exact_material_balance current request
  · simp [RawLaw.step,draw,valid]

theorem every_original_word_generates_its_complete_material_account (current : Current) (index : Nat) (word : List Action) :
    potential (law.execute current index word).final + spent (law.execute current index word).items = potential current := by
  induction word generalizing current index with
  | nil => simp [RawLaw.execute,spent]
  | cons request tail ih =>
    have first := arbitrary_attempts_have_the_exact_paid_balance current request
    have later := ih (law.step current request) (index+1)
    simp only [RawLaw.execute,spent,List.map_cons,List.sum_cons]
    simp only [spent] at later
    linarith

theorem nonnegative_potential (current : Current) (stocks : ∀ party good, 0 ≤ current.stock party good) :
    0 ≤ potential current := by
  have nonnegative (good : Good) : 0 ≤ total current good := add_nonneg (add_nonneg (stocks _ _) (stocks _ _)) (stocks _ _)
  unfold potential
  linarith [nonnegative .feedstock,nonnegative .service,nonnegative .waste,nonnegative .energy]

theorem paid_draw_is_nonnegative (current : Current) (request : Action) : 0 ≤ draw current request := by
  by_cases valid : law.Valid current request
  · simp only [draw,if_pos valid]
    cases kind : request.operation with
    | use bearer goods purpose =>
      have nonnegative (good : Good) : 0 ≤ amount Good goods good := by
        have entry := amount_nonnegative (law.debit current request) valid.2.2.2.1 (bearer,good)
        change 0 ≤ flowAt (law.debit current request) bearer good at entry
        simpa [RawLaw.debit,kind,flow_locate] using entry
      simp only [quote,kind,bundleCost]
      linarith [nonnegative .feedstock,nonnegative .service,nonnegative .waste,nonnegative .energy]
    | _ => simp [quote,kind]
  · simp [draw,valid]

theorem spent_is_nonnegative (items : List (ExecutionItem Party Good Delegation.Funded.Port (Mandate.State Party Bool) Unit)) :
    0 ≤ spent items := by
  apply List.sum_nonneg
  intro value inside
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp inside
  exact paid_draw_is_nonnegative item.before item.request

theorem execute_stocks_are_nonnegative (current : Current) (index : Nat) (word : List Action)
    (stocks : ∀ party good, 0 ≤ current.stock party good) :
    ∀ party good, 0 ≤ (law.execute current index word).final.stock party good := by
  induction word generalizing current index with
  | nil => exact stocks
  | cons request tail ih => exact ih (law.step current request) (index+1) (law.step_stock_nonnegative current request stocks)

theorem the_actual_source_stock_funds_every_paid_prefix (current : Current) (index : Nat) (word : List Action)
    (stocks : ∀ party good, 0 ≤ current.stock party good) :
    spent (law.execute current index word).items ≤ potential current := by
  have balance := every_original_word_generates_its_complete_material_account current index word
  have remains := nonnegative_potential _ (execute_stocks_are_nonnegative current index word stocks)
  linarith

theorem a_fully_paid_word_consumes_its_original_quote (current : Current) (index : Nat) (word : List Action)
    (paid : ∀ item ∈ (law.execute current index word).items,law.Valid item.before item.request) :
    spent (law.execute current index word).items = (word.map quote).sum := by
  have exactRequests := law.inventory_requests_exact current index word
  have same : (law.execute current index word).items.map (fun item => draw item.before item.request) =
      (law.execute current index word).items.map (fun item => quote item.request) := by
    apply List.map_congr_left
    intro item inside
    simp only [draw,if_pos (paid item inside)]
  unfold spent
  rw [same]
  simpa only [List.map_map,Function.comp_def] using congrArg (fun requests => (requests.map quote).sum) exactRequests

theorem the_generated_shortfall_requires_actual_new_material (current : Current) (word : List Action)
    (stocks : ∀ party good, 0 ≤ current.stock party good) (missing : 0 < shortfall current word) :
    ¬ ∀ item ∈ law.rawItems current word,law.Valid item.before item.request := by
  intro paid
  have funded := the_actual_source_stock_funds_every_paid_prefix current 0 word stocks
  rw [a_fully_paid_word_consumes_its_original_quote current 0 word paid] at funded
  have zero : shortfall current word = 0 := by
    exact max_eq_left (sub_nonpos.mpr funded)
  rw [zero] at missing
  exact (lt_irrefl (0 : ℚ)) missing
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialSource
