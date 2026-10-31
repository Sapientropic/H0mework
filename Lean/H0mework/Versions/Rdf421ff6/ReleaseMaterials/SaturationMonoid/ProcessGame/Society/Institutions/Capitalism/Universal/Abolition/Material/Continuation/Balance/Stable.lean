import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.Support
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.NonFinancial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

def StableRequest (request : Request Party Good Port Technology Instrument) : Prop :=
  Root.Settlement.NonFinancialRequest request ∧
    match request.operation with | .revise .. => False | _ => True

instance (request : Request Party Good Port Technology Instrument) : Decidable (StableRequest request) := by
  unfold StableRequest
  cases request.operation <;> infer_instance

def StableWord (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ request ∈ word, StableRequest request

instance (word : RawEvent Party Good Port Technology Instrument) : Decidable (StableWord word) := by
  unfold StableWord
  infer_instance

private theorem stable_step_coordinates
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (safe : StableRequest request) :
    (law.step current request).claims = current.claims ∧
    (law.step current request).technology = current.technology ∧
    (law.step current request).clock = current.clock ∧
    (law.step current request).round = current.round := by
  refine ⟨safe.1.step_claims law current request, ?_, ?_, ?_⟩
  · unfold RawLaw.step
    split
    · change (match request.operation with | .revise _ target => target | _ => current.technology) = _
      have fixed := safe.2
      cases kind : request.operation <;> simp_all
    · rfl
  · unfold RawLaw.step
    split <;> rfl
  · unfold RawLaw.step
    split <;> rfl

theorem stable_execution_coordinates
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument) (safe : StableWord word) :
    (law.execute current index word).final.claims = current.claims ∧
    (law.execute current index word).final.technology = current.technology ∧
    (law.execute current index word).final.clock = current.clock ∧
    (law.execute current index word).final.round = current.round := by
  induction word generalizing current index with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons request tail ih =>
      have head := stable_step_coordinates law current request (safe request List.mem_cons_self)
      have later := ih (law.step current request) (index + 1)
        (fun original present => safe original (List.mem_cons_of_mem _ present))
      exact ⟨later.1.trans head.1, later.2.1.trans head.2.1,
        later.2.2.1.trans head.2.2.1, later.2.2.2.trans head.2.2.2⟩

/-- The endpoint is derived from the actual finite flow. No endpoint state
or inventory equality is supplied to this producer. -/
theorem generated_gain_endpoint
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (safe : StableWord word) :
    (law.execute current 0 word).final = current.addReserve (gain law current word) := by
  have fixed := stable_execution_coordinates law current 0 word safe
  apply RawCurrent.ext
  · funext person good
    exact exact_stock_after_original_effects law current word person good
  · exact fixed.1
  · exact fixed.2.1
  · exact fixed.2.2.1
  · exact fixed.2.2.2

theorem finite_balance_generates_closed_period
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (safe : StableWord word) (balanced : Balanced law current word) :
    (law.execute current 0 word).final = current := by
  rw [generated_gain_endpoint law current word safe]
  apply RawCurrent.ext
  · funext person good
    change current.stock person good + gain law current word person good = _
    rw [balanced_gain_zero law current word balanced, add_zero]
  · rfl
  · rfl
  · rfl
  · rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.generated_gain_endpoint
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.finite_balance_generates_closed_period
