import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (item : ExecutionItem Party Good Port Technology Instrument)

inductive RecipeFailure : Type
  | signer (failed : ¬ RawLaw.SignerMatches item.request)
  | policy (failed : law.operationAllowed item.before item.request ≠ true)
  | permission (port : Port) (original : port ∈ law.requiredPorts item.before item.request)
      (notAllowed : law.allowed item.before.technology port item.request.signer ≠ true)
      (notConsented : law.controller item.before.technology port ∉ item.request.consents)
  | demand (failed : ¬ law.ClaimGuard item.before item.request)
  | debit (entry : (Party × Good) × ℚ) (original : entry ∈ law.debit item.before item.request) (negative : entry.2 < 0)
  | credit (entry : (Party × Good) × ℚ) (original : entry ∈ law.credit item.before item.request) (negative : entry.2 < 0)

inductive RecipeResult : Type
  | ready (facts : RecipeFacts law [item])
  | blocked (issue : RecipeFailure law item)

noncomputable def inspectRecipeAt : RecipeResult law item := by
  haveI : Decidable (RawLaw.SignerMatches item.request) := by
    unfold RawLaw.SignerMatches
    cases item.request.operation <;> infer_instance
  haveI : Decidable (law.ClaimGuard item.before item.request) := by
    unfold RawLaw.ClaimGuard
    cases item.request.operation with
    | use _ _ purpose => cases purpose <;> infer_instance
    | _ => infer_instance
  if signer : RawLaw.SignerMatches item.request then
    if policy : law.operationAllowed item.before item.request = true then
      match inspectAll (fun port => law.allowed item.before.technology port item.request.signer = true ∨
          law.controller item.before.technology port ∈ item.request.consents) (law.requiredPorts item.before item.request) with
      | .blocked port original failed => exact .blocked (.permission port original (fun h => failed (.inl h)) (fun h => failed (.inr h)))
      | .ready permission =>
        if demand : law.ClaimGuard item.before item.request then
          match inspectAll (fun entry : (Party × Good) × ℚ => 0 ≤ entry.2) (law.debit item.before item.request) with
          | .blocked entry original negative => exact .blocked (.debit entry original (lt_of_not_ge negative))
          | .ready debit =>
            match inspectAll (fun entry : (Party × Good) × ℚ => 0 ≤ entry.2) (law.credit item.before item.request) with
            | .blocked entry original negative => exact .blocked (.credit entry original (lt_of_not_ge negative))
            | .ready credit =>
              exact .ready (by intro next member; cases List.mem_singleton.mp member; exact ⟨signer,policy,permission,demand,debit,credit⟩)
        else exact .blocked (.demand demand)
    else exact .blocked (.policy policy)
  else exact .blocked (.signer signer)

omit [DecidableEq Instrument] [DecidableEq Good] in
theorem recipe_failure_is_the_original_raw_source_failure (issue : RecipeFailure law item) :
    ¬ RecipeFacts law [item] := by
  intro facts
  have atItem := facts item List.mem_cons_self
  cases issue with
  | signer failed => exact failed atItem.1
  | policy failed => exact failed atItem.2.1
  | permission port original notAllowed notConsented =>
    exact (atItem.2.2.1 port original).elim notAllowed notConsented
  | demand failed => exact failed atItem.2.2.2.1
  | debit entry original negative => exact not_le_of_gt negative (atItem.2.2.2.2.1 entry original)
  | credit entry original negative => exact not_le_of_gt negative (atItem.2.2.2.2.2 entry original)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection
