import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Checks

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

omit [DecidableEq Instrument] in
theorem actual_debit_uses_own_stock (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (lot : (Party × Good) × ℚ)
    (paid : lot ∈ law.actualDebit item.before item.request) : lot.1.1 = item.request.signer := by
  rw [RawLaw.actualDebit, if_pos self.2.2.1] at paid
  have kind := self.1
  cases operation : item.request.operation with
  | produce person =>
      simp only [SelfOperation, operation] at kind
      simp only [RawLaw.debit, operation, locate, List.mem_map] at paid
      obtain ⟨goods, _original, rfl⟩ := paid
      exact kind.symm
  | use person goods purpose =>
      simp only [SelfOperation, operation] at kind
      simp only [RawLaw.debit, operation, locate, List.mem_map] at paid
      obtain ⟨goods, _original, rfl⟩ := paid
      exact kind.1.symm
  | _ => simp only [SelfOperation, operation] at kind

omit [DecidableEq Instrument] in
theorem actual_credit_returns_to_producer (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (lot : (Party × Good) × ℚ)
    (produced : lot ∈ law.actualCredit item.before item.request) : lot.1.1 = item.request.signer := by
  rw [RawLaw.actualCredit, if_pos self.2.2.1] at produced
  have kind := self.1
  cases operation : item.request.operation with
  | produce person =>
      simp only [SelfOperation, operation] at kind
      simp only [RawLaw.credit, operation, locate, List.mem_map] at produced
      obtain ⟨goods, _original, rfl⟩ := produced
      exact kind.symm
  | use person goods purpose => simp only [RawLaw.credit, operation, List.not_mem_nil] at produced
  | _ => simp only [SelfOperation, operation] at kind

omit [DecidableEq Instrument] in
theorem own_authority_is_actually_executable (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) (port : Port) (required : port ∈ law.requiredPorts item.before item.request) :
    law.controller item.before.technology port = item.request.signer ∧
      law.allowed item.before.technology port item.request.signer = true := by
  refine ⟨self.2.2.2.1 port required, ?_⟩
  rcases self.2.2.1.2.1 port required with allowed | consent
  · exact allowed
  · rw [self.2.1] at consent
    exact (List.not_mem_nil consent).elim

private theorem execute_preserves_claims (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Nat)
    (checked : ∀ item ∈ (law.execute current index word).items, At law item) :
    (law.execute current index word).final.claims = current.claims := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simp only [RawLaw.execute, List.forall_mem_cons] at checked
      exact (ih _ (index + 1) checked.2).trans
        (original_claims_are_retained law ⟨index, current, request⟩ checked.1)

theorem complete_word_retains_every_original_claim (current : RawCurrent Party Good Technology Instrument)
    (group : List Party) (word : RawEvent Party Good Port Technology Instrument)
    (checked : Checks law current group word) : (law.next current word).claims = current.claims :=
  execute_preserves_claims law current word 0 (fun item present => (checked.1 item present).1)

#print axioms actual_debit_uses_own_stock
#print axioms actual_credit_returns_to_producer
#print axioms complete_word_retains_every_original_claim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction
