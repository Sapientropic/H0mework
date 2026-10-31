import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.LocalRenewal

/-! A finite self-supply check reads the original operations and their paid
stock legs.  It does not classify a relation as non-capital: that decision
still belongs to the source-generated relation family. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def SelfOperation (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with
  | .produce person => request.signer = person
  | .use person _ purpose => request.signer = person ∧
      (purpose = .necessity ∨ purpose = .maintenance)
  | _ => False

instance (request : Request Party Good Port Technology Instrument) : Decidable (SelfOperation request) := by
  unfold SelfOperation
  cases request.operation <;> infer_instance

variable (law : RawLaw Party Good Port Technology Instrument)

def At (item : ExecutionItem Party Good Port Technology Instrument) : Prop :=
  SelfOperation item.request ∧ item.request.consents = [] ∧ law.Valid item.before item.request ∧
    (∀ port ∈ law.requiredPorts item.before item.request,
      law.controller item.before.technology port = item.request.signer) ∧
    (match law.policy with | .opaque _ => False | _ => True)

instance (item : ExecutionItem Party Good Port Technology Instrument) : Decidable (At law item) := by
  unfold At
  cases law.policy <;> infer_instance

def Checks (current : RawCurrent Party Good Technology Instrument) (group : List Party)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  (∀ item ∈ law.rawItems current word, At law item ∧ item.request.signer ∈ group) ∧
    Necessity.AllNeedsPaid law current group word

instance (current : RawCurrent Party Good Technology Instrument) (group : List Party)
    (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Checks law current group word) := by
  unfold Checks
  infer_instance

theorem checked_joint_word (current : RawCurrent Party Good Technology Instrument) (group : List Party)
    (word : RawEvent Party Good Port Technology Instrument) (checked : Checks law current group word) :
    law.jointWord group current word ≠ none := by
  apply law.jointWord_of_internal_execution
  intro item member
  obtain ⟨self, signer⟩ := checked.1 item member
  refine ⟨self.2.2.1, signer, ?_⟩
  intro person included
  rw [self.2.1] at included
  exact (List.not_mem_nil included).elim

theorem original_claims_are_retained (item : ExecutionItem Party Good Port Technology Instrument)
    (self : At law item) : (law.step item.before item.request).claims = item.before.claims := by
  rw [RawLaw.step, if_pos self.2.2.1]
  have kind := self.1
  cases operation : item.request.operation with
  | produce person => simp only [RawLaw.paidStep, RawLaw.nextClaims, operation]
  | use person goods purpose => simp only [RawLaw.paidStep, RawLaw.nextClaims, operation]
  | _ => simp only [SelfOperation, operation] at kind

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction
