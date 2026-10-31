import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

/-!
# Public service planning from primitive requests

The task contains beneficiaries, material service bundles and a time window,
but no provider or replacement word. The action alphabet is raw source code;
all words up to the explicit execution budget are generated here.

The physical interpretation removes permission and policy gates, retaining
stocks, techniques, maintenance costs, claim guards and settlement rates.
It is used only for obstruction evidence, never for actual execution.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure ServiceSlot (Party Good : Type u) where
  bearer : Party
  goods : Bundle Good
  purpose : Use

structure PublicTaskSpec (Party Good : Type u) where
  slots : List (ServiceSlot Party Good)
  earliest : ℚ
  deadline : ℚ
  demand : ∃ slot ∈ slots, ∃ requirement ∈ slot.goods, 0 < requirement.2

def physicalLaw (law : RawLaw Party Good Port Technology Instrument) :
    RawLaw Party Good Port Technology Instrument :=
  { law with allowed := fun _ _ _ => true, policy := .unrestricted }

omit [DecidableEq Instrument] in
theorem valid_physical (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (accepted : law.Valid current request) :
    (physicalLaw law).Valid current request := by
  refine ⟨⟨accepted.1.1, rfl⟩, ?_, accepted.2.2⟩
  intro port inside
  exact Or.inl rfl

theorem execute_physical_of_authorized
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument)
    (physical : ∀ item ∈ ((physicalLaw law).execute current index word).items,
      (physicalLaw law).Valid item.before item.request)
    (authorized : ∀ item ∈ ((physicalLaw law).execute current index word).items,
      law.Valid item.before item.request) :
    law.execute current index word = (physicalLaw law).execute current index word := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail ih =>
    have front := authorized ⟨index, current, request⟩ List.mem_cons_self
    have physicalFront := physical ⟨index, current, request⟩ List.mem_cons_self
    have same : law.step current request = (physicalLaw law).step current request := by
      simp only [RawLaw.step, if_pos front, if_pos physicalFront]
      rfl
    have restPhysical : ∀ item ∈ ((physicalLaw law).execute
        ((physicalLaw law).step current request) (index + 1) tail).items,
        (physicalLaw law).Valid item.before item.request :=
      fun item inside => physical item (List.mem_cons_of_mem _ inside)
    have restAuthorized : ∀ item ∈ ((physicalLaw law).execute
        ((physicalLaw law).step current request) (index + 1) tail).items,
        law.Valid item.before item.request :=
      fun item inside => authorized item (List.mem_cons_of_mem _ inside)
    simp only [RawLaw.execute, same, ih _ _ restPhysical restAuthorized]

def words (alphabet : List (Request Party Good Port Technology Instrument)) :
    Nat → List (RawEvent Party Good Port Technology Instrument)
  | 0 => [[]]
  | depth + 1 => [] :: alphabet.flatMap (fun request =>
      (words alphabet depth).map (List.cons request))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem mem_words_iff
    (alphabet : List (Request Party Good Port Technology Instrument))
    (depth : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    word ∈ words alphabet depth ↔
      word.length ≤ depth ∧ ∀ request ∈ word, request ∈ alphabet := by
  induction depth generalizing word with
  | zero => cases word <;> simp [words]
  | succ depth ih =>
    cases word with
    | nil => simp [words]
    | cons request tail =>
      simp only [words, List.mem_cons, List.cons_ne_nil, false_or,
        List.mem_flatMap, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨head, inside, rest, generated, sameHead, sameTail⟩
        subst head; subst rest
        obtain ⟨bounded, supported⟩ := (ih tail).mp generated
        exact ⟨Nat.succ_le_succ bounded, by simpa using And.intro inside supported⟩
      · rintro ⟨bounded, supported⟩
        refine ⟨request, supported request (Or.inl rfl), tail, ?_, rfl, rfl⟩
        exact (ih tail).mpr ⟨Nat.le_of_succ_le_succ bounded,
          fun action inside => supported action (Or.inr inside)⟩

def ServiceAdequate (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (task : PublicTaskSpec Party Good)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  task.earliest ≤ current.clock ∧
  (law.next current word).clock ≤ task.deadline ∧
  ∀ slot ∈ task.slots,
    Necessity.BundlePaid law current word slot.bearer slot.goods slot.purpose

instance (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (task : PublicTaskSpec Party Good)
    (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (ServiceAdequate law current task word) := by
  unfold ServiceAdequate
  infer_instance

def PhysicallyFeasible (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (task : PublicTaskSpec Party Good)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  (∀ item ∈ (physicalLaw law).rawItems current word,
    (physicalLaw law).Valid item.before item.request) ∧
  ServiceAdequate (physicalLaw law) current task word

def Authorized (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ item ∈ (physicalLaw law).rawItems current word,
    law.Valid item.before item.request

instance (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (task : PublicTaskSpec Party Good)
    (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (PhysicallyFeasible law current task word) := by
  unfold PhysicallyFeasible
  infer_instance

instance (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Authorized law current word) := by
  unfold Authorized
  infer_instance

theorem service_actual_of_authorized
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (task : PublicTaskSpec Party Good)
    (word : RawEvent Party Good Port Technology Instrument)
    (physical : PhysicallyFeasible law current task word)
    (authorized : Authorized law current word) :
    ServiceAdequate law current task word ∧
    (∀ item ∈ law.rawItems current word, law.Valid item.before item.request) := by
  have execution := execute_physical_of_authorized law current 0 word physical.1 authorized
  have items : law.rawItems current word = (physicalLaw law).rawItems current word :=
    congrArg ExecutionResult.items execution
  refine ⟨⟨physical.2.1, physical.2.2.1, ?_⟩, ?_⟩
  · intro slot inside
    rcases physical.2.2.2 slot inside with empty | ⟨item, member, _, matched⟩
    · exact Or.inl empty
    · exact Or.inr ⟨item, items ▸ member, authorized item member, matched⟩
  · intro item inside
    exact authorized item (items ▸ inside)

end SaturationMonoid.ProcessGame.Society.PublicFunction
