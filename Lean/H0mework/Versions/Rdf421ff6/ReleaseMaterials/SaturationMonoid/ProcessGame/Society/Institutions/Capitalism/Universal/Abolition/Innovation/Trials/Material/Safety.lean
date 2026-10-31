import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Safety

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (mechanism : Mechanism Party Good Port Technology Instrument)

def addresses := mechanism.code.parties.product mechanism.code.goods

def required (person : Party) (good : Good) : ℚ :=
  amount Good (mechanism.code.law.necessities mechanism.code.initial person) good +
    amount Good (mechanism.code.law.mandatoryMaintenance mechanism.code.initial person) good

/-- The original life and maintenance reserve is protected separately for
each person and good. Trial gains cannot compensate another person's loss. -/
def Floor (current : RawCurrent Party Good Technology Instrument) : Prop :=
  ∀ address ∈ addresses mechanism, required mechanism address.1 address.2 ≤ current.stock address.1 address.2

instance (current : RawCurrent Party Good Technology Instrument) : Decidable (Floor mechanism current) := by
  unfold Floor
  infer_instance

structure Deficit (current : RawCurrent Party Good Technology Instrument) where
  address : Party × Good
  original : address ∈ addresses mechanism
  short : current.stock address.1 address.2 < required mechanism address.1 address.2

theorem Deficit.refutes {current : RawCurrent Party Good Technology Instrument}
    (issue : Deficit mechanism current) : ¬ Floor mechanism current :=
  fun floor => (not_le_of_gt issue.short) (floor issue.address issue.original)

inductive AtDecision (current : RawCurrent Party Good Technology Instrument) where
  | accepted (floor : Floor mechanism current)
  | rejected (issue : Deficit mechanism current)

def inspectAt (current : RawCurrent Party Good Technology Instrument) : AtDecision mechanism current :=
  match Material.inspectList (fun address : Party × Good =>
      required mechanism address.1 address.2 ≤ current.stock address.1 address.2) (addresses mechanism) with
  | .clear floor => .accepted floor
  | .failure address original failed => .rejected ⟨address, original, lt_of_not_ge failed⟩

variable (nature : mechanism.Nature)

def Safe : Prop :=
  Floor mechanism mechanism.code.initial ∧
    ∀ item ∈ (mechanism.execution nature).items,
      Floor mechanism item.before ∧ Floor mechanism (mechanism.code.law.step item.before item.request)

instance : Decidable (Safe mechanism nature) := by
  unfold Safe
  infer_instance

inductive Issue where
  | initial (issue : Deficit mechanism mechanism.code.initial)
  | before (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ (mechanism.execution nature).items) (issue : Deficit mechanism item.before)
  | after (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ (mechanism.execution nature).items)
      (issue : Deficit mechanism (mechanism.code.law.step item.before item.request))

theorem Issue.refutes (issue : Issue mechanism nature) : ¬ Safe mechanism nature := by
  intro safe
  cases issue with
  | initial deficit => exact deficit.refutes mechanism safe.1
  | before item original deficit => exact deficit.refutes mechanism (safe.2 item original).1
  | after item original deficit => exact deficit.refutes mechanism (safe.2 item original).2

inductive Decision where
  | accepted (safe : Safe mechanism nature)
  | rejected (issue : Issue mechanism nature)

def check : Decision mechanism nature :=
  match inspectAt mechanism mechanism.code.initial with
  | .rejected issue => .rejected (.initial issue)
  | .accepted initial =>
      match Material.inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
          Floor mechanism item.before ∧ Floor mechanism (mechanism.code.law.step item.before item.request))
          (mechanism.execution nature).items with
      | .clear all => .accepted ⟨initial, all⟩
      | .failure item original failed =>
          match inspectAt mechanism item.before with
          | .rejected issue => .rejected (.before item original issue)
          | .accepted before =>
              match inspectAt mechanism (mechanism.code.law.step item.before item.request) with
              | .rejected issue => .rejected (.after item original issue)
              | .accepted after => False.elim (failed ⟨before, after⟩)

private theorem execute_preserves_checked_floor
    (initial : RawCurrent Party Good Technology Instrument) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument)
    (start : Floor mechanism initial)
    (each : ∀ item ∈ (mechanism.code.law.execute initial index word).items,
      Floor mechanism (mechanism.code.law.step item.before item.request)) :
    Floor mechanism (mechanism.code.law.execute initial index word).final := by
  induction word generalizing initial index with
  | nil => exact start
  | cons request tail ih =>
      exact ih (mechanism.code.law.step initial request) (index + 1)
        (each ⟨index, initial, request⟩ List.mem_cons_self)
        (fun item member => each item (List.mem_cons_of_mem _ member))

theorem every_protected_person_keeps_the_original_life_and_maintenance_budget
    (safe : Safe mechanism nature) (person : Party) (good : Good) :
    required mechanism person good ≤ (mechanism.after nature).stock person good := by
  have final := execute_preserves_checked_floor mechanism mechanism.code.initial 0
    (mechanism.word nature) safe.1 (fun item member => (safe.2 item member).2)
  exact final (person, good) (List.mem_product.mpr
    ⟨mechanism.code.parties_cover person, mechanism.code.goods_cover good⟩)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Safety
