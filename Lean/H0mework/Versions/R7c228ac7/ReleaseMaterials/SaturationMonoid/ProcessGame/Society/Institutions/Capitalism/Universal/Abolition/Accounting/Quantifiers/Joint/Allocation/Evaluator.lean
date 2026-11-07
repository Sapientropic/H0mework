import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Kernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def actualReadings : Readings Party Good Port Technology Instrument :=
  ⟨fun item => (actualLaw seed).actualDebit item.before item.request,
    fun item => (actualLaw seed).actualCredit item.before item.request⟩

def incoming (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  Kernel.incoming (actualReadings seed) item key

theorem incoming_nonnegative (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) :
    0 ≤ incoming seed item key := le_max_left _ _

def productiveTransfer (old : Party × Good → ℚ) (p : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  Kernel.reservation (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response) (actualReadings seed) old p work item key

def productiveNet (p : Bool) (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  Kernel.net (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response) (actualReadings seed) p item key

def grossTransfer (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) : ℚ :=
  Kernel.gross (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response) (Entitlement.Duty.scope (window seed))
    (actualReadings seed) old p g work item key

/-- Reservation protects the original productive quota. Every real unit not
assigned to gross remains available for this word's later material costs. -/
def productiveCredit (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  Kernel.productiveCredit (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response) (Entitlement.Duty.scope (window seed))
    (actualReadings seed) old p g work item key

theorem productive_transfer_nonnegative (old : Party × Good → ℚ) (p : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) :
    0 ≤ productiveTransfer seed old p work item key := by
  unfold productiveTransfer Kernel.reservation
  split
  · split <;> try exact le_rfl
    split
    · exact first_nonnegative _ _ (le_max_left _ _)
    · exact le_rfl
  · exact le_rfl

theorem gross_transfer_nonnegative (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    0 ≤ grossTransfer seed old p g work item key :=
  Kernel.gross_nonnegative _ _ _ _ _ _ _ _ _ _

def afterItem (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) : Working Party Good :=
  Kernel.after (Responsibility.controllerCohort mechanism past nature response)
    (Responsibility.Family.positiveScope mechanism past nature response) (Entitlement.Duty.scope (window seed))
    (actualReadings seed) old p g work item

def run (old : Party × Good → ℚ) (productiveDeclared grossDeclared : Bool)
    (gross : Entitlement.Duty.Key (Party := Party) (Good := Good) → ℚ) (nonnegative : ∀ key, 0 ≤ gross key)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) :
    Working Party Good :=
  ((actualLaw seed).rawItems before word).foldl (afterItem seed old productiveDeclared grossDeclared)
    ⟨fun _ => 0,gross,nonnegative⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation
