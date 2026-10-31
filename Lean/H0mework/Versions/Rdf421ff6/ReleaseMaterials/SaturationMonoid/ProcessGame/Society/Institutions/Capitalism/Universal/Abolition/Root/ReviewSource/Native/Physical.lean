import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.SourceBirth
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)

/-- Coordinates of one original Physical source occurrence. All effects,
clock readings, requests and ledger receipts are read from its compiler. -/
structure SourceInput where
  portDecidable : DecidableEq Port
  depth : Nat
  count : Nat
  prefixLimit : Nat
  renewalLimit : Nat
  cursor : Physical.Cursor Party Good Port Technology Instrument

namespace SourceInput
variable {code} (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def before :=
  letI := actual.portDecidable
  Physical.stateAt code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor.past

def result :=
  letI := actual.portDecidable
  Physical.resultAt code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor

def requests :=
  letI := actual.portDecidable
  (actual.result (code := code)).requests code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit (actual.before (code := code))

def after :=
  letI := actual.portDecidable
  (actual.result (code := code)).next code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit (actual.before (code := code))

def root :=
  letI := actual.portDecidable
  Physical.ledgerRoot code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor

def visit := (actual.root (code := code)).toRoot.initialVisit
def occurrence := (actual.root (code := code)).emitted (actual.visit (code := code)).current
def generated := (actual.root (code := code)).generatedAtTemporalVisit (.finite (actual.visit (code := code)))

def successor : SourceNativeLedgerGeneratedSuccessorAt
    (actual.occurrence (code := code)) (actual.generated (code := code)).wholeLedgerWriteBack := by
  letI := actual.portDecidable
  change SourceNativeLedgerGeneratedSuccessorAt _
    ((Physical.ledgerCompiler code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor).compile _)
  dsimp only [Physical.ledgerCompiler]
  split <;> exact PUnit.unit

theorem source_next_is_the_original_consumption :
    (actual.successor (code := code)).targetCurrent = Physical.next actual.cursor := by
  let _ : DecidableEq Port := actual.portDecidable
  have next : ((actual.root (code := code)).toRoot.evolutionAt (actual.visit (code := code)).current).nextCurrent? =
      some (Physical.next actual.cursor) := by
    change ((Physical.sourceAt code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor).toRootSource.actual.compile
      (Physical.emitted code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor actual.cursor)).nextCurrent? = _
    rw [Physical.compiler_eq_source_choice]
    split <;> rfl
  exact Option.some.inj ((actual.successor (code := code)).next_eq.symm.trans next)

def Paid (index : Slot code) : Prop :=
  (originalTask code).earliest ≤ (actual.before (code := code)).raw.clock ∧
    (actual.after (code := code)).raw.clock ≤ (originalTask code).deadline ∧
    Exit.Necessity.BundlePaid code.law (actual.before (code := code)).raw (actual.requests (code := code))
      (serviceSlot code index).bearer (serviceSlot code index).goods (serviceSlot code index).purpose

instance (index : Slot code) : Decidable (actual.Paid index) := by unfold Paid; infer_instance

structure Receipt : Type where
  successor : SourceNativeLedgerGeneratedSuccessorAt
    (actual.occurrence (code := code)) (actual.generated (code := code)).wholeLedgerWriteBack
  source_next : successor.targetCurrent = Physical.next actual.cursor

def receipt : Receipt (code := code) actual :=
  ⟨actual.successor (code := code), actual.source_next_is_the_original_consumption (code := code)⟩

theorem receipt_reads_the_same_actual_clock_and_material :
    letI := actual.portDecidable
    Physical.stateAt code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit
      (actual.receipt (code := code)).successor.targetCurrent.past = actual.after (code := code) := by
  let _ : DecidableEq Port := actual.portDecidable
  rw [(actual.receipt (code := code)).source_next]
  exact Physical.consumed_input_generates_its_own_after code.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor

end SourceInput

#print axioms SourceInput.receipt
#print axioms SourceInput.receipt_reads_the_same_actual_clock_and_material

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native
