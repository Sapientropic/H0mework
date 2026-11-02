import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingResponsibility
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Source coordinates for one existing Physical occurrence. They contain
raw finite input and its existing algorithm dictionary, never an endpoint,
payment witness, native target or future programme. -/
structure SourceInput (source : OutstandingSource Party Good Port Technology Instrument) where
  portDecidable : DecidableEq Port
  depth : Nat
  count : Nat
  prefixLimit : Nat
  renewalLimit : Nat
  cursor : Physical.Cursor Party Good Port Technology Instrument

namespace SourceInput
variable {source : OutstandingSource Party Good Port Technology Instrument} (actual : SourceInput source)

def before :=
  letI : DecidableEq Port := actual.portDecidable
  Physical.stateAt source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor.past

def result :=
  letI : DecidableEq Port := actual.portDecidable
  Physical.resultAt source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor

def requests :=
  letI : DecidableEq Port := actual.portDecidable
  actual.result.requests source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.before

def after :=
  letI : DecidableEq Port := actual.portDecidable
  actual.result.next source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.before

def world :=
  letI : DecidableEq Port := actual.portDecidable
  Physical.N source.input actual.depth actual.count

def root :=
  letI : DecidableEq Port := actual.portDecidable
  Physical.ledgerRoot source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor

def visit := actual.root.toRoot.initialVisit

def occurrence := actual.root.emitted actual.visit.current

def generated := actual.root.generatedAtTemporalVisit (.finite actual.visit)

def successor : SourceNativeLedgerGeneratedSuccessorAt actual.occurrence actual.generated.wholeLedgerWriteBack := by
  letI : DecidableEq Port := actual.portDecidable
  change SourceNativeLedgerGeneratedSuccessorAt _
    ((Physical.ledgerCompiler source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor).compile _)
  dsimp only [Physical.ledgerCompiler]
  split <;> exact PUnit.unit

theorem source_next_is_the_same_input_consumption :
    actual.successor.targetCurrent = Physical.next actual.cursor := by
  let : DecidableEq Port := actual.portDecidable
  have original : (actual.root.toRoot.evolutionAt actual.visit.current).nextCurrent? = some (Physical.next actual.cursor) := by
    change ((Physical.sourceAt source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor).toRootSource.actual.compile
      (Physical.emitted source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor actual.cursor)).nextCurrent? = _
    rw [Physical.compiler_eq_source_choice]
    split <;> rfl
  exact Option.some.inj (actual.successor.next_eq.symm.trans original)

def Paid (index : source.Slot) : Prop :=
  source.seed.task.earliest ≤ actual.before.raw.clock ∧
    actual.after.raw.clock ≤ source.seed.task.deadline ∧
    Exit.Necessity.BundlePaid source.seed.law actual.before.raw actual.requests
      (source.seed.slot index).bearer (source.seed.slot index).goods (source.seed.slot index).purpose

instance (index : source.Slot) : Decidable (actual.Paid index) := by
  unfold Paid
  infer_instance

/-- Both views are restrictions of this emitted occurrence. Neither creates
a period boundary: before/after are read from its actual command compiler. -/
structure Receipt where
  successor : SourceNativeLedgerGeneratedSuccessorAt actual.occurrence actual.generated.wholeLedgerWriteBack
  source_next : successor.targetCurrent = Physical.next actual.cursor

def receipt : Receipt actual := ⟨actual.successor, actual.source_next_is_the_same_input_consumption⟩

theorem receipt_after_is_the_same_physical_current :
    letI : DecidableEq Port := actual.portDecidable
    (Physical.stateAt source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit
      actual.receipt.successor.targetCurrent.past) = actual.after := by
  let : DecidableEq Port := actual.portDecidable
  rw [actual.receipt.source_next]
  exact Physical.consumed_input_generates_its_own_after source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor

private def SameRows {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  ∀ generated : SourceNativeLedgerGeneratedSuccessorAt occurrence image,
    ∀ entry, ((generated.ledgerEvolution.destination entry).1).1 = entry.1

theorem receipt_keeps_every_original_responsibility
    (entry : OpenResponsibilityAt actual.world
      (actual.root.toRoot.supportAt actual.visit.current)) :
    ((actual.receipt.successor.ledgerEvolution.destination entry).1).1 = entry.1 := by
  let portEq : DecidableEq Port := actual.portDecidable
  have all : SameRows actual.generated.wholeLedgerWriteBack := by
    change SameRows ((Physical.ledgerCompiler source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor).compile _)
    dsimp only [Physical.ledgerCompiler]
    split <;> intro generated original <;>
      exact congrArg Sigma.fst (Physical.destination_is_original_entry source.input actual.depth actual.count
        actual.prefixLimit actual.renewalLimit actual.cursor actual.cursor original)
  exact all _ entry

end SourceInput

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput.receipt
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput.receipt_after_is_the_same_physical_current
