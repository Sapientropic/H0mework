import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.Source

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.Readback
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program PublicFunction
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : OutstandingSource Party Good Port Technology Instrument} (actual : SourceInput source)

/-- Use this occurrence's actual cursor for the original generated successor. -/
def successor : SourceNativeLedgerGeneratedSuccessorAt actual.occurrence actual.generated.wholeLedgerWriteBack := by
  letI : DecidableEq Port := actual.portDecidable
  change SourceNativeLedgerGeneratedSuccessorAt _
    ((Physical.ledgerCompiler source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor).compile
      (Physical.emitted source.input actual.depth actual.count actual.prefixLimit actual.renewalLimit actual.cursor actual.cursor))
  dsimp only [Physical.ledgerCompiler]
  split <;> exact PUnit.unit

theorem successor_exact : successor actual = actual.successor := rfl

def receipt : SourceInput.Receipt actual :=
  ⟨successor actual,actual.source_next_is_the_same_input_consumption⟩

@[csimp] theorem successor_codegen : @SourceInput.successor = @successor := rfl
@[csimp] theorem receipt_codegen : @SourceInput.receipt = @receipt := rfl


end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.Readback
