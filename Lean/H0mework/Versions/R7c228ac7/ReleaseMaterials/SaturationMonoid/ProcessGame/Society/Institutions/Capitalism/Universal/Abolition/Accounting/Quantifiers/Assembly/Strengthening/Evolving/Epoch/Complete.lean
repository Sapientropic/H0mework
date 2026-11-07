import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Validity
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Accounting
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Receipt

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

structure ClosedAt : Prop where
  actualNext : current.advance.inquiry.erase = (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase
  actualLaw : (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
    (RootInquiryProcessNode.active current.advance.inquiry)
  sourceControl : current.control = current.binding.value
  sourceCompiler : (Compilation.state current).compileInquiry PUnit.unit = Compilation.compileUnit current
  sourceReport : ∀ complete, (Transition.returnedReport current complete).proposal = current.proposal ∧
    (Transition.returnedReport current complete).choice = current.choice ∧
    (Transition.returnedReport current complete).physical = current.physicalResult
  writtenControl : ∀ complete, (Transition.next current complete).control = current.afterControl
  writtenPhysical : ∀ complete, (Transition.next current complete).raw = current.physicalResult.next.raw
  actualLedger : current.sourceLedger.next = current.advance.native
  claimsInjective : Function.Injective current.sourceLedger.claimMap
  wholeLedger : ∀ row, (current.sourceLedger.carry row).claim = current.sourceLedger.claimMap row.claim ∧
    (current.sourceLedger.carry row).progressBudget ≤ row.progressBudget
  productiveHistory : current.sourceLedger.carry current.native.rows.productive = current.sourceLedger.next.rows.productive
  grossHistory : current.sourceLedger.carry current.native.rows.gross = current.sourceLedger.next.rows.gross
  productivePaid : current.advance.native.rows.productive.progressBudget = 0
  grossPaid : current.advance.native.rows.gross.progressBudget = 0
  activeNoCapital : Global.NoCapital current.advance.native.handlerFace.rootRead

theorem the_source_generates_its_whole_ledger_actual_epoch : ClosedAt current where
  actualNext := current.advance_is_the_actual_root_successor.1
  actualLaw := current.advance_is_the_actual_root_successor.2
  sourceControl := current.control_is_the_actual_root_coordinate
  sourceCompiler := rfl
  sourceReport := Transition.the_actual_root_returns_its_original_input_choice_and_physical_verdict current
  writtenControl := Transition.next_reads_the_written_control current
  writtenPhysical := Transition.next_state_reads_the_same_actual_material_target current
  actualLedger := current.sourceLedger_is_the_actual_next
  claimsInjective := current.sourceLedger.claim_injective
  wholeLedger := current.every_original_responsibility_keeps_its_claim_and_never_refills
  productiveHistory := current.sourceLedger.productive_history
  grossHistory := current.sourceLedger.gross_history
  productivePaid := current.advance.native.rows.productive_zero
  grossPaid := current.advance.native.rows.gross_zero
  activeNoCapital := current.advance.native.the_actual_root_interpreter_excludes_every_capital_relation

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
