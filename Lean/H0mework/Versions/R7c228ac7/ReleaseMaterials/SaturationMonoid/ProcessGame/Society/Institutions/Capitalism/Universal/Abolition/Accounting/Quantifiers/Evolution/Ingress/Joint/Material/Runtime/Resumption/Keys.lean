import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

local notation "F" => Runtime.flow seed claim

private def ImageKeepsKeys (current : FinancialCurrent seed)
    (image : SourceNativeLedgerEvolutionAt (Abolition.Accounting.Root.Compiler.source F)
      (Abolition.Accounting.Root.Compiler.emitted F current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (Abolition.Accounting.Root.Compiler.emitted F current) image,
    Financial.Installation.KeepsKeys actual.ledgerEvolution

theorem every_actual_root_successor_keeps_all_original_responsibility_keys (current : FinancialCurrent seed) :
    Financial.Installation.KeepsKeys (Abolition.Accounting.Root.Compiler.successor F current).ledgerEvolution := by
  have rows : Financial.Installation.KeepsKeys (Abolition.Accounting.Root.Compiler.patch F current).toLedgerWriteEvolution := by
    unfold Financial.Installation.KeepsKeys
    rw [Abolition.Accounting.Root.Compiler.patch_destination F current,Abolition.Accounting.Root.Compiler.patch_origin F current]
    exact Runtime.every_original_key_survives_the_joint_actual_write seed claim current
  have all : ImageKeepsKeys seed claim current
      ((Abolition.Accounting.Root.Compiler.ledgerCompiler F).compile (Abolition.Accounting.Root.Compiler.emitted F current)) := by
    dsimp only [Abolition.Accounting.Root.Compiler.ledgerCompiler,Abolition.Accounting.Root.Compiler.sourcePacket]
    split <;> intro actual <;> exact rows
  exact all _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
