import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation Quantifiers.Joint
open Financial.Installation (KeepsKeys)

noncomputable section

private def ImageKeepsKeys {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt occurrence image, KeepsKeys actual.ledgerEvolution

private theorem actual_flow_keys {N : WorldRelationNetwork} (F : Abolition.Accounting.Root.Compiler.Flow N)
    (current : F.Current) (keys : KeepsKeys (F.evolution current)) :
    KeepsKeys (Abolition.Accounting.Root.Compiler.successor F current).ledgerEvolution := by
  have all : ImageKeepsKeys ((Abolition.Accounting.Root.Compiler.ledgerCompiler F).compile
      (Abolition.Accounting.Root.Compiler.emitted F current)) := by
    dsimp only [Abolition.Accounting.Root.Compiler.ledgerCompiler,Abolition.Accounting.Root.Compiler.sourcePacket]
    split <;> intro actual <;> change KeepsKeys (Abolition.Accounting.Root.Compiler.patch F current).toLedgerWriteEvolution
    all_goals
      unfold KeepsKeys
      rw [Abolition.Accounting.Root.Compiler.patch_destination,Abolition.Accounting.Root.Compiler.patch_origin]
      exact keys
  exact all _

private theorem joint_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after : N.Support} {source target : law.DebtState}
    (base : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩)
    (owner : OpenResponsibilityAt N before) (step : law.StepAt source target)
    (keys : KeepsKeys base) : KeepsKeys (jointStepLedgerEvolution base owner step) := by
  constructor
  · rintro ⟨key,opened⟩
    cases key with
    | inl old => exact congrArg Sum.inl (keys.1 ⟨old,opened⟩)
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl
  · rintro ⟨key,opened⟩
    cases key with
    | inl old => exact congrArg Sum.inl (keys.2 ⟨old,opened⟩)
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

theorem the_actual_old_source_declaration_keeps_every_key : KeepsKeys (sourceSuccessor seed grossClaim).ledgerEvolution :=
  actual_flow_keys (Rebase.flow seed grossClaim) Rebase.Stage.entered
    (Rebase.every_stage_keeps_the_original_keys seed grossClaim Rebase.Stage.entered)

theorem gross_admission_keeps_every_original_key : KeepsKeys (firstWrite seed grossClaim) :=
  joint_keys _ _ _ (the_actual_old_source_declaration_keeps_every_key seed grossClaim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission
