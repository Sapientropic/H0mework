import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "C" => code claim current word
local notation "newRoot" => targetRoot claim current word
local notation "stepResult" => Compiler.successor C false

private theorem canonicalKey_target_eq {network : WorldRelationNetwork} {voc : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure network voc) {current leftTarget rightTarget : voc.Current}
    (same : leftTarget = rightTarget)
    (left : (root.toRoot.evolutionAt current).nextCurrent? = some leftTarget)
    (right : (root.toRoot.evolutionAt current).nextCurrent? = some rightTarget)
    (entry : OpenResponsibilityAt network (root.source.source.toRootSource.account.supportOf (root.emitted current))) :
    (root.canonicalTargetEntryAtNext left entry).1 = (root.canonicalTargetEntryAtNext right entry).1 := by
  cases same
  rfl

theorem target_row_keeps_the_same_original_key :
    (rawGenerated claim current word).target.targetEntry.1 = .inr (Responsibility.Family.activationLaw claim).debtId := by
  change ((newRoot).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (stepResult).next_eq current.row).1 = _
  refine (canonicalKey_target_eq (newRoot).toAuthoritativeRoot.toLedgerRoot
    (Compiler.successor_current C false) (stepResult).next_eq (Compiler.next_eq C false) current.row).trans ?_
  apply Compiler.canonical_key C false current.row _
  exact ((code_keeps_every_original_key claim current word).1 current.row).trans current.rowKey

def rawNext : Current (oldN := oldN) claim where
  V := targetV claim current word
  root := newRoot
  visit := (rawGenerated claim current word).target.targetVisit
  row := (rawGenerated claim current word).target.targetEntry
  rowKey := target_row_keeps_the_same_original_key claim current word
  authority := (rawGenerated claim current word).target.targetAuthority
  basis := current.basis
  actualLaw := current.actualLaw
  members := current.members
  contextFace := {
    projection := oldProjection claim current word current.contextFace.projection
    active := current.contextFace.active
    classifier_eq := current.contextFace.classifier_eq }
  context_heq := current.context_heq

theorem next_reads_the_actual_updated_state :
    Current.state claim (rawNext claim current word) = updated claim current word := by
  have sameSupport : Current.support claim (rawNext claim current word) =
      ((Current.support claim current).1,some (updated claim current word)) := by
    change Fibre.supportAt claim current word (stepResult).targetCurrent
      (current.root.emitted current.visit.current) = _
    rw [Compiler.successor_current C false]
    exact Fibre.emitted_support claim current word true
  have old := Option.some_get (Current.active claim (rawNext claim current word))
  exact Option.some.inj (old.trans (congrArg Prod.snd sameSupport))

theorem raw_next_retains_the_entire_original_support :
    (Current.support claim (rawNext claim current word)).1 = (Current.support claim current).1 := by
  change (Fibre.supportAt claim current word (stepResult).targetCurrent
    (current.root.emitted current.visit.current)).1 = _
  have lower := congrArg (fun support : oldN.Support × Option (Responsibility.Family.State claim) => support.1)
      (Fibre.emitted_support claim current word true)
  exact (congrArg (fun phase : Bool => (Fibre.supportAt claim current word phase
    (current.root.emitted current.visit.current)).1) (Compiler.successor_current C false)).trans lower

theorem next_uses_the_same_world :
    (rawGenerated claim current word).target.TargetN =
      DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim) := rfl

theorem raw_next_is_the_canonical_root_next :
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
      (rawGenerated claim current word).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      Current.erase claim (rawNext claim current word) :=
  congrArg (fun next =>
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),next⟩ :
      AnyAuthoritativeRootCurrent)) (rawGenerated claim current word).target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
