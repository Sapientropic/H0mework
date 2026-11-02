import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

def InjectiveLedger {N : WorldRelationNetwork} {before after : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N before after) : Prop :=
  Function.Injective (fun entry => (evolution.origin entry).1) ∧
    Function.Injective (fun entry => (evolution.destination entry).1)

theorem injective_cast {N : WorldRelationNetwork} {Index : Type}
    {source : CompleteLiveLedgerAt N} (target : Index → CompleteLiveLedgerAt N)
    {left right : Index} (same : left = right)
    (evolution : LedgerWriteEvolutionAt N source (target left)) (injective : InjectiveLedger evolution) :
    InjectiveLedger (Eq.mp (congrArg (fun index => LedgerWriteEvolutionAt N source (target index)) same) evolution) := by
  cases same
  exact injective

def liftedMap {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after : N.Support} (first last : law.DebtState)
    (mapping : OpenResponsibilityAt N before → OpenResponsibilityAt N after) :
    OpenResponsibilityAt (ExtendedNetwork N law) (before, some first) →
      OpenResponsibilityAt (ExtendedNetwork N law) (after, some last) :=
  (activeInventoryPresentation last (ConstructivePresentation.refl _)).forward ∘
    Option.map mapping ∘ (activeInventoryPresentation first (ConstructivePresentation.refl _)).backward

theorem liftedMap_injective {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after : N.Support} (first last : law.DebtState)
    (mapping : OpenResponsibilityAt N before → OpenResponsibilityAt N after)
    (injective : Function.Injective mapping) : Function.Injective (liftedMap first last mapping) :=
  (Function.LeftInverse.injective (activeInventoryPresentation last (ConstructivePresentation.refl _)).backward_forward).comp
    ((Option.map_injective injective).comp
      (Function.LeftInverse.injective (activeInventoryPresentation first (ConstructivePresentation.refl _)).forward_backward))

theorem jointStep_injective {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after : N.Support} {first last : law.DebtState}
    (base : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩) (owner : OpenResponsibilityAt N before)
    (paid : law.StepAt first last) (injective : InjectiveLedger base) :
    InjectiveLedger (jointStepLedgerEvolution base owner paid) := by
  have backward : (fun entry => ((jointStepLedgerEvolution base owner paid).origin entry).1) =
      liftedMap last first (fun entry => (base.origin entry).1) := by
    funext entry
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => rfl
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl
  have forward : (fun entry => ((jointStepLedgerEvolution base owner paid).destination entry).1) =
      liftedMap first last (fun entry => (base.destination entry).1) := by
    funext entry
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => rfl
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl
  exact ⟨backward ▸ liftedMap_injective last first _ injective.1,
    forward ▸ liftedMap_injective first last _ injective.2⟩

theorem wholeTransport_injective {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after : N.Support} {first last : law.DebtState}
    (base : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩) (owner : OpenResponsibilityAt N before)
    (carried : law.TransportAt first last) (injective : InjectiveLedger base) :
    InjectiveLedger (wholeTransport base owner carried) := by
  have backward : (fun entry => ((wholeTransport base owner carried).origin entry).1) =
      liftedMap last first (fun entry => (base.origin entry).1) := by
    funext entry
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => rfl
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl
  have forward : (fun entry => ((wholeTransport base owner carried).destination entry).1) =
      liftedMap first last (fun entry => (base.destination entry).1) := by
    funext entry
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => rfl
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl
  exact ⟨backward ▸ liftedMap_injective last first _ injective.1,
    forward ▸ liftedMap_injective first last _ injective.2⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

theorem base_injective (current : Current input frame registered) :
    InjectiveLedger (baseEvolution input frame registered current) :=
  injective_cast (fun occurrence =>
    ⟨frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence⟩)
    (frame.program.emit current.1).target_emitted (frame.program.emit current.1).evolution
    ⟨frame.origin_injective current.1, frame.destination_injective current.1⟩

theorem whole_injective (current : Current input frame registered) :
    InjectiveLedger (wholeEvolution input frame registered current) := by
  unfold wholeEvolution
  refine injective_cast (fun target => activeLedger
    (supportAt input frame registered (next input frame registered current)).1 target)
    (next_state input frame registered current.2).symm _ ?_
  unfold actionEvolution
  cases actionReceipt input frame registered current.2 with
  | inl paid => exact jointStep_injective _ _ paid (base_injective input frame registered current)
  | inr carried => exact wholeTransport_injective _ _ carried (base_injective input frame registered current)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
