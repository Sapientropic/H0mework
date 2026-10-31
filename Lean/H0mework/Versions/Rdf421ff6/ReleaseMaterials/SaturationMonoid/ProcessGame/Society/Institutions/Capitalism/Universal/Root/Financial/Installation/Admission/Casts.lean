import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.JointTransport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

theorem destination_cast_heq {N : WorldRelationNetwork} {Index : Type}
    {source : CompleteLiveLedgerAt N} (target : Index → CompleteLiveLedgerAt N)
    {left right : Index} (same : left = right)
    (evolution : LedgerWriteEvolutionAt N source (target left)) :
    HEq (Eq.mp (congrArg (fun index => LedgerWriteEvolutionAt N source (target index)) same)
      evolution).destination evolution.destination := by
  cases same
  rfl

theorem destination_entry_cast_heq {N : WorldRelationNetwork} {Index : Type}
    {source : CompleteLiveLedgerAt N} (target : Index → CompleteLiveLedgerAt N)
    {left right : Index} (same : left = right)
    (evolution : LedgerWriteEvolutionAt N source (target left)) (entry : source.Entry) :
    HEq (((Eq.mp (congrArg (fun index => LedgerWriteEvolutionAt N source (target index)) same)
      evolution).destination entry).1) ((evolution.destination entry).1) := by
  cases same
  rfl

theorem joint_destination_cast_heq {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after other : N.Support} {first last : law.DebtState}
    (same : after = other) (base : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩)
    (owner : OpenResponsibilityAt N before) (step : law.StepAt first last) :
    HEq (jointStepLedgerEvolution
      (Eq.mp (congrArg (fun support => LedgerWriteEvolutionAt N ⟨before⟩ ⟨support⟩) same) base)
      owner step).destination (jointStepLedgerEvolution base owner step).destination := by
  cases same
  rfl

theorem oldEntry_state_heq {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {support : N.Support} {left right : law.DebtState} (same : left = right)
    (entry : OpenResponsibilityAt N support) :
    HEq (oldEntry (law := law) (state? := some left) entry)
      (oldEntry (law := law) (state? := some right) entry) := by
  cases same
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
