import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Ledger

import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.FirstWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev originalSuccessor (cut : Nat) :=
  Boundary.continuing root.toAuthoritativeRoot.toLedgerRoot (boundary.history.next_eq_at_visit cut)

theorem originalTargetCurrent (cut : Nat) : (originalSuccessor root boundary cut).targetCurrent =
    (boundary.history.visitAt (cut + 1)).current :=
  Option.some.inj ((originalSuccessor root boundary cut).next_eq.symm.trans
    (boundary.history.next_eq_at_visit cut))

theorem originalTargetSupport (cut : Nat) : (originalSuccessor root boundary cut).targetOccurrence.1 =
    root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt (cut + 1)).current :=
  (Evolving.nextSupportEq root (.finite (boundary.history.visitAt cut))
    (originalSuccessor root boundary cut)).trans
      (congrArg root.toAuthoritativeRoot.toRoot.supportAt (originalTargetCurrent root boundary cut))

def originalEvolution (cut : Nat) : LedgerWriteEvolutionAt N
    ⟨root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current⟩
    ⟨root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt (cut + 1)).current⟩ :=
  Eq.mp (congrArg (fun support => LedgerWriteEvolutionAt N
    ⟨root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current⟩ ⟨support⟩)
      (originalTargetSupport root boundary cut)) (originalSuccessor root boundary cut).ledgerEvolution

abbrev Current := Nat ⊕ Nat

def rawCurrent : Current → V.Current
  | .inl cut => (boundary.history.visitAt cut).current
  | .inr _ => boundary.current

def supportAt (current : Current) : (W root boundary).Support :=
  (root.toAuthoritativeRoot.toRoot.supportAt (rawCurrent root boundary current),
    match current with | .inl _ => false | .inr _ => true)

def next : Current → Current
  | .inl cut => .inl (cut + 1)
  | .inr phase => .inr (phase + 1)

def evolution : (current : Current) → LedgerWriteEvolutionAt (W root boundary)
    ⟨supportAt root boundary current⟩ ⟨supportAt root boundary (next current)⟩
  | .inl cut => liftLedger root boundary (originalEvolution root boundary cut)
  | .inr 0 => firstLedger root boundary
  | .inr (_ + 1) => LedgerWriteEvolutionAt.identity _

theorem the_new_finite_ledger_is_the_original_whole_ledger (cut : Nat) :
    evolution root boundary (.inl cut) = liftLedger root boundary (originalEvolution root boundary cut) := rfl

theorem the_boundary_first_write_is_the_source_registration :
    evolution root boundary (.inr 0) = firstLedger root boundary := rfl

theorem later_writes_carry_the_same_registered_rows (phase : Nat) :
    evolution root boundary (.inr (phase + 1)) = LedgerWriteEvolutionAt.identity
      ⟨supportAt root boundary (.inr (phase + 1))⟩ := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
