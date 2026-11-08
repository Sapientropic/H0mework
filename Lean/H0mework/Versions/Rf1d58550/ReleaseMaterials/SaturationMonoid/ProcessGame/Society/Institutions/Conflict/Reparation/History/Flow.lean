import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Stage
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment.Write

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Financial.Installation.Admission (InjectiveLedger)
open private jointWrite from H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment.Write

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

variable (script : List (Option (Capitalism.Universal.Abolition.Root.Registered.Compile.RawInput
    Party Good Port Technology Instrument))) (safe : NoFinancialBirths (Birth.attacked claim) script)

def oldSupport : Cursor claim script → (Birth.originalFrame claim).N.Support
  | .inl position => supportAt (Birth.attacked claim) script safe position.val position.isLt.le
  | .inr original => networkAt (Birth.attacked claim) script safe script.length le_rfl ▸
      (finalFrame claim script).sourceSupport original

abbrev support (current : Cursor claim script) : (Birth.N claim).Support :=
  (oldSupport claim script safe current, some (debtAt claim script current))

set_option maxHeartbeats 600000 in
private theorem last_support (position : Fin script.length) (last : ¬ position.val + 1 < script.length) :
    supportAt (Birth.attacked claim) script safe (position.val + 1) position.isLt =
      oldSupport claim script safe (.inr (finalCut claim script).native.visit.current) := by
  have lastIndex : position.val + 1 = script.length := by omega
  have same : (⟨position.val + 1, Nat.lt_succ_of_le position.isLt⟩ : Fin (script.length + 1)) =
      ⟨script.length, Nat.lt_succ_self _⟩ := Fin.ext lastIndex
  exact congrArg (fun index : Fin (script.length + 1) =>
    supportAt (Birth.attacked claim) script safe index.val (Nat.le_of_lt_succ index.isLt)) same

set_option maxHeartbeats 600000 in
def oldWrite (current : Cursor claim script) :
    {whole : LedgerWriteEvolutionAt (Birth.originalFrame claim).N
      ⟨oldSupport claim script safe current⟩
      ⟨oldSupport claim script safe (nextCursor claim script current)⟩ //
        Financial.Installation.KeepsKeys whole} := by
  cases current with
  | inl position =>
    let original := originalWriteAt (Birth.attacked claim) script safe position
    let result := fun finish : (Birth.originalFrame claim).N.Support =>
      {whole : LedgerWriteEvolutionAt (Birth.originalFrame claim).N
        ⟨oldSupport claim script safe (.inl position)⟩ ⟨finish⟩ // Financial.Installation.KeepsKeys whole}
    by_cases later : position.val + 1 < script.length
    · have selected : nextCursor claim script (.inl position) = .inl ⟨position.val + 1, later⟩ :=
        dif_pos later
      exact cast (congrArg result (congrArg (oldSupport claim script safe) selected.symm)) original
    · have selected : nextCursor claim script (.inl position) = .inr (finalCut claim script).native.visit.current :=
        dif_neg later
      exact cast (congrArg result ((last_support claim script safe position later).trans
        (congrArg (oldSupport claim script safe) selected.symm))) original
  | inr original =>
    exact rebaseWrite (networkAt (Birth.attacked claim) script safe script.length le_rfl)
      (nativeWrite (finalFrame claim script) original)

def writes (current : Cursor claim script) : Bool :=
  let old := match current with
  | .inl position => (edgeAt (Birth.attacked claim) script safe position).writes
  | .inr original => hasWrite (finalFrame claim script) original
  old || match disposition claim script current with
  | .inl _ => true
  | .inr _ => false

private theorem cast_finite {old new : WorldRelationNetwork} (same : old = new) (s : old.Support)
    (finite : Finite (OpenResponsibilityAt old s)) :
    Finite (OpenResponsibilityAt new (same ▸ s)) := by
  cases same
  exact finite

private theorem finiteAt (current : Cursor claim script) :
    Finite (OpenResponsibilityAt (Birth.originalFrame claim).N (oldSupport claim script safe current)) := by
  cases current with
  | inl position =>
    let cut := cutAt (Birth.attacked claim) script position.val
    exact cast_finite (networkAt (Birth.attacked claim) script safe position.val position.isLt.le)
      (cutSupport cut) (cut.native.frame.entries_finite cut.native.visit.current)
  | inr original =>
    exact cast_finite (networkAt (Birth.attacked claim) script safe script.length le_rfl)
      _ ((finalFrame claim script).entries_finite original)

def joint (current : Cursor claim script) :
    {whole : LedgerWriteEvolutionAt (Birth.N claim)
      ⟨support claim script safe current⟩ ⟨support claim script safe (nextCursor claim script current)⟩ //
        InjectiveLedger whole} :=
  let old := oldWrite claim script safe current
  let basis := (Birth.originalFrame claim).family
  let owner := basis.entry (oldSupport claim script safe current)
  let conserved : InjectiveLedger old.val :=
    ⟨Financial.Installation.keys_imply_origin_injective _ old.property basis.open_fibres,
      Financial.Installation.keys_imply_destination_injective _ old.property basis.open_fibres⟩
  jointWrite ⟨old.val, conserved⟩ owner (disposition claim script current)

def flow : Accounting.Root.Compiler.Flow (Birth.N claim) where
  Current := Cursor claim script
  initial := positionAt claim script 0
  support := support claim script safe
  next := nextCursor claim script
  writes := writes claim script safe
  evolution := fun current => (joint claim script safe current).val
  finite := fun current => Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _
    (finiteAt claim script safe current)
  injective := fun current => (joint claim script safe current).property
  open_fibres := Birth.open_fibres claim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
