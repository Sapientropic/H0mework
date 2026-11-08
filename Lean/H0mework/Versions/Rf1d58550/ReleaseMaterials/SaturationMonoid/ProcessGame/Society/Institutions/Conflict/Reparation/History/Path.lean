import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next query endAt_append)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev cutAt (source : C) (script : Script) (position : Nat) :=
  endAt source (script.take position)

def NoFinancialBirths (source : C) (script : Script) : Prop :=
  ∀ position : Fin script.length,
    NoFinancialBirth (query (cutAt source script position.val) script[position.val])

theorem cutAt_step (source : C) (script : Script) (position : Fin script.length) :
    cutAt source script (position.val + 1) =
      next (cutAt source script position.val) script[position.val] := by
  simp only [cutAt, List.take_succ_eq_append_getElem position.isLt, endAt_append]
  rfl

def edgeAt (source : C) (script : Script) (safe : NoFinancialBirths source script)
    (position : Fin script.length) :
    NativeEdge (cutAt source script position.val) (cutAt source script (position.val + 1)) :=
  (cutAt_step source script position).symm ▸ originalEdge
    (cutAt source script position.val) script[position.val] (safe position)

theorem networkAt (source : C) (script : Script) (safe : NoFinancialBirths source script)
    (position : Nat) (bounded : position ≤ script.length) :
    (cutAt source script position).native.frame.N = source.native.frame.N := by
  induction position with
  | zero => rfl
  | succ position prior =>
    let step : Fin script.length := ⟨position, bounded⟩
    exact (edgeAt source script safe step).sameNetwork.trans (prior (Nat.le_of_lt bounded))

abbrev supportAt (source : C) (script : Script) (safe : NoFinancialBirths source script)
    (position : Nat) (bounded : position ≤ script.length) : source.native.frame.N.Support :=
  networkAt source script safe position bounded ▸ cutSupport (cutAt source script position)

def rebaseWrite {old new : WorldRelationNetwork} (same : old = new)
    {start finish : old.Support}
    (whole : {write : LedgerWriteEvolutionAt old ⟨start⟩ ⟨finish⟩ // Financial.Installation.KeepsKeys write}) :
    {write : LedgerWriteEvolutionAt new ⟨same ▸ start⟩ ⟨same ▸ finish⟩ // Financial.Installation.KeepsKeys write} := by
  cases same
  exact whole

theorem support_transport_trans {first middle last : WorldRelationNetwork}
    (one : first = middle) (two : middle = last) (support : first.Support) :
    two ▸ (one ▸ support) = one.trans two ▸ support := by
  cases one
  cases two
  rfl

def originalWriteAt (source : C) (script : Script) (safe : NoFinancialBirths source script)
    (position : Fin script.length) :
    {whole : LedgerWriteEvolutionAt source.native.frame.N
      ⟨supportAt source script safe position.val position.isLt.le⟩
      ⟨supportAt source script safe (position.val + 1) position.isLt⟩ //
        Financial.Installation.KeepsKeys whole} := by
  let actual := edgeAt source script safe position
  let prior := networkAt source script safe position.val position.isLt.le
  let after := networkAt source script safe (position.val + 1) position.isLt
  have same :
      prior ▸ (actual.sameNetwork ▸ cutSupport (cutAt source script (position.val + 1))) =
      after ▸ cutSupport (cutAt source script (position.val + 1)) :=
    support_transport_trans actual.sameNetwork prior _
  exact cast (congrArg (fun finish =>
    {whole : LedgerWriteEvolutionAt source.native.frame.N
      ⟨supportAt source script safe position.val position.isLt.le⟩ ⟨finish⟩ // Financial.Installation.KeepsKeys whole})
    same) (rebaseWrite prior ⟨actual.whole, actual.keys⟩)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
