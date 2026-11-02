import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Joint
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Authority

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

structure Bound where
  base : RawLaw Party Good Port Technology Instrument
  scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)
  source : Machine Party Good Port (Mandate.State Party Technology) Instrument
  law_exact : source.code.law = Mandate.law base scope
  task_exact : source.code.task = scope.task

variable (bound : Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

abbrev currentAt (depth : Nat) := (bound.source.actualExecution depth).before
abbrev wordAt (depth : Nat) := (bound.source.actualExecution depth).submitted

structure TracedGrant (birth last : Nat) where
  private mk ::
  admission : Mandate.AdmittedGrant bound.base bound.scope (currentAt bound birth) (wordAt bound birth)
  continuation : Mandate.Lifecycle.Observed.History bound.base bound.scope (currentAt bound) (wordAt bound) birth admission.grant
  exact : continuation = Mandate.Lifecycle.Observed.through last

def traceGrant (birth last : Nat)
    (grant : Mandate.Grant bound.base bound.scope (currentAt bound birth) (wordAt bound birth)) : TracedGrant bound birth last :=
  ⟨Mandate.admitGrant bound.base bound.scope _ _ grant, Mandate.Lifecycle.Observed.through last, rfl⟩

def recordsAt (last : Nat) : List (Sigma fun birth : Fin (last + 1) => TracedGrant bound birth.val last) :=
  (List.finRange (last + 1)).flatMap fun birth =>
    (Mandate.grantsAt bound.base bound.scope (currentAt bound birth.val) (wordAt bound birth.val)).map fun grant =>
      ⟨birth, traceGrant bound birth.val last grant⟩

structure Disposition (depth : Nat) where
  private mk ::
  joint : Native.Disposition bound.source depth
  joint_exact : joint = Native.generate bound.source depth
  mandates : List (Sigma fun birth : Fin (depth + 1) => TracedGrant bound birth.val depth)
  mandates_exact : mandates = recordsAt bound depth

def generate (depth : Nat) : Disposition bound depth :=
  ⟨Native.generate bound.source depth, rfl, recordsAt bound depth, rfl⟩

theorem every_actual_grant_is_admitted (last : Nat) (birth : Fin (last + 1))
    (grant : Mandate.Grant bound.base bound.scope (currentAt bound birth.val) (wordAt bound birth.val))
    (actual : grant ∈ Mandate.grantsAt bound.base bound.scope (currentAt bound birth.val) (wordAt bound birth.val)) :
    (⟨birth, traceGrant bound birth.val last grant⟩ : Sigma fun birth : Fin (last + 1) => TracedGrant bound birth.val last) ∈
      (generate bound last).mandates := by
  apply List.mem_flatMap.mpr
  exact ⟨birth, List.mem_finRange _, List.mem_map.mpr ⟨grant, actual, rfl⟩⟩

theorem each_grant_retains_its_original_native_responsibility (birth last : Nat) (record : TracedGrant bound birth last) :
    record.continuation.state.LiveAt 0 ∧
      HEq record.continuation.obligation.admission
        (Mandate.Lifecycle.original bound.base bound.scope (currentAt bound) (wordAt bound) birth record.admission.grant).admission :=
  ⟨record.continuation.responsibility_remains_live, record.continuation.original_admission⟩

theorem actual_law_generates_the_same_mandate_items (depth : Nat) :
    (Mandate.law bound.base bound.scope).rawItems (currentAt bound depth) (wordAt bound depth) =
      bound.source.code.law.rawItems (bound.source.actualExecution depth).before (bound.source.actualExecution depth).submitted := by
  rw [bound.law_exact]

theorem old_grant_continues_on_the_next_actual_word (birth last : Nat)
    (grant : Mandate.Grant bound.base bound.scope (currentAt bound birth) (wordAt bound birth)) :
    (traceGrant bound birth (last + 1) grant).continuation =
      (traceGrant bound birth last grant).continuation.visit (last + 1) :=
  (Mandate.Lifecycle.Observed.through_succ last).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Authority
