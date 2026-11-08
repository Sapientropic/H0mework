import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth.Installation
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Conflict.Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)
  (repair : Request Party Good Port Technology Instrument)

abbrev atAttack := Birth.attacked claim
abbrev submit := queued (atAttack claim) repair
abbrev frame := Evolving.Epoch.Transition.fullFrame (submit claim repair)
abbrev start := (frame claim repair).root.toAuthoritativeRoot.toRoot.initialVisit.current

theorem original_paid_boundary (paid : Conflict.Root.Paid source (attack ++ [repair])) :
    Ready (atAttack claim) ∧ ReviewAvailable (atAttack claim) := by
  have continuation := Conflict.Root.trace_after_prefix source _ attack [repair] paid.trace
  exact continuation.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)

theorem recorded_body_starts_from_the_original_support :
    (frame claim repair).sourceSupport (start claim repair) =
      (Birth.originalFrame claim).sourceSupport (Birth.originalVisit claim).current := by
  exact Accounting.Quantifiers.Evolution.Factory.Direct.the_target_starts_with_the_same_whole_source_support
    (submit claim repair).native.full (submit claim repair).native.sourceActual
    (submit claim repair).executionReader

theorem original_support_survives_filing (paid : Conflict.Root.Paid source (attack ++ [repair])) :
    (Birth.originalFrame claim).sourceSupport
      ((Birth.originalFrame claim).successor (Birth.originalVisit claim).current).targetCurrent =
    (Birth.originalFrame claim).sourceSupport (Birth.originalVisit claim).current := by
  let native := (atAttack claim).native
  have ready := (original_paid_boundary claim repair paid).1
  have empty : Public.Accounting.item? native.input native.depth native.count native.prefixLimit
      native.renewalLimit native.oldPast native.start native.actual.actual = none := by
    cases candidate : Public.Accounting.item? native.input native.depth native.count native.prefixLimit
      native.renewalLimit native.oldPast native.start native.actual.actual with
    | none => rfl
    | some item => exact (ready (Or.inr (by rw [candidate]; rfl))).elim
  have hold : Public.Accounting.nativeNext native.input native.depth native.count native.prefixLimit
      native.renewalLimit native.oldPast native.start native.actual.actual = native.actual.actual := by
    rw [Public.Accounting.nativeNext, dif_pos native.bodyPaid, empty]
  have same := native.frame.cursor_next native.visit.current native.actual.actual native.actual.aligned
  rw [hold] at same
  exact (native.frame.support_exact _ _ same).trans
    (native.frame.support_exact _ _ native.actual.aligned).symm

def stage (paid : Conflict.Root.Paid source (attack ++ [repair])) : Birth.Stage source attack :=
  .filed [repair] paid

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment
