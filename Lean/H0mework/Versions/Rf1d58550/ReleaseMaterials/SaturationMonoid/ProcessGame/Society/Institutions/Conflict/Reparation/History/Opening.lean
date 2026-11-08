import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Flow
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

theorem original_attack_is_ready :
    ¬ Public.Inquiry.HasWork (Birth.attacked claim).native.frame (Birth.attacked claim).native.actual.actual :=
  claim.paid.whole.finished

theorem filing_preserves_the_original_ready_support :
    (Birth.originalFrame claim).sourceSupport
      ((Birth.originalFrame claim).successor (Birth.originalVisit claim).current).targetCurrent =
    cutSupport (Birth.attacked claim) := by
  let native := (Birth.attacked claim).native
  have empty : Public.Accounting.item? native.input native.depth native.count native.prefixLimit
      native.renewalLimit native.oldPast native.start native.actual.actual = none := by
    cases item : Public.Accounting.item? native.input native.depth native.count native.prefixLimit
      native.renewalLimit native.oldPast native.start native.actual.actual with
    | none => rfl
    | some _ => exact (original_attack_is_ready claim (Or.inr (by rw [item]; rfl))).elim
  have hold : Public.Accounting.nativeNext native.input native.depth native.count native.prefixLimit
      native.renewalLimit native.oldPast native.start native.actual.actual = native.actual.actual := by
    rw [Public.Accounting.nativeNext, dif_pos native.bodyPaid, empty]
  have same := native.frame.cursor_next native.visit.current native.actual.actual native.actual.aligned
  rw [hold] at same
  exact (native.frame.support_exact _ _ same).trans
    (native.frame.support_exact _ _ native.actual.aligned).symm

abbrev filed := (Birth.generated claim).target
abbrev filedVisit := (filed claim).targetVisit
abbrev filedOwner := (filed claim).targetRoot.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
  (filed claim).firstSuccessor.next_eq (filed claim).bornEntry

abbrev filedAuthority := (filed claim).bornAuthority.next (filed claim).firstSuccessor.next_eq

theorem initial_is_the_actual_filed_support
    (script : Script) (safe : NoFinancialBirths (Birth.attacked claim) script) (nonempty : 0 < script.length) :
    (flow claim script safe).support (flow claim script safe).initial =
      (filed claim).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt (filedVisit claim).current := by
  have aligned : (filedVisit claim).current = Birth.next claim .pending :=
    Capitalism.Universal.Abolition.Accounting.Root.Compiler.successor_current (Birth.flow claim) .pending
  change support claim script safe (positionAt claim script 0) = Birth.support claim (filedVisit claim).current
  rw [aligned, positionAt, dif_pos nonempty]
  change (cutSupport (Birth.attacked claim), some (Birth.opening claim)) =
    ((Birth.originalFrame claim).sourceSupport
      ((Birth.originalFrame claim).successor (Birth.originalVisit claim).current).targetCurrent,
        some (Birth.opening claim))
  exact congrArg (fun stock => (stock, some (Birth.opening claim)))
    (filing_preserves_the_original_ready_support claim).symm

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
