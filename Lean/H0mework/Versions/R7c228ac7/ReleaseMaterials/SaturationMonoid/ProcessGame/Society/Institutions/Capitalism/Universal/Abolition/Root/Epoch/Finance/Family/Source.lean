import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Lifecycle
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Movement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle ComplementObservation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

/-- The tags identify actual source epochs. Each fibre retains both the
old canonical claims and the original raw-micro claims and actor images. -/
abbrev Claim := (index : Index) × Finance.Claim (sources index) (depths index) (counts index)
abbrev Origin := (index : Index) × Finance.Origin (sources index) (depths index) (counts index)
abbrev Actor := (index : Index) × Interface.Actors.Image (sources index) (depths index) (counts index)
abbrev ActualItem := (index : Index) × Finance.ActualItem (sources index) (depths index) (counts index)
abbrev Balance := Party →₀ ℚ

def claimOrigin (claim : Claim sources depths counts) : Origin sources depths counts :=
  ⟨claim.1, claim.2.origin (sources claim.1) (depths claim.1) (counts claim.1)⟩

def claimActor (claim : Claim sources depths counts) : Actor sources depths counts :=
  ⟨claim.1, claim.2.debtorActor (sources claim.1) (depths claim.1) (counts claim.1)⟩

/-- A cross-epoch receipt is still an actual original instruction under its
own law. The old obligation's unit and rate are checked, never reset. -/
structure Review (claim : Claim sources depths counts) where
  private mk ::
  origin : ActualItem sources depths counts
  movement : Finance.Movement (sources origin.1) (depths origin.1) (counts origin.1) origin.2
  instrument : movement.instrument = claim.2.instrument (sources claim.1) (depths claim.1) (counts claim.1)
  debtor : movement.debtor = claim.2.debtor (sources claim.1) (depths claim.1) (counts claim.1)
  unit : (sources origin.1).law.settlementUnit movement.instrument =
    (sources claim.1).law.settlementUnit movement.instrument
  rate : (sources origin.1).law.settlementRate movement.instrument =
    (sources claim.1).law.settlementRate movement.instrument

def readReview (claim : Claim sources depths counts) (origin : ActualItem sources depths counts) :
    Option (Review sources depths counts claim) :=
  match Finance.readMovement (sources origin.1) (depths origin.1) (counts origin.1) origin.2 with
  | none => none
  | some movement =>
      if instrument : movement.instrument = claim.2.instrument (sources claim.1) (depths claim.1) (counts claim.1) then
        if debtor : movement.debtor = claim.2.debtor (sources claim.1) (depths claim.1) (counts claim.1) then
          if unit : (sources origin.1).law.settlementUnit movement.instrument =
              (sources claim.1).law.settlementUnit movement.instrument then
            if rate : (sources origin.1).law.settlementRate movement.instrument =
                (sources claim.1).law.settlementRate movement.instrument then
              some ⟨origin, movement, instrument, debtor, unit, rate⟩
            else none
          else none
        else none
      else none

def Review.after {claim : Claim sources depths counts} (review : Review sources depths counts claim)
    (before : Balance (Party := Party)) (cap : ℚ) : Balance (Party := Party) :=
  let used := min cap (before review.movement.sender)
  match review.movement.kind with
  | .payment => Financial.pay (sources claim.1) before review.movement.sender used
  | .assignment => Financial.assign (sources claim.1) before review.movement.sender review.movement.receiver used

theorem Review.quantity_nonnegative {claim : Claim sources depths counts}
    (review : Review sources depths counts claim) : 0 ≤ review.movement.quantity :=
  review.movement.quantity_nonnegative (sources review.origin.1) (depths review.origin.1) (counts review.origin.1)

#print axioms readReview

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
