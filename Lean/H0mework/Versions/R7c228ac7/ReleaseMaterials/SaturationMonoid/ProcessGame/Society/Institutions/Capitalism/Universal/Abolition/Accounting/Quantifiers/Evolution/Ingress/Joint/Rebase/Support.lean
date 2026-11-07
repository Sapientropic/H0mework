import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Family
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Productive.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation
open Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

abbrev OldN := ExtendedNetwork (Background.original seed).native.N (Productive.oldLaw seed)
abbrev NewN := ExtendedNetwork (Background.world seed) (Productive.law seed grossClaim)

def supportForward (support : (OldN seed).Support) : (NewN seed grossClaim).Support :=
  ((Background.translation seed).support.forward support.1,support.2.map Productive.State.legacy)

def supportBackward (support : (NewN seed grossClaim).Support) : (OldN seed).Support :=
  ((Background.translation seed).support.backward support.1,support.2.map (Productive.backward seed grossClaim))

def supportRetract : ConstructiveRetract (OldN seed).Support (NewN seed grossClaim).Support where
  forward := supportForward seed grossClaim
  backward := supportBackward seed grossClaim
  backward_forward := by
    rintro ⟨support,state⟩
    apply Prod.ext
    · exact (Background.translation seed).support.backward_forward support
    · cases state <;> rfl

def oldSupport := Abolition.Accounting.Root.Reentry.Frame.support seed.claim seed.current

def mappedSupport := supportForward seed grossClaim (oldSupport seed)

def enteredSupport : (NewN seed grossClaim).Support :=
  ((Background.family seed).currentSupport,some (.current (Current.initial seed grossClaim)))

theorem entering_uses_the_original_live_material_cursor :
    (Current.initial seed grossClaim).raw =
      (Abolition.Accounting.Root.Reentry.Frame.state seed.claim seed.current).raw := rfl

theorem entering_cannot_reset_any_original_productive_quantity :
    (Current.initial seed grossClaim).productive =
      (Abolition.Accounting.Root.Reentry.Frame.state seed.claim seed.current).remaining := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
