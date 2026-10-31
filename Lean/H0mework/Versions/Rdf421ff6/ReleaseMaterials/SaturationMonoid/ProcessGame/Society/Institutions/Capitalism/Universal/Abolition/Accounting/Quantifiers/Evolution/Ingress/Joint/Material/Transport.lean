import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Context

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def support (base : (Background.world seed).Support) (current : Current seed claim) :
    (Admission.N seed claim).Support := ((base,some (.current current)),some current)

variable {before after : (Background.world seed).Support}
  (financial : LedgerWriteEvolutionAt (Background.world seed) ⟨before⟩ ⟨after⟩)
  (owner : OpenResponsibilityAt (Background.world seed) before)
  (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)

def productiveTransport : LedgerWriteEvolutionAt (Rebase.NewN seed claim)
    ⟨before,some (.current current)⟩ ⟨after,some (.current (Current.advance seed claim current word))⟩ :=
  Financial.Installation.wholeTransport financial owner (Productive.actual seed claim current word)

/-- Lift the one original financial evolution through both material rows.
Both projections use the same computed successor, never per-row endpoints. -/
def wholeTransport : LedgerWriteEvolutionAt (Admission.N seed claim)
    ⟨support seed claim before current⟩ ⟨support seed claim after (Current.advance seed claim current word)⟩ :=
  Financial.Installation.wholeTransport (productiveTransport seed claim financial owner current word)
    (oldEntry (law := Productive.law seed claim) (state? := some (.current current)) owner)
    (Gross.actual seed claim current word)

theorem the_whole_transport_retains_all_original_keys
    (keys : Financial.Installation.KeepsKeys financial) :
    Financial.Installation.KeepsKeys (wholeTransport seed claim financial owner current word) :=
  Financial.Installation.wholeTransport_keeps_keys
    (productiveTransport seed claim financial owner current word)
    (oldEntry (law := Productive.law seed claim) (state? := some (.current current)) owner)
    (Gross.actual seed claim current word)
    (Financial.Installation.wholeTransport_keeps_keys financial owner
      (Productive.actual seed claim current word) keys)

omit word in
def identityTransport : LedgerWriteEvolutionAt (Admission.N seed claim)
    ⟨support seed claim before current⟩ ⟨support seed claim after current⟩ :=
  Financial.Installation.wholeTransport
    (Financial.Installation.wholeTransport financial owner (Productive.Transport.identity (.current current)))
    (oldEntry (law := Productive.law seed claim) (state? := some (.current current)) owner)
    (Gross.Carry.identity current)

omit word in
theorem identityTransport_keeps_keys (keys : Financial.Installation.KeepsKeys financial) :
    Financial.Installation.KeepsKeys (identityTransport seed claim financial owner current) :=
  Financial.Installation.wholeTransport_keeps_keys (law := Gross.law seed claim) _ _ (Gross.Carry.identity current)
    (Financial.Installation.wholeTransport_keeps_keys (law := Productive.law seed claim) financial owner
      (Productive.Transport.identity (.current current)) keys)

theorem the_same_actual_successor_is_in_both_material_rows :
    (support seed claim after (Current.advance seed claim current word)).1.2 =
        some (.current (Current.advance seed claim current word)) ∧
      (support seed claim after (Current.advance seed claim current word)).2 =
        some (Current.advance seed claim current word) := ⟨rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material
