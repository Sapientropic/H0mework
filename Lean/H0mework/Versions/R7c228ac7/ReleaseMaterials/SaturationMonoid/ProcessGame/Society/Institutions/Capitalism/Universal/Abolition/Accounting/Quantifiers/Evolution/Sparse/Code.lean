import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Fibre

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

private structure WholeTransport (N : WorldRelationNetwork) (source target : CompleteLiveLedgerAt N) where
  evolution : LedgerWriteEvolutionAt N source target
  inverse_origin : ∀ entry,(evolution.destination (evolution.origin entry).1).1 = entry
  inverse_destination : ∀ entry,(evolution.origin (evolution.destination entry).1).1 = entry
  keys : Financial.Installation.KeepsKeys evolution

private def castTarget {N : WorldRelationNetwork} {source middle target : CompleteLiveLedgerAt N}
    (same : middle = target) (transport : WholeTransport N source middle) :
    WholeTransport N source target := same ▸ transport

private def identityTransport {N : WorldRelationNetwork} (ledger : CompleteLiveLedgerAt N) : WholeTransport N ledger ledger where
  evolution := LedgerWriteEvolutionAt.identity ledger
  inverse_origin := fun _ => rfl
  inverse_destination := fun _ => rfl
  keys := ⟨fun _ => rfl,fun _ => rfl⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "N" => DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)

private def nativeTransport : WholeTransport N ⟨support claim current word false⟩ ⟨support claim current word true⟩ where
  evolution := actualEvolution claim current word
  inverse_origin := actual_inverse_origin claim current word
  inverse_destination := actual_inverse_destination claim current word
  keys := actual_keeps_every_original_key claim current word

private def initialTransport (origin : Fibre.Origin claim current) : WholeTransport N
    ⟨Fibre.supportAt claim current word false origin⟩ ⟨Fibre.supportAt claim current word true origin⟩ := by
  classical
  if selected : origin = current.root.emitted current.visit.current then
    subst origin
    exact castTarget (congrArg CompleteLiveLedgerAt.mk (Fibre.emitted_support claim current word true).symm)
      (nativeTransport claim current word)
  else
    exact castTarget (congrArg CompleteLiveLedgerAt.mk (Fibre.unselected_support claim current word origin selected).symm)
      (identityTransport _)

private def transport : (phase : Bool) → (origin : Fibre.Origin claim current) → WholeTransport N
    ⟨Fibre.supportAt claim current word phase origin⟩ ⟨Fibre.supportAt claim current word true origin⟩
  | false,origin => initialTransport claim current word origin
  | true,_ => identityTransport _

def fibreEvolution (phase : Bool) (origin : Fibre.Origin claim current) :=
  (transport claim current word phase origin).evolution

def code : Compiler.Code N where
  Current := Bool
  Fibre := Fibre.Origin claim current
  emission := current.root.emitted current.visit.current
  initial := false
  supportAt := Fibre.supportAt claim current word
  anchor_coherent := Fibre.anchor_coherent claim current word
  incidence_coherent := Fibre.incidence_coherent claim current word
  lineage_coherent := Fibre.lineage_coherent claim current word
  next := fun _ => true
  writes := fun phase => !phase
  evolution := fibreEvolution claim current word
  inverse_origin := fun phase origin => (transport claim current word phase origin).inverse_origin
  inverse_destination := fun phase origin => (transport claim current word phase origin).inverse_destination

theorem code_keeps_every_original_key :
    Financial.Installation.KeepsKeys ((code claim current word).evolution false (code claim current word).emission) :=
  (transport claim current word false (current.root.emitted current.visit.current)).keys

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
