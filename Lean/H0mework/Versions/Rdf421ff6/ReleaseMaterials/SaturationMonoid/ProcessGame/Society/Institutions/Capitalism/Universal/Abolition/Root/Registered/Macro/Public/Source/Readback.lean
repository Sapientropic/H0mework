import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Successor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

local notation "C" => Accounting.Current input depth count anchor
local notation "supp" => Accounting.support input depth count family
local notation "advance" => Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start
local notation "evolution" => Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start family

local notation "src" => source input depth count prefixLimit renewalLimit oldPast start family
local notation "emit" => emitted input depth count prefixLimit renewalLimit oldPast start family
local notation "Seed" => RowSeed input depth count prefixLimit renewalLimit oldPast start family
local notation "beforeRow" => sourceRow input depth count prefixLimit renewalLimit oldPast start family
local notation "afterRow" => targetRow input depth count prefixLimit renewalLimit oldPast start family
local notation "enumerate" => rowEnum input depth count prefixLimit renewalLimit oldPast start family

local notation "V₀" => V input depth count prefixLimit renewalLimit oldPast start family
local notation "rawRows" => RawRowAt input depth count prefixLimit renewalLimit oldPast start family
local notation "rowCompiler" => rowSource input depth count prefixLimit renewalLimit oldPast start family
local notation "wholePatch" => patch input depth count prefixLimit renewalLimit oldPast start family
local notation "sourceWrites" => writes input depth count prefixLimit renewalLimit oldPast start

local notation "lc" => ledgerCompiler input depth count prefixLimit renewalLimit oldPast start family
local notation "lsrc" => ledgerSource input depth count prefixLimit renewalLimit oldPast start family

local notation "root" => livingRoot input depth count prefixLimit renewalLimit oldPast start family

private def ReadbackAt (current : C) (image : SourceNativeLedgerEvolutionAt src (emit current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emit current) image,
    actual.targetOccurrence.1 = supp (advance current) ∧
      HEq actual.ledgerEvolution.destination (evolution current).destination ∧
      HEq actual.ledgerEvolution.origin (evolution current).origin

private theorem readback (current : C) :
    ReadbackAt input depth count prefixLimit renewalLimit oldPast start family current ((lc).compile (emit current)) := by
  dsimp only [ledgerCompiler, sourcePacket]
  split <;> intro actual <;>
    exact ⟨rfl, heq_of_eq (patch_destination input depth count prefixLimit renewalLimit oldPast start family current),
      heq_of_eq (patch_origin input depth count prefixLimit renewalLimit oldPast start family current)⟩

theorem successor_support (current : C) :
    (successor input depth count prefixLimit renewalLimit oldPast start family current).targetOccurrence.1 =
      Accounting.support input depth count family (Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start current) :=
  (readback input depth count prefixLimit renewalLimit oldPast start family current _).1

theorem successor_destination_heq (current : C) :
    HEq (successor input depth count prefixLimit renewalLimit oldPast start family current).ledgerEvolution.destination
      (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start family current).destination :=
  (readback input depth count prefixLimit renewalLimit oldPast start family current _).2.1

theorem successor_origin_heq (current : C) :
    HEq (successor input depth count prefixLimit renewalLimit oldPast start family current).ledgerEvolution.origin
      (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start family current).origin :=
  (readback input depth count prefixLimit renewalLimit oldPast start family current _).2.2

#print axioms successor_support
#print axioms successor_destination_heq
#print axioms successor_origin_heq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
