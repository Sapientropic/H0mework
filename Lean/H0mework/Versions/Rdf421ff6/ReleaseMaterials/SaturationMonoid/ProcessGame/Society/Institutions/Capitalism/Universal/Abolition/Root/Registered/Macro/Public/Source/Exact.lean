import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Rows

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

local notation "wholePatch" => patch input depth count prefixLimit renewalLimit oldPast start family

private theorem destination_selected (current : C) (entry : OpenResponsibilityAt world (supp current))
    (seed : Seed current) (selected : seed = .inl entry) (entry_eq : beforeRow current seed = entry) :
    (⟨afterRow current seed,
      Eq.mp (congrArg (fun before => LedgerEntryEvolutionAt world before (afterRow current seed)) entry_eq)
        (rowEvolution input depth count prefixLimit renewalLimit oldPast start family current seed)⟩ :
      Σ targetEntry : OpenResponsibilityAt world (supp (advance current)), LedgerEntryEvolutionAt world entry targetEntry) =
      (evolution current).destination entry := by
  cases selected
  rfl

private theorem origin_selected (current : C) (entry : OpenResponsibilityAt world (supp (advance current)))
    (seed : Seed current) (selected : seed = .inr entry) (entry_eq : afterRow current seed = entry) :
    (⟨beforeRow current seed,
      Eq.mp (congrArg (fun after => LedgerEntryEvolutionAt world (beforeRow current seed) after) entry_eq)
        (rowEvolution input depth count prefixLimit renewalLimit oldPast start family current seed)⟩ :
      Σ sourceEntry : OpenResponsibilityAt world (supp current), LedgerEntryEvolutionAt world sourceEntry entry) =
      (evolution current).origin entry := by
  cases selected
  rfl

theorem patch_destination (current : C) :
    (patch input depth count prefixLimit renewalLimit oldPast start family current).toLedgerWriteEvolution.destination =
      (evolution current).destination := by
  funext entry
  exact destination_selected input depth count prefixLimit renewalLimit oldPast start family current entry _
    ((enumerate current).symm_apply_apply (.inl entry))
    ((coverage input depth count prefixLimit renewalLimit oldPast start family current).destination_sound entry)

theorem patch_origin (current : C) :
    (patch input depth count prefixLimit renewalLimit oldPast start family current).toLedgerWriteEvolution.origin =
      (evolution current).origin := by
  funext entry
  exact origin_selected input depth count prefixLimit renewalLimit oldPast start family current entry _
    ((enumerate current).symm_apply_apply (.inr entry))
    ((coverage input depth count prefixLimit renewalLimit oldPast start family current).origin_sound entry)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
