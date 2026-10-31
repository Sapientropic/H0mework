import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)


local notation "C" => State origin registered
local notation "supp" => supportAt prior origin registered
local notation "advance" => next origin registered
local notation "evolution" => wholeEvolution prior origin registered

local notation "src" => source prior origin registered
local notation "emit" => emitted prior origin registered
local notation "Seed" => RowSeed prior origin registered
local notation "beforeRow" => sourceRow prior origin registered
local notation "afterRow" => targetRow prior origin registered
local notation "enumerate" => rowEnum prior origin registered

local notation "wholePatch" => patch prior origin registered

private theorem destination_selected (current : C) (entry : OpenResponsibilityAt (Born.N prior origin registered) (supp current))
    (seed : Seed current) (selected : seed = .inl entry) (entry_eq : beforeRow current seed = entry) :
    (⟨afterRow current seed,
      Eq.mp (congrArg (fun before => LedgerEntryEvolutionAt (Born.N prior origin registered) before (afterRow current seed)) entry_eq)
        (rowEvolution prior origin registered current seed)⟩ :
      Σ targetEntry : OpenResponsibilityAt (Born.N prior origin registered) (supp (advance current)), LedgerEntryEvolutionAt (Born.N prior origin registered) entry targetEntry) =
      (evolution current).destination entry := by
  cases selected
  rfl

private theorem origin_selected (current : C) (entry : OpenResponsibilityAt (Born.N prior origin registered) (supp (advance current)))
    (seed : Seed current) (selected : seed = .inr entry) (entry_eq : afterRow current seed = entry) :
    (⟨beforeRow current seed,
      Eq.mp (congrArg (fun after => LedgerEntryEvolutionAt (Born.N prior origin registered) (beforeRow current seed) after) entry_eq)
        (rowEvolution prior origin registered current seed)⟩ :
      Σ sourceEntry : OpenResponsibilityAt (Born.N prior origin registered) (supp current), LedgerEntryEvolutionAt (Born.N prior origin registered) sourceEntry entry) =
      (evolution current).origin entry := by
  cases selected
  rfl

theorem patch_destination (current : C) :
    (patch prior origin registered current).toLedgerWriteEvolution.destination =
      (evolution current).destination := by
  funext entry
  exact destination_selected prior origin registered current entry _
    ((enumerate current).symm_apply_apply (.inl entry))
    ((coverage prior origin registered current).destination_sound entry)

theorem patch_origin (current : C) :
    (patch prior origin registered current).toLedgerWriteEvolution.origin =
      (evolution current).origin := by
  funext entry
  exact origin_selected prior origin registered current entry _
    ((enumerate current).symm_apply_apply (.inr entry))
    ((coverage prior origin registered current).origin_sound entry)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
