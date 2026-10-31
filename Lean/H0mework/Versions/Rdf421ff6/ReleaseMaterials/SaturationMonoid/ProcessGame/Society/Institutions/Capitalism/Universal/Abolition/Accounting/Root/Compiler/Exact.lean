import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {N : WorldRelationNetwork} (F : Flow N)



local notation "C" => F.Current
local notation "supp" => F.support
local notation "advance" => F.next
local notation "evolution" => F.evolution

local notation "src" => source F
local notation "emit" => emitted F
local notation "Seed" => RowSeed F
local notation "beforeRow" => sourceRow F
local notation "afterRow" => targetRow F
local notation "enumerate" => rowEnum F

local notation "wholePatch" => patch F

private theorem destination_selected (current : C) (entry : OpenResponsibilityAt (N) (supp current))
    (seed : Seed current) (selected : seed = .inl entry) (entry_eq : beforeRow current seed = entry) :
    (⟨afterRow current seed,
      Eq.mp (congrArg (fun before => LedgerEntryEvolutionAt (N) before (afterRow current seed)) entry_eq)
        (rowEvolution F current seed)⟩ :
      Σ targetEntry : OpenResponsibilityAt (N) (supp (advance current)), LedgerEntryEvolutionAt (N) entry targetEntry) =
      (evolution current).destination entry := by
  cases selected
  rfl

private theorem origin_selected (current : C) (entry : OpenResponsibilityAt (N) (supp (advance current)))
    (seed : Seed current) (selected : seed = .inr entry) (entry_eq : afterRow current seed = entry) :
    (⟨beforeRow current seed,
      Eq.mp (congrArg (fun after => LedgerEntryEvolutionAt (N) (beforeRow current seed) after) entry_eq)
        (rowEvolution F current seed)⟩ :
      Σ sourceEntry : OpenResponsibilityAt (N) (supp current), LedgerEntryEvolutionAt (N) sourceEntry entry) =
      (evolution current).origin entry := by
  cases selected
  rfl

theorem patch_destination (current : C) :
    (patch F current).toLedgerWriteEvolution.destination =
      (evolution current).destination := by
  funext entry
  exact destination_selected F current entry _
    ((enumerate current).symm_apply_apply (.inl entry))
    ((coverage F current).destination_sound entry)

theorem patch_origin (current : C) :
    (patch F current).toLedgerWriteEvolution.origin =
      (evolution current).origin := by
  funext entry
  exact origin_selected F current entry _
    ((enumerate current).symm_apply_apply (.inr entry))
    ((coverage F current).origin_sound entry)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
