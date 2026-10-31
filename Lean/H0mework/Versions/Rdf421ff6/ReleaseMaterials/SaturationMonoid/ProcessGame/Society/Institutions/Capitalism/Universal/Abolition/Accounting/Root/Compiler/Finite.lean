import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Law
import Mathlib.Data.Fintype.Sum

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

@[instance_reducible] def entryFintype (current : C) :
    Fintype (OpenResponsibilityAt (N) (supp current)) := by
  exact @Fintype.ofFinite _ (F.finite current)

abbrev RowSeed (current : C) :=
  OpenResponsibilityAt (N) (supp current) ⊕ OpenResponsibilityAt (N) (supp (advance current))

@[instance_reducible] private def rowFintype (current : C) :
    Fintype (RowSeed F current) := by
  letI := entryFintype F current
  letI := entryFintype F (advance current)
  exact inferInstance

def rowCount (current : C) :=
  @Fintype.card _ (rowFintype F current)

def rowEnum (current : C) :=
  @Fintype.equivFin _ (rowFintype F current)

def sourceRow (current : C) :
    RowSeed F current → OpenResponsibilityAt (N) (supp current)
  | .inl entry => entry
  | .inr entry => ((evolution current).origin entry).1

def targetRow (current : C) :
    RowSeed F current → OpenResponsibilityAt (N) (supp (advance current))
  | .inl entry => ((evolution current).destination entry).1
  | .inr entry => entry

def rowEvolution (current : C) (seed : RowSeed F current) :
    LedgerEntryEvolutionAt (N) (sourceRow F current seed)
      (targetRow F current seed) :=
  match seed with
  | .inl entry => ((evolution current).destination entry).2
  | .inr entry => ((evolution current).origin entry).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
