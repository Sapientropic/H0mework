import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Law
import Mathlib.Data.Fintype.Sum

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

@[instance_reducible] def entryFintype (current : C) :
    Fintype (OpenResponsibilityAt (Born.N prior origin registered) (supp current)) := by
  exact @Fintype.ofFinite _ (entry_finite prior origin registered current)

abbrev RowSeed (current : C) :=
  OpenResponsibilityAt (Born.N prior origin registered) (supp current) ⊕ OpenResponsibilityAt (Born.N prior origin registered) (supp (advance current))

@[instance_reducible] private def rowFintype (current : C) :
    Fintype (RowSeed prior origin registered current) := by
  letI := entryFintype prior origin registered current
  letI := entryFintype prior origin registered (advance current)
  exact inferInstance

def rowCount (current : C) :=
  @Fintype.card _ (rowFintype prior origin registered current)

def rowEnum (current : C) :=
  @Fintype.equivFin _ (rowFintype prior origin registered current)

def sourceRow (current : C) :
    RowSeed prior origin registered current → OpenResponsibilityAt (Born.N prior origin registered) (supp current)
  | .inl entry => entry
  | .inr entry => ((evolution current).origin entry).1

def targetRow (current : C) :
    RowSeed prior origin registered current → OpenResponsibilityAt (Born.N prior origin registered) (supp (advance current))
  | .inl entry => ((evolution current).destination entry).1
  | .inr entry => entry

def rowEvolution (current : C) (seed : RowSeed prior origin registered current) :
    LedgerEntryEvolutionAt (Born.N prior origin registered) (sourceRow prior origin registered current seed)
      (targetRow prior origin registered current seed) :=
  match seed with
  | .inl entry => ((evolution current).destination entry).2
  | .inr entry => ((evolution current).origin entry).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
