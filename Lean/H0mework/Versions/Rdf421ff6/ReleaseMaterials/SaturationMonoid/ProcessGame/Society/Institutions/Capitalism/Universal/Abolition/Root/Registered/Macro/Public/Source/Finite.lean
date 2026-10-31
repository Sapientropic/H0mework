import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Law
import Mathlib.Data.Fintype.Sum

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

@[instance_reducible] def entryFintype (current : C) :
    Fintype (OpenResponsibilityAt world (supp current)) := by
  exact @Fintype.ofFinite _ (family.entries_finite current.account current.native)

abbrev RowSeed (current : C) :=
  OpenResponsibilityAt world (supp current) ⊕ OpenResponsibilityAt world (supp (advance current))

@[instance_reducible] private def rowFintype (current : C) :
    Fintype (RowSeed input depth count prefixLimit renewalLimit oldPast start family current) := by
  letI := entryFintype input depth count family current
  letI := entryFintype input depth count family (advance current)
  exact inferInstance

def rowCount (current : C) :=
  @Fintype.card _ (rowFintype input depth count prefixLimit renewalLimit oldPast start family current)

def rowEnum (current : C) :=
  @Fintype.equivFin _ (rowFintype input depth count prefixLimit renewalLimit oldPast start family current)

def sourceRow (current : C) :
    RowSeed input depth count prefixLimit renewalLimit oldPast start family current → OpenResponsibilityAt world (supp current)
  | .inl entry => entry
  | .inr entry => ((evolution current).origin entry).1

def targetRow (current : C) :
    RowSeed input depth count prefixLimit renewalLimit oldPast start family current → OpenResponsibilityAt world (supp (advance current))
  | .inl entry => ((evolution current).destination entry).1
  | .inr entry => entry

def rowEvolution (current : C) (seed : RowSeed input depth count prefixLimit renewalLimit oldPast start family current) :
    LedgerEntryEvolutionAt world (sourceRow input depth count prefixLimit renewalLimit oldPast start family current seed)
      (targetRow input depth count prefixLimit renewalLimit oldPast start family current seed) :=
  match seed with
  | .inl entry => ((evolution current).destination entry).2
  | .inr entry => ((evolution current).origin entry).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
