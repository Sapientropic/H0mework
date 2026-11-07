import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (F : Flow N)

inductive Projection
  | ledger | current

def projectionLaw : SourceNativeProjectionLaw (ledgerSource F) where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .ledger => SourceNativeLedgerEvolutionAt (source F) occurrence
    | .current => F.Current
  project := fun projection {current} occurrence _ => match projection with
    | .ledger => (ledgerCompiler F).compile occurrence
    | .current => current

def authoritySource : SourceNativeAuthoritySource N (V F) where
  restructuringSource := restructuringSource F
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (restructuringSource F) (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic N
  projectionLaw := projectionLaw F

def livingRoot : SourceNativeLivingRootClosure N (V F) where
  source := {
    base := authoritySource F
    terminalHandoff := (authoritySource F).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted F
  compiler_commutes := by
    intro current
    change ((ledgerCompiler F).compile (emitted F current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

#print axioms livingRoot

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
