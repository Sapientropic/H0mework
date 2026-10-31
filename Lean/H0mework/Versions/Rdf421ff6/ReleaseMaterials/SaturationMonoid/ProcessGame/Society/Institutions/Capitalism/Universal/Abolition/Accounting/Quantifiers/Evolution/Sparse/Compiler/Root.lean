import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootGeneratedProofRelevantRestructuring

noncomputable section

variable {N : WorldRelationNetwork} (code : Code N)

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source code) :=
  RootGeneratedProofRelevantRestructuring.law N (code.support code.initial) (source code)

def restructuringCertification {current : code.Current}
    (occurrence : (source code).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw code) ((ledgerCompiler code).compile occurrence) := by
  rcases occurrence with ⟨oldSupport,event⟩
  cases event with
  | emitted origin =>
    dsimp only [ledgerCompiler,sourcePacket]
    split <;> apply ExactLedgerRestructuringCertificationAt.ofInjective
    all_goals rw [patch_is_the_complete_original_transport]
    · intro left right same
      rw [← code.inverse_origin current origin left,← code.inverse_origin current origin right]
      exact congrArg (fun entry => ((code.evolution current origin).destination entry).1) same
    · intro left right same
      rw [← code.inverse_destination current origin left,← code.inverse_destination current origin right]
      exact congrArg (fun entry => ((code.evolution current origin).origin entry).1) same
    · intro left right same
      rw [← code.inverse_origin current origin left,← code.inverse_origin current origin right]
      exact congrArg (fun entry => ((code.evolution current origin).destination entry).1) same
    · intro left right same
      rw [← code.inverse_destination current origin left,← code.inverse_destination current origin right]
      exact congrArg (fun entry => ((code.evolution current origin).origin entry).1) same

def restructuringSource : SourceNativeRestructuringLedgerSource N (V code) where
  source := source code
  compiler := { ledgerCompiler := ledgerCompiler code
                restructuringLaw := restructuringLaw code
                certifyRestructuring := restructuringCertification code }

def projectionLaw : SourceNativeProjectionLaw (ledgerSource code) where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => code.Current
  project := fun _ {current} _ _ => current

def authoritySource : SourceNativeAuthoritySource N (V code) where
  restructuringSource := restructuringSource code
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource code) (fun _ => ⟨fun impossible => nomatch impossible⟩)
  lawSurface := TheoryState.rootSemantic N
  projectionLaw := projectionLaw code

def livingRoot : SourceNativeLivingRootClosure N (V code) where
  source := { base := authoritySource code
              terminalHandoff := (authoritySource code).emptyFaithfulTerminalHandoff (fun _ => ⟨fun impossible => nomatch impossible⟩) }
  emitted := emitted code
  compiler_commutes := (ledgerRoot code).compiler_commutes

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
