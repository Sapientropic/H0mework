import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open Capitalism.Universal.Abolition.Accounting.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (First identityWhole)

noncomputable section

variable {N : WorldRelationNetwork} (first : First N) (theory : TheoryState N)

private def authoritySource : SourceNativeAuthoritySource N (Compiler.V first.flow) :=
  { Compiler.authoritySource first.flow with lawSurface := theory }

/-- The operational theory belongs to the authority source before the
compiler emits either side of the whole-ledger first write. -/
def sourceWithTheory : SourceNativeLivingRootClosure N (Compiler.V first.flow) where
  source := ⟨authoritySource first theory, (authoritySource first theory).emptyFaithfulTerminalHandoff
    (fun _ => ⟨fun impossible => impossible.elim⟩)⟩
  emitted := Compiler.emitted first.flow
  compiler_commutes := (Compiler.livingRoot first.flow).compiler_commutes

theorem after_first_write_keeps_row (entry : OpenResponsibilityAt N first.after) :
    (Compiler.ledgerCompiler first.flow |>.compile (Compiler.emitted first.flow true)).entryDisposition entry =
      .evolved (.carried rfl HEq.rfl) := by
  let dispose (row : Σ target : OpenResponsibilityAt N first.after,
      LedgerEntryEvolutionAt N entry target) : LedgerEntryDispositionAt N entry := .evolved row.2
  exact congrArg dispose (congrFun (Compiler.patch_destination first.flow true) entry)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
