import H0mework.Versions.R2.Foundation.Authority.CausalEntry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace MotherNativeAuthority

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

abbrev EntryAt (root : SourceNativeLivingRootClosure N V) (current : V.Current) :=
  OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted current))

/-- Source-constructor operands at the full original living-root indices.
This is an assembly grammar; forming its admission rows is a separate source operation. -/
inductive Material (root : SourceNativeLivingRootClosure N V) :
    {current : V.Current} →
      (history : SourceNativeTemporalReachableAt root.toAuthoritativeRoot.toLedgerRoot current) →
      EntryAt root current → Type (u + 1)
  | initialAdmission
      (entry : EntryAt root root.toAuthoritativeRoot.toRoot.source.initial)
      (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (.finite root.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt entry) :
      Material root (.finite .initial) entry
  | cofinalAdmission
      {visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
      {entry : EntryAt root visit.current}
      (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (.cofinal visit)).GeneratedEntryRowAt entry) :
      Material root (.postCofinal (.cofinal visit)) entry
  | finiteSuccessor
      {current next : V.Current}
      {prior : root.toAuthoritativeRoot.toRoot.ReachableAt current}
      (next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? = some next)
      {entry : EntryAt root current}
      (material : Material root (.finite prior) entry) :
      Material root (.finite (.step prior next_eq))
        (root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext next_eq entry)
  | postCofinalSuccessor
      {current next : V.Current}
      {prior : SourceNativePostCofinalReachableAt root.toAuthoritativeRoot.toLedgerRoot current}
      (next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? = some next)
      {entry : EntryAt root current}
      (material : Material root (.postCofinal prior) entry) :
      Material root (.postCofinal (.step prior next_eq))
        (root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext next_eq entry)

variable {root : SourceNativeLivingRootClosure N V}

/-- Only the original public full-authority introductions assemble these operands. -/
def assemble :
    {current : V.Current} →
    {history : SourceNativeTemporalReachableAt root.toAuthoritativeRoot.toLedgerRoot current} →
    {entry : EntryAt root current} → Material root history entry →
      SourceNativeLivingTemporalCausalEntryAuthorityAt root ⟨current, history⟩ entry
  | _, _, _, .initialAdmission entry row =>
      .generatedFromInitialRow root entry row
  | _, _, _, @Material.cofinalAdmission _ _ _ visit entry row =>
      .generatedFromCofinalRow root visit entry row
  | _, _, _, .finiteSuccessor next_eq prior => (assemble prior).next next_eq
  | _, _, _, .postCofinalSuccessor next_eq prior => (assemble prior).next next_eq

/-- Eliminate a full original authority, retaining its exact Type-valued value.
No erased ledger readout is an input to this eliminator or to assembly. -/
noncomputable def decompose
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : EntryAt root visit.current}
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry) :
    {material : Material root visit.history entry // assemble material = authority} := by
  rcases visit with ⟨current, history⟩
  rcases authority with ⟨authoritative⟩
  rcases authoritative with ⟨ledgerHistory⟩
  dsimp only [SourceNativeTemporalCausalEntryLedgerReadoutAt] at ledgerHistory ⊢
  induction ledgerHistory with
  | initialAdmission entry row => exact ⟨.initialAdmission entry row, rfl⟩
  | cofinalAdmission row => exact ⟨.cofinalAdmission row, rfl⟩
  | finiteSuccessor next_eq prior ih =>
      rcases ih with ⟨material, recovered⟩
      exact ⟨.finiteSuccessor next_eq material,
        congrArg (fun original => original.next next_eq) recovered⟩
  | postCofinalSuccessor next_eq prior ih =>
      rcases ih with ⟨material, recovered⟩
      exact ⟨.postCofinalSuccessor next_eq material,
        congrArg (fun original => original.next next_eq) recovered⟩

abbrev AuthorityTotal (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :=
  Σ entry : EntryAt root visit.current,
    SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry

abbrev MaterialTotal (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :=
  Σ entry : EntryAt root visit.current, Material root visit.history entry

def assembleTotal {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (material : MaterialTotal root visit) : AuthorityTotal root visit :=
  ⟨material.1, assemble material.2⟩

noncomputable def decomposeTotal {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (authority : AuthorityTotal root visit) : MaterialTotal root visit :=
  ⟨authority.1, (decompose authority.2).val⟩

theorem assemble_decomposeTotal
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (authority : AuthorityTotal root visit) :
    assembleTotal (decomposeTotal authority) = authority := by
  rcases authority with ⟨entry, authority⟩
  exact congrArg (Sigma.mk entry) (decompose authority).property

end MotherNativeAuthority
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
