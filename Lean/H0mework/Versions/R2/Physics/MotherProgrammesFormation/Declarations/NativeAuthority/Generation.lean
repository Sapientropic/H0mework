import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.Admissions
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.Cofinal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace MotherNativeAuthority

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

noncomputable section

/-- This entry fibre is fixed by the source emitter before any cofinal visit is formed. -/
def CofinalEntry (root : SourceNativeLivingRootClosure N V) : Type u :=
  match V.cofinal.emit? with
  | none => PEmpty
  | some event => EntryAt root (V.cofinal.target event)

private theorem cofinalEntryType (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :
    CofinalEntry root = EntryAt root visit.current := by
  unfold CofinalEntry
  rw [visit.emitted_eq_event]
  rfl

def cofinalEntryAt (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (input : CofinalEntry root) : EntryAt root visit.current :=
  cast (cofinalEntryType root visit) input

private def cofinalInput (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : EntryAt root visit.current) : CofinalEntry root :=
  cast (cofinalEntryType root visit).symm entry

private theorem cofinalInput_recovers (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : EntryAt root visit.current) :
    cofinalEntryAt root visit (cofinalInput root visit entry) = entry := by
  unfold cofinalEntryAt cofinalInput
  exact (cast_cast _ _ entry).trans (cast_eq _ entry)

/-- Only original entry material is supplied. Rows, visits and successors are generated internally. -/
inductive Seed (root : SourceNativeLivingRootClosure N V) : Type u
  | initial (entry : EntryAt root root.toAuthoritativeRoot.toRoot.source.initial)
  | cofinal (entry : CofinalEntry root)

abbrev MaterialState (root : SourceNativeLivingRootClosure N V) :=
  Σ visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot,
    MaterialTotal root visit

private def atVisit {root : SourceNativeLivingRootClosure N V}
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (material : MaterialTotal root visit) : MaterialState root := ⟨visit, material⟩

def start? (root : SourceNativeLivingRootClosure N V) : Seed root → Option (MaterialState root)
  | .initial entry =>
      (formInitial root entry).map (atVisit (.finite root.toAuthoritativeRoot.toRoot.initialVisit))
  | .cofinal entry =>
      (formCofinal root).bind fun visit =>
        (formCofinalAt root visit (cofinalEntryAt root visit entry)).map (atVisit (.cofinal visit))

def nextMaterial {root : SourceNativeLivingRootClosure N V}
    {current : V.Current}
    {history : SourceNativeTemporalReachableAt root.toAuthoritativeRoot.toLedgerRoot current}
    {entry : EntryAt root current} (material : Material root history entry)
    {next : V.Current}
    (next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? = some next) :
    Material root (history.next next_eq)
      (root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext next_eq entry) :=
  match history with
  | .finite _ => .finiteSuccessor next_eq material
  | .postCofinal _ => .postCofinalSuccessor next_eq material

theorem assemble_nextMaterial {root : SourceNativeLivingRootClosure N V}
    {current : V.Current}
    {history : SourceNativeTemporalReachableAt root.toAuthoritativeRoot.toLedgerRoot current}
    {entry : EntryAt root current} (material : Material root history entry)
    {next : V.Current}
    (next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? = some next) :
    assemble (nextMaterial material next_eq) = (assemble material).next next_eq := by
  cases history <;> rfl

/-- The original root compiler supplies the successor value and its equality. -/
def advance? (root : SourceNativeLivingRootClosure N V) (state : MaterialState root) :
    Option (MaterialState root) :=
  match next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt state.1.current).nextCurrent? with
  | none => none
  | some _next => some ⟨state.1.next next_eq,
      ⟨root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext next_eq state.2.1,
        nextMaterial state.2.2 next_eq⟩⟩

private theorem advance_recovers (root : SourceNativeLivingRootClosure N V)
    (state : MaterialState root) {next : V.Current}
    (next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt state.1.current).nextCurrent? = some next) :
    advance? root state = some ⟨state.1.next next_eq,
      ⟨root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext next_eq state.2.1,
        nextMaterial state.2.2 next_eq⟩⟩ := by
  unfold advance?
  split
  · rename_i absent
    cases next_eq.symm.trans absent
  · rename_i other produced
    have same : other = next := Option.some.inj (produced.symm.trans next_eq)
    cases same
    rfl

def generate? (root : SourceNativeLivingRootClosure N V) (seed : Seed root) :
    Nat → Option (MaterialState root)
  | 0 => start? root seed
  | steps + 1 => (generate? root seed steps).bind (advance? root)

theorem every_material (root : SourceNativeLivingRootClosure N V)
    {current : V.Current}
    {history : SourceNativeTemporalReachableAt root.toAuthoritativeRoot.toLedgerRoot current}
    {entry : EntryAt root current} (material : Material root history entry) :
    ∃ seed : Seed root, ∃ steps : Nat,
      generate? root seed steps = some ⟨⟨current, history⟩, ⟨entry, material⟩⟩ := by
  induction material with
  | initialAdmission entry row =>
      refine ⟨.initial entry, 0, ?_⟩
      exact congrArg (Option.map (atVisit (.finite root.toAuthoritativeRoot.toRoot.initialVisit)))
        (formInitial_recovers root entry row)
  | @cofinalAdmission visit entry row =>
      refine ⟨.cofinal (cofinalInput root visit entry), 0, ?_⟩
      change (formCofinal root).bind _ = _
      rw [formCofinal_recovers root visit]
      change (formCofinalAt root visit (cofinalEntryAt root visit (cofinalInput root visit entry))).map _ = _
      rw [cofinalInput_recovers root visit entry]
      exact congrArg (Option.map (atVisit (.cofinal visit)))
        (formCofinalAt_recovers root visit entry row)
  | finiteSuccessor next_eq prior ih =>
      obtain ⟨seed, steps, generated⟩ := ih
      refine ⟨seed, steps + 1, ?_⟩
      rw [generate?, generated]
      exact advance_recovers root _ next_eq
  | postCofinalSuccessor next_eq prior ih =>
      obtain ⟨seed, steps, generated⟩ := ih
      refine ⟨seed, steps + 1, ?_⟩
      rw [generate?, generated]
      exact advance_recovers root _ next_eq

abbrev AuthorityState (root : SourceNativeLivingRootClosure N V) :=
  Σ visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot,
    AuthorityTotal root visit

def assembleState {root : SourceNativeLivingRootClosure N V}
    (state : MaterialState root) : AuthorityState root :=
  ⟨state.1, assembleTotal state.2⟩

def formAuthority (root : SourceNativeLivingRootClosure N V) (seed : Seed root) (steps : Nat) :
    Option (AuthorityState root) :=
  (generate? root seed steps).map assembleState

/-- Every original full authority is recovered from source entry material and finite transport count. -/
theorem every_authority (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (authority : AuthorityTotal root visit) :
    ∃ seed : Seed root, ∃ steps : Nat,
      formAuthority root seed steps = some ⟨visit, authority⟩ := by
  obtain ⟨seed, steps, generated⟩ := every_material root (decomposeTotal authority).2
  refine ⟨seed, steps, ?_⟩
  calc
    formAuthority root seed steps = some ⟨visit, assembleTotal (decomposeTotal authority)⟩ :=
      congrArg (Option.map assembleState) generated
    _ = some ⟨visit, authority⟩ :=
      congrArg (fun value : AuthorityTotal root visit =>
        (some ⟨visit, value⟩ : Option (AuthorityState root))) (assemble_decomposeTotal authority)

end
end MotherNativeAuthority
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
