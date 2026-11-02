import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem nativeNext_eq (frame : NativeFrame input) (current : frame.V.Current) :
    (frame.root.toAuthoritativeRoot.toLedgerRoot.toRoot.evolutionAt current).nextCurrent? =
      some (frame.V.nativeTarget (frame.program.emit current).write) := by
  exact congrArg EvolutionAt.nextCurrent? (frame.program.emit current).structural_eq

structure EntryProtocol (frame : NativeFrame input) : Prop where
  entry_image : ∀ current, HEq
    ((frame.program.emit current).evolution.destination
      (frame.entrySupport
        (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (frame.root.emitted current)))).1
    (frame.entrySupport
      (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.root.emitted (frame.V.nativeTarget (frame.program.emit current).write))))
  entry_next : ∀ current,
    frame.root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (nativeNext_eq input frame current)
      (frame.entrySupport
        (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (frame.root.emitted current))) =
    frame.entrySupport
      (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (frame.root.emitted (frame.V.nativeTarget (frame.program.emit current).write)))

theorem entry_eq_of_key {N : WorldRelationNetwork} {support : N.Support}
    (left right : OpenResponsibilityAt N support)
    (same : left.1 = right.1)
    (fibres : ∀ responsibility, Subsingleton (N.OpenAt support responsibility)) : left = right := by
  rcases left with ⟨left, openedLeft⟩
  rcases right with ⟨right, openedRight⟩
  dsimp at same
  subst right
  exact Sigma.ext rfl (heq_of_eq ((fibres left).elim _ _))

theorem canonicalEntry_key : {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (left right : (world input (ProgrammeSource.N input) run).Support) →
    (canonicalEntry input run left).1 = (canonicalEntry input run right).1 := by
  intro current run
  induction run with
  | nil => intro left right; cases left <;> cases right <;> rfl
  | step prior edge ih =>
      intro left right
      cases edge with
      | admit _ => exact congrArg Sum.inl (ih left.1 right.1)
      | cross _ _ _ _ => exact ih left right
      | reopen _ _ _ impossible => exact impossible.elim

namespace AccountSource

variable (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

theorem whole_canonical_entry (current : Current input start) :
    ((wholeEvolution input start current).destination
      (canonicalEntry input start.account.generated (supportAt input start current))).1 =
      canonicalEntry input start.account.generated (supportAt input start (next input start current)) :=
  entry_eq_of_key _ _
    (((wholeEvolution_keeps_keys input start current).1 _).trans
      (canonicalEntry_key input start.account.generated _ _))
    (world_openAt_subsingleton input start.account.generated _)

theorem entryProtocol : EntryProtocol input (nativeFrame input start startPositive) := by
  constructor
  · intro current
    change HEq ((patch input start startPositive current).toLedgerWriteEvolution.destination
      (canonicalEntry input start.account.generated (supportAt input start current))).1 _
    have selected := congrFun (patch_destination input start startPositive current)
      (canonicalEntry input start.account.generated (supportAt input start current))
    exact (heq_of_eq (congrArg Sigma.fst selected)).trans
      (heq_of_eq (whole_canonical_entry input start current))
  · intro current
    change ((patch input start startPositive current).toLedgerWriteEvolution.destination
      (canonicalEntry input start.account.generated (supportAt input start current))).1 = _
    have selected := congrFun (patch_destination input start startPositive current)
      (canonicalEntry input start.account.generated (supportAt input start current))
    exact (congrArg Sigma.fst selected).trans (whole_canonical_entry input start current)

end AccountSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
