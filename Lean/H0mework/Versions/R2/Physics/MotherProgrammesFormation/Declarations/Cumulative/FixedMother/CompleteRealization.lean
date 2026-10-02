import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.FixedMother.Formation

/-! A single quantified conclusion joins the fixed Mother's completion,
the actual source factories, full inverse restrictions and native consumers.
The original admission types are unchanged; all formation properties are
conclusions of the theorem, not additional admission conditions. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FixedMotherRealization
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion ZeroLawRootAdmission
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

/-- The whole spaces of all parents survive a source-material expansion. -/
def ParentsRetained {High Low : Type} (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) : Prop :=
  Function.LeftInverse
    (fun material =>
      ((fun index => MotherMaterialJoin.Mixed.restrictHigh high low index material),
        (fun index => MotherMaterialJoin.Mixed.restrictLow high low index material)))
    (fun materials => MotherMaterialJoin.Mixed.combine high low materials.1 materials.2)

structure WorldRealization {root : SourceNativeAuthoritativeRootClosure N V}
    {state : LawfulWorldStateAt root}
    (origin : MotherAdmittedWorld.Origin (⟨V, root, state⟩ : MotherAdmittedWorld.StateAt N)) : Prop where
  formation : LowFormation origin.rank origin.material
  formed : MotherAdmittedWorld.formState origin.presentation.restrictHeader
    (MotherArenaHigher.split origin.rank origin.material).2 = some ⟨V, root, state⟩
  world : origin.world = ⟨N, V, root, state⟩
  fields : origin.read = ⟨V, root, state⟩
  originalMaterial : Function.LeftInverse
    (MotherArenaHigher.restrictOriginal origin.rank origin.originalAddress)
    (MotherArenaHigher.includeOriginal origin.rank origin.originalAddress)
  occurrence : HEq origin.read.2.2.registeredOccurrence state.registeredOccurrence
  authority : HEq origin.read.2.2.authoritativeEvolution state.authoritativeEvolution
  disposition : HEq origin.read.2.2.positiveDisposition state.positiveDisposition
  priorPatches : HEq origin.read.2.2.registeredOccurrence.2.priorPatches state.registeredOccurrence.2.priorPatches
  currentPatch : HEq origin.read.2.2.registeredOccurrence.2.currentPatch state.registeredOccurrence.2.currentPatch
  wholeLedger : HEq origin.read.2.2.registeredOccurrence.2.wholeLedgerWriteBack state.registeredOccurrence.2.wholeLedgerWriteBack
  next : HEq (origin.read.2.1.toRoot.evolutionAt origin.read.2.2.current).nextCurrent?
    (root.toRoot.evolutionAt state.current).nextCurrent?
  advance : HEq (MotherAdmittedWorld.advance origin.read.2.1.toLedgerRoot origin.read.2.2)
    (MotherAdmittedWorld.advance root.toLedgerRoot state)
  totalReality : TotalReality.TotalRealityAt (RootTotalReality.semantics origin.read.2.1)

structure InquiryRealization {state : RootInquiryStateAt N V}
    (origin : MotherCompleteInquiry.Origin state) : Prop where
  formation : HighFormation origin.rank origin.material
  parents : ParentsRetained origin.highRank origin.lowRank
  world : origin.readWorld = ⟨N, V, RootInquiryEngineStateAt.create state⟩
  clauses : origin.clauses = MotherNativeClause.ofState state
  compile : ∀ query : origin.readWorld.Query,
    HEq (origin.readWorld.state.base.compileInquiry query)
      (state.compileInquiry (Equiv.cast (congrArg RootInquiryStatePresentation.Query origin.readWorld_eq) query))
  everyEvent : ∀ event : ExactTemporalCausalRootEventAt state.root.toAuthoritativeRoot.toLedgerRoot state.visit,
    ∀ query : state.Query, HEq ((origin.clauses query).program.compile event) (state.compileInquiry query)

structure ProcessRealization {original : SourceNativeInquiryEngineProcess.{0}}
    (origin : MotherMacroSource.Origin original) : Prop where
  formation : HighFormation origin.rank origin.material
  parents : ParentsRetained origin.highRank origin.lowRank
  formed : origin.form = some origin.process
  process : origin.restrict = original
  states : origin.restrict.State = original.State
  stateAt : HEq origin.restrict.stateAt original.stateAt
  initial : HEq origin.restrict.initial original.initial
  successorAt : HEq origin.restrict.successorAt original.successorAt
  compile : ∀ index : origin.process.State, ∀ query : (origin.process.stateAt index).Query,
    HEq (MotherRegistryRecovery.compile (origin.process.stateAt index) query)
      (MotherRegistryRecovery.compile (original.stateAt (origin.presentation.state index))
        (origin.presentation.query index query))
  ask : ∀ engine : Engine original, ∀ activation : Engine.SourceNativeInquiryActivationAt engine,
    let actual := (MotherMacroRuntime.transportEngine origin.restrict_eq.symm engine).ask
      (MotherMacroRuntime.transportActivation origin.restrict_eq.symm activation)
    HEq actual (engine.ask activation) ∧
    actual.next = MotherMacroRuntime.transportEngine origin.restrict_eq.symm (engine.ask activation).next
  law : ∀ prior : Engine.SourceNativeInquiryActivationLaw original,
    let actual := MotherMacroRuntime.transportLaw origin.restrict_eq.symm prior
    HEq actual prior ∧ HEq actual.initial prior.initial ∧ HEq actual.nextAt prior.nextAt
  tick : ∀ runtime : SourceNativeInquiryRuntime original, ∀ state : runtime.State,
    let actual := (MotherMacroRuntime.transportState origin.restrict_eq.symm state).tick
    HEq actual state.tick ∧
    actual.nextState = MotherMacroRuntime.transportState origin.restrict_eq.symm state.tick.nextState
  history : ∀ runtime : SourceNativeInquiryRuntime original, ∀ depth : Nat,
    (origin.runtime runtime).stateAt depth =
      MotherMacroRuntime.transportState origin.restrict_eq.symm (runtime.stateAt depth) ∧
    HEq ((origin.runtime runtime).tickAt depth) (runtime.tickAt depth) ∧
    ((origin.runtime runtime).tickAt depth).nextState =
      MotherMacroRuntime.transportState origin.restrict_eq.symm (runtime.tickAt depth).nextState

private theorem process_fields {first last : SourceNativeInquiryEngineProcess.{0}} (same : first = last) :
    first.State = last.State ∧ HEq first.stateAt last.stateAt ∧
      HEq first.initial last.initial ∧ HEq first.successorAt last.successorAt := by
  cases same
  exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- Root admission, fixed-mother formation and full faithful realization in
one theorem. Every material witness is in the full completion of actual
programmes of MotherFamilyOccurrence.MotherRoot; each factory consumes
that same material. The three quantified domains are the original world,
inquiry and complete process interfaces, without added premises. -/
theorem root_admission_fixed_mother_complete_realization :
    (∀ (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
      (root : SourceNativeAuthoritativeRootClosure N V) (state : LawfulWorldStateAt root),
      ∃ origin : MotherAdmittedWorld.Origin (⟨V, root, state⟩ : MotherAdmittedWorld.StateAt N),
        WorldRealization origin) ∧
    (∀ (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0}) (state : RootInquiryStateAt N V),
      ∃ origin : MotherCompleteInquiry.Origin state, InquiryRealization origin) ∧
    (∀ original : SourceNativeInquiryEngineProcess.{0},
      ∃ origin : MotherMacroSource.Origin original, ProcessRealization origin) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N V root state
    obtain ⟨origin⟩ := MotherAdmittedWorld.every_state N ⟨V, root, state⟩
    obtain ⟨occurrence, authority, disposition, prior, current, ledger, next, advance⟩ := origin.consumers_recovers
    exact ⟨origin, {
      formation := low_formation origin.rank origin.material
      formed := origin.formed
      world := origin.world_eq
      fields := origin.read_eq
      originalMaterial := origin.originalRetained
      occurrence := occurrence
      authority := authority
      disposition := disposition
      priorPatches := prior
      currentPatch := current
      wholeLedger := ledger
      next := next
      advance := advance
      totalReality := origin.totalReality }⟩
  · intro N V state
    obtain ⟨origin⟩ := MotherCompleteInquiry.every_source N V state
    exact ⟨origin, {
      formation := high_formation origin.rank origin.material
      parents := origin.whole_material_spaces
      world := origin.readWorld_eq
      clauses := origin.clauses_eq
      compile := origin.compile_recovers
      everyEvent := fun event query => origin.compile_at_every_event query event }⟩
  · intro original
    obtain ⟨origin⟩ := MotherMacroSource.every_source original
    obtain ⟨states, stateAt, initial, successorAt⟩ := process_fields origin.restrict_eq
    refine ⟨origin, {
      formation := high_formation origin.rank origin.material
      parents := origin.whole_material_spaces
      formed := origin.form_formed.trans (congrArg some origin.process_eq.symm)
      process := origin.restrict_eq
      states := states
      stateAt := stateAt
      initial := initial
      successorAt := successorAt
      compile := origin.compile_recovers
      ask := ?_
      law := fun prior => MotherMacroRuntime.law_recovers origin.restrict_eq.symm prior
      tick := ?_
      history := origin.runtime_history }⟩
    · intro engine activation
      obtain ⟨whole, _, _, _, next⟩ := origin.ask_recovers engine activation
      exact ⟨whole, next⟩
    · intro runtime state
      obtain ⟨whole, _, _, _, _, _, _, nextState⟩ := origin.runtime_tick runtime state
      exact ⟨whole, nextState⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FixedMotherRealization
