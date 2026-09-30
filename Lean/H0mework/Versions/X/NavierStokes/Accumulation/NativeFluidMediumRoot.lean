import H0mework.NavierStokes.Accumulation.NativeFluidMedium
import H0mework.Foundation.Runtime.GeneratedContinuity
import H0mework.Foundation.Arithmetic.RootIncidence
import H0mework.Foundation.Inquiry.ObstructionLineage
import H0mework.Foundation.Authority.EntryDisposition

/-!
# Living-law root for a source-native fluid medium

The medium, not its classical NS restriction, is the actual root event in
this module.  One compiler occurrence carries the source/action state,
constitutive stress, temporal ledger, classical whole restriction, medium
residual and adjacent-patch commuting law.  The classical and residual faces
are dependent projections of that occurrence; neither can be installed as a
sibling source.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticGeneration
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-! ## Actual-state physical and operational ledger network -/

/-- The complete medium ledger has one physical occurrence row and one
operational standing row. -/
inductive NativeFluidMediumResponsibility
  | physical
  | operational
  deriving DecidableEq

inductive NativeFluidMediumClaim
  | physical
  | operational
  deriving DecidableEq

/-- Exact seal of the source-generated operational effect at one state. -/
structure NativeFluidMediumExactOperationalEffectAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) : Type where
  private mk ::
  effect : source.OperationalEffectAt state
  effect_eq : effect = source.operationalEffectAt state

def nativeFluidMediumExactOperationalEffectAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    NativeFluidMediumExactOperationalEffectAt source state :=
  ⟨source.operationalEffectAt state, rfl⟩

namespace NativeFluidMediumExactOperationalEffectAt

instance instSubsingleton
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State} :
    Subsingleton (NativeFluidMediumExactOperationalEffectAt source state) where
  allEq := by
    rintro ⟨left, leftEq⟩ ⟨right, rightEq⟩
    subst left
    subst right
    rfl

def arithmeticMaterial
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (effect : NativeFluidMediumExactOperationalEffectAt source state) :
    RootArithmeticMaterialAt :=
  source.operationalArithmeticMaterialAt effect.effect

def parallelNormalForm
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (effect : NativeFluidMediumExactOperationalEffectAt source state) :
    ParallelIncidenceNormalFormAt effect.effect effect.arithmeticMaterial :=
  normalizeParallel effect.effect effect.arithmeticMaterial

def netEnstrophyDebit
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (effect : NativeFluidMediumExactOperationalEffectAt source state) : Real :=
  source.operationalNetEnstrophyDebitAt effect.effect

def contactTime
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (effect : NativeFluidMediumExactOperationalEffectAt source state) : Real :=
  source.operationalContactTimeAt effect.effect

theorem contactTime_pos
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (effect : NativeFluidMediumExactOperationalEffectAt source state) :
    0 < effect.contactTime :=
  source.operationalContactTime_pos effect.effect

end NativeFluidMediumExactOperationalEffectAt

/-- Both ledger rows are generated from the exact same medium state. -/
inductive NativeFluidMediumOpenAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) : NativeFluidMediumResponsibility → Type
  | physical (occurrence : NativeFluidMediumOccurrence source state) :
      NativeFluidMediumOpenAt source state .physical
  | operational
      (effect : NativeFluidMediumExactOperationalEffectAt source state) :
      NativeFluidMediumOpenAt source state .operational

private instance nativeFluidMediumOccurrence_subsingleton
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State} :
    Subsingleton (NativeFluidMediumOccurrence source state) where
  allEq := by intro left right; cases left; cases right; rfl

private instance nativeFluidMediumOpenAt_subsingleton
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (state : source.State)
    (responsibility : NativeFluidMediumResponsibility) :
    Subsingleton (NativeFluidMediumOpenAt source state responsibility) where
  allEq := by
    intro left right
    cases left with
    | physical leftOccurrence =>
        cases right with
        | physical rightOccurrence =>
            cases Subsingleton.elim leftOccurrence rightOccurrence
            rfl
    | operational leftEffect =>
        cases right with
        | operational rightEffect =>
            cases Subsingleton.elim leftEffect rightEffect
            rfl

/-- A generated residual is paid by one of the two quantitative projections
of the same dependent material: either its standing debit is already
positive, or its source-generated physical expansion has positive finite
valuation.  No qualitative kind can be paired with a foreign scalar proof. -/
inductive NativeFluidMediumResidualPaymentAt
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (effect : NativeFluidMediumExactOperationalEffectAt source state)
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (expansion : source.OperationalResidualExpansionAt effect.effect residual) :
    Type
  | standingDebit
      (positive : 0 < effect.netEnstrophyDebit)
  | expansionDebit
      (positive : 0 < source.operationalResidualExpansionDebitAt
        effect.effect residual expansion)

/-- A residual obstruction is silent in both valuations of the same
material.  The root, rather than a downstream classifier, owns this exact
liability and its U7 disposition. -/
structure NativeFluidMediumOperationalObstructionAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) : Type where
  effect : NativeFluidMediumExactOperationalEffectAt source state
  residual : GeneratedParallelResidualAt effect.effect effect.arithmeticMaterial
  expansion : source.OperationalResidualExpansionAt effect.effect residual
  expansion_eq : expansion =
    source.generateOperationalResidualExpansionAt effect.effect residual
  netEnstrophyDebit_nonpos : effect.netEnstrophyDebit ≤ 0
  residualExpansionDebit_nonpos :
    source.operationalResidualExpansionDebitAt
      effect.effect residual expansion ≤ 0

namespace NativeFluidMediumOperationalObstructionAt

def liability
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (obstruction : NativeFluidMediumOperationalObstructionAt source state) :
    Real :=
  -obstruction.effect.netEnstrophyDebit

theorem liability_nonneg
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (obstruction : NativeFluidMediumOperationalObstructionAt source state) :
    0 ≤ obstruction.liability := by
  unfold liability
  linarith [obstruction.netEnstrophyDebit_nonpos]

theorem residualExpansionDebit_eq_zero
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (obstruction : NativeFluidMediumOperationalObstructionAt source state) :
    source.operationalResidualExpansionDebitAt obstruction.effect.effect
        obstruction.residual obstruction.expansion = 0 := by
  exact le_antisymm obstruction.residualExpansionDebit_nonpos
    (source.operationalResidualExpansionDebit_nonneg
      obstruction.effect.effect obstruction.residual obstruction.expansion)

end NativeFluidMediumOperationalObstructionAt

/-- Typed world receipts.  Their dependent effect is the same source payload
that appears in the root current and native write. -/
inductive NativeFluidMediumDispositionAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) : WorldDispositionKind → Type
  | physicalAdvance
      (occurrence : NativeFluidMediumOccurrence source state) :
      NativeFluidMediumDispositionAt source state .transfer
  | exactPayment
      (effect : NativeFluidMediumExactOperationalEffectAt source state)
      (rooted : IncidenceProvenanceAt effect.effect)
      (commutes : effect.arithmeticMaterial.whole =
        effect.arithmeticMaterial.left.parallel
          effect.arithmeticMaterial.right) :
      NativeFluidMediumDispositionAt source state .transfer
  | generatedResidual
      (effect : NativeFluidMediumExactOperationalEffectAt source state)
      (residual : GeneratedParallelResidualAt
        effect.effect effect.arithmeticMaterial)
      (expansion : source.OperationalResidualExpansionAt effect.effect residual)
      (expansion_eq : expansion =
        source.generateOperationalResidualExpansionAt effect.effect residual)
      (payment : NativeFluidMediumResidualPaymentAt
        effect residual expansion) :
      NativeFluidMediumDispositionAt source state .transfer
  | obstructionAdvance
      (obstruction : NativeFluidMediumOperationalObstructionAt source state) :
      NativeFluidMediumDispositionAt source state .transfer
  | obstructionAudit
      (obstruction : NativeFluidMediumOperationalObstructionAt source state) :
      NativeFluidMediumDispositionAt source state .lawSurfaceExtension

private def operationalTransferReceiptFromNormalForm
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (effect : NativeFluidMediumExactOperationalEffectAt source state)
    (normalForm : ParallelIncidenceNormalFormAt
      effect.effect effect.arithmeticMaterial) :
    NativeFluidMediumDispositionAt source state .transfer :=
  match normalForm with
  | .exact rooted commutes => .exactPayment effect rooted commutes
  | .generatedResidual residual =>
      let expansion :=
        source.generateOperationalResidualExpansionAt effect.effect residual
      if debitPos : 0 < effect.netEnstrophyDebit then
        .generatedResidual effect residual expansion rfl
          (.standingDebit debitPos)
      else if expansionPos :
          0 < source.operationalResidualExpansionDebitAt
          effect.effect residual expansion
      then
        .generatedResidual effect residual expansion rfl
          (.expansionDebit expansionPos)
      else
        .obstructionAdvance
          ⟨effect, residual, expansion, rfl, le_of_not_gt debitPos,
            le_of_not_gt expansionPos⟩

/-- The only public transfer receipt uses the normal form computed by this
source effect; no caller selects a branch or its payment proof. -/
def nativeFluidMediumOperationalTransferReceipt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    NativeFluidMediumDispositionAt source state .transfer :=
  let effect := nativeFluidMediumExactOperationalEffectAt source state
  operationalTransferReceiptFromNormalForm source state effect
    effect.parallelNormalForm

/-- A transfer can expose the clock carried by its actual operational effect.
The physical-row constructor has no such operational receipt. -/
def nativeFluidMediumTransferContactTime?
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    NativeFluidMediumDispositionAt source state .transfer → Option Real
  | .physicalAdvance _ => none
  | .exactPayment effect _ _ => some effect.contactTime
  | .generatedResidual effect _ _ _ _ => some effect.contactTime
  | .obstructionAdvance obstruction => some obstruction.effect.contactTime

private theorem operationalTransferReceiptFromNormalForm_contactTime
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (effect : NativeFluidMediumExactOperationalEffectAt source state)
    (normalForm : ParallelIncidenceNormalFormAt
      effect.effect effect.arithmeticMaterial) :
    nativeFluidMediumTransferContactTime? source state
        (operationalTransferReceiptFromNormalForm source state effect normalForm) =
      some effect.contactTime := by
  cases normalForm with
  | exact rooted commutes =>
      rfl
  | generatedResidual residual =>
      simp only [operationalTransferReceiptFromNormalForm,
        nativeFluidMediumTransferContactTime?]
      split_ifs <;> rfl

theorem nativeFluidMediumOperationalTransferReceipt_contactTime
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    nativeFluidMediumTransferContactTime? source state
        (nativeFluidMediumOperationalTransferReceipt source state) =
      some (nativeFluidMediumExactOperationalEffectAt source state).contactTime := by
  exact operationalTransferReceiptFromNormalForm_contactTime source state
    (nativeFluidMediumExactOperationalEffectAt source state)
    (nativeFluidMediumExactOperationalEffectAt source state).parallelNormalForm

/-- The shared support is the complete source state, not a singleton shadow. -/
def nativeFluidMediumNetwork
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) : WorldRelationNetwork where
  Support := source.State
  Anchor := PUnit
  Incidence := PUnit
  Lineage := PUnit
  Responsibility := NativeFluidMediumResponsibility
  Claim := NativeFluidMediumClaim
  anchorAt := fun _ => PUnit.unit
  incidenceAt := fun _ => PUnit.unit
  lineageAt := fun _ => PUnit.unit
  OpenAt := NativeFluidMediumOpenAt source
  openClaimAt := fun openAt => match openAt with
    | .physical _ => .physical
    | .operational _ => .operational
  HoldsAt := fun state claim => match claim with
    | .physical => NativeFluidMediumOccurrence source state
    | .operational => NativeFluidMediumExactOperationalEffectAt source state
  ObstructionAt := NativeFluidMediumOperationalObstructionAt source
  obstructionClaim := fun _ => .operational
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := NativeFluidMediumDispositionAt source

abbrev NativeFluidMediumNetwork
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) := nativeFluidMediumNetwork source

/-- U7 demand calculus for an exact nonpositive operational obstruction.  The
demand payload is empty because its complete identity is already carried by
the dependent obstruction index. -/
def nativeFluidMediumU7Producer
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    U7ProducerCalculus (NativeFluidMediumNetwork source) where
  DemandAt := fun _ => PUnit
  generateDemand := fun _ => PUnit.unit

/-- Total source outcome at one medium state.  The obstruction branch already
contains the exact source-generated U7 demand seal; no later caller chooses a
branch or supplies a demand. -/
inductive NativeFluidMediumRootOperationalOutcomeAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) : Type
  | exactPayment
      (effect : NativeFluidMediumExactOperationalEffectAt source state)
      (rooted : IncidenceProvenanceAt effect.effect)
      (commutes : effect.arithmeticMaterial.whole =
        effect.arithmeticMaterial.left.parallel
          effect.arithmeticMaterial.right)
  | generatedResidual
      (effect : NativeFluidMediumExactOperationalEffectAt source state)
      (residual : GeneratedParallelResidualAt
        effect.effect effect.arithmeticMaterial)
      (expansion : source.OperationalResidualExpansionAt effect.effect residual)
      (expansion_eq : expansion =
        source.generateOperationalResidualExpansionAt effect.effect residual)
      (payment : NativeFluidMediumResidualPaymentAt
        effect residual expansion)
  | obstruction
      (obstruction : NativeFluidMediumOperationalObstructionAt source state)
      (demand : SourceGeneratedU7DemandAt
        (nativeFluidMediumU7Producer source) obstruction
          ((nativeFluidMediumU7Producer source).generateDemand obstruction))

def nativeFluidMediumRootOperationalOutcomeAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    NativeFluidMediumRootOperationalOutcomeAt source state := by
  let effect := nativeFluidMediumExactOperationalEffectAt source state
  generalize normalFormEq : effect.parallelNormalForm = normalForm
  cases normalForm with
  | exact rooted commutes =>
      exact .exactPayment effect rooted commutes
  | generatedResidual residual =>
    let expansion :=
      source.generateOperationalResidualExpansionAt effect.effect residual
    by_cases debitPos : 0 < effect.netEnstrophyDebit
    · exact .generatedResidual effect residual expansion rfl
        (.standingDebit debitPos)
    · by_cases expansionPos :
        0 < source.operationalResidualExpansionDebitAt
          effect.effect residual expansion
      · exact .generatedResidual effect residual expansion rfl
          (.expansionDebit expansionPos)
      ·
        let obstruction : NativeFluidMediumOperationalObstructionAt source state :=
          ⟨effect, residual, expansion, rfl, le_of_not_gt debitPos,
            le_of_not_gt expansionPos⟩
        exact .obstruction obstruction
          (@SourceGeneratedU7DemandAt.canonical
            (NativeFluidMediumNetwork source)
            (nativeFluidMediumU7Producer source) state obstruction)

/-- Dependent paid subtype of the root's total operational outcome.  This is
not a second classifier: it pattern-matches the already generated outcome
and is empty exactly on its obstruction constructor. -/
def NativeFluidMediumRootOperationalOutcomeAt.IsPaid
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (outcome : NativeFluidMediumRootOperationalOutcomeAt source state) : Type :=
  match outcome with
  | .exactPayment _ _ _ => PUnit
  | .generatedResidual _ _ _ _ _ => PUnit
  | .obstruction _ _ => PEmpty

def nativeFluidMediumVocabulary
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) : Vocabulary where
  Current := source.State
  Anchor := PUnit
  Incidence := PUnit
  Lineage := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := fun _ => PUnit.unit
  lineageAt := fun _ => PUnit.unit
  NativeWriteAt := NativeFluidMediumOccurrence source
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => source.successor current
  relationTarget := fun write => nomatch write
  continuedTarget := fun write => nomatch write
  redirectTarget := fun write => nomatch write

abbrev NativeFluidMediumVocabulary
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :=
  nativeFluidMediumVocabulary source

inductive NativeFluidMediumRootEventAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    source.State → source.State → Type
  | actual (state : source.State)
      (occurrence : NativeFluidMediumOccurrence source state) :
      NativeFluidMediumRootEventAt source state state

def nativeFluidMediumEventAlgebra
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeEventAlgebra (NativeFluidMediumNetwork source)
      (NativeFluidMediumVocabulary source) where
  EventAt := NativeFluidMediumRootEventAt source
  compile := fun event => match event with
    | .actual _ occurrence => .nativeWrite occurrence
  AffectedInventoryAt := fun {_current} {support} _ =>
    OpenResponsibilityAt (NativeFluidMediumNetwork source) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def nativeFluidMediumSource
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeSource (NativeFluidMediumNetwork source)
      (NativeFluidMediumVocabulary source) where
  initial := source.initial
  law := nativeFluidMediumEventAlgebra source

def nativeFluidMediumEmitted
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    (nativeFluidMediumSource source).toRootSource.actual.OccurrenceAt state :=
  ⟨state, .actual state (source.generateOccurrence state)⟩

def nativeFluidMediumPhysicalEntry
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    OpenResponsibilityAt (NativeFluidMediumNetwork source) state :=
  ⟨.physical, .physical (source.generateOccurrence state)⟩

def nativeFluidMediumOperationalEntry
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    OpenResponsibilityAt (NativeFluidMediumNetwork source) state :=
  ⟨.operational,
    .operational (nativeFluidMediumExactOperationalEffectAt source state)⟩

def nativeFluidMediumEntryAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) : Fin 2 →
      OpenResponsibilityAt (NativeFluidMediumNetwork source) state
  | ⟨0, _⟩ => nativeFluidMediumPhysicalEntry source state
  | ⟨1, _⟩ => nativeFluidMediumOperationalEntry source state

def nativeFluidMediumEntryIndex
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State} :
    OpenResponsibilityAt (NativeFluidMediumNetwork source) state → Fin 2
  | ⟨.physical, _⟩ => ⟨0, by decide⟩
  | ⟨.operational, _⟩ => ⟨1, by decide⟩

theorem nativeFluidMediumEntryAt_index
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (entry : OpenResponsibilityAt (NativeFluidMediumNetwork source) state) :
    nativeFluidMediumEntryAt source state
        (nativeFluidMediumEntryIndex entry) = entry := by
  rcases entry with ⟨responsibility, openAt⟩
  cases openAt with
  | physical occurrence =>
      change nativeFluidMediumPhysicalEntry source state = _
      cases Subsingleton.elim occurrence (source.generateOccurrence state)
      rfl
  | operational effect =>
      change nativeFluidMediumOperationalEntry source state = _
      cases Subsingleton.elim effect
        (nativeFluidMediumExactOperationalEffectAt source state)
      rfl

private theorem nativeFluidMediumEntry_eq_of_responsibility_eq
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (left right : OpenResponsibilityAt
      (NativeFluidMediumNetwork source) state)
    (responsibilityEq : left.1 = right.1) : left = right := by
  rcases left with ⟨leftResponsibility, leftOpen⟩
  rcases right with ⟨rightResponsibility, rightOpen⟩
  cases responsibilityEq
  have openEq : leftOpen = rightOpen :=
    (nativeFluidMediumOpenAt_subsingleton state leftResponsibility).allEq
      leftOpen rightOpen
  cases openEq
  rfl

private structure NativeFluidMediumExactTransitionAt
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    (occurrence : (nativeFluidMediumSource source).toRootSource.actual.OccurrenceAt
      state)
    {targetSupport : source.State}
    (sourceEntry : OpenResponsibilityAt
      (NativeFluidMediumNetwork source) occurrence.1)
    (targetEntry : OpenResponsibilityAt
      (NativeFluidMediumNetwork source) targetSupport) : Type where
  responsibility_eq : sourceEntry.1 = targetEntry.1

private inductive NativeFluidMediumRowEventAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    {current : source.State} →
    (occurrence : (nativeFluidMediumSource source).toRootSource.actual.OccurrenceAt
      current) →
    {targetSupport : source.State} →
    (sourceEntry : OpenResponsibilityAt
      (NativeFluidMediumNetwork source) occurrence.1) →
    (targetEntry : OpenResponsibilityAt
      (NativeFluidMediumNetwork source) targetSupport) →
      Type
  | physical (state : source.State)
      (occurrence : NativeFluidMediumOccurrence source state) :
      NativeFluidMediumRowEventAt source
        ⟨state, .actual state occurrence⟩
        (nativeFluidMediumPhysicalEntry source state)
        (nativeFluidMediumPhysicalEntry source (source.successor state))
  | operational (state : source.State)
      (occurrence : NativeFluidMediumOccurrence source state) :
      NativeFluidMediumRowEventAt source
        ⟨state, .actual state occurrence⟩
        (nativeFluidMediumOperationalEntry source state)
        (nativeFluidMediumOperationalEntry source (source.successor state))

private def nativeFluidMediumWriteRowSource
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    LedgerWriteRowSourceAt (nativeFluidMediumSource source) (by
      intro _ occurrence targetSupport sourceEntry targetEntry
      exact NativeFluidMediumExactTransitionAt occurrence sourceEntry targetEntry) :=
  { IncidenceOccurrenceAt := NativeFluidMediumRowEventAt source
    compileEvolution := fun event => by
      cases event with
      | physical occurrence =>
          exact .transferred (.physicalAdvance occurrence) rfl rfl
            (Nat.zero_le 0)
      | operational occurrence =>
          exact .transferred
            (nativeFluidMediumOperationalTransferReceipt source _)
            rfl rfl (Nat.zero_le 0)
    compileExact := fun event => by
      cases event
      all_goals exact ⟨rfl⟩ }

private def nativeFluidMediumRows
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (occurrence : NativeFluidMediumOccurrence source state) :
    FiniteGeneratedLedgerWriteRowsAt
      (nativeFluidMediumWriteRowSource source)
      ⟨state, .actual state occurrence⟩
      ⟨source.successor state⟩ where
  size := 2
  sourceEntryAt := nativeFluidMediumEntryAt source state
  targetEntryAt := nativeFluidMediumEntryAt source (source.successor state)
  rowAt
    | ⟨0, _⟩ =>
        (nativeFluidMediumWriteRowSource source).generate
          (.physical state occurrence)
    | ⟨1, _⟩ =>
        (nativeFluidMediumWriteRowSource source).generate
          (.operational state occurrence)

private def nativeFluidMediumCoverage
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (occurrence : NativeFluidMediumOccurrence source state) :
    LedgerCompleteFiniteCoverageAt
      (nativeFluidMediumRows source state occurrence) where
  destinationIndex := nativeFluidMediumEntryIndex
  originIndex := nativeFluidMediumEntryIndex
  destination_sound := nativeFluidMediumEntryAt_index source state
  origin_sound :=
    nativeFluidMediumEntryAt_index source (source.successor state)

private def nativeFluidMediumPatch
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (occurrence : NativeFluidMediumOccurrence source state) :
    FiniteGeneratedLedgerWritePatchAt
      (nativeFluidMediumWriteRowSource source)
      ⟨state, .actual state occurrence⟩
      ⟨source.successor state⟩ :=
  .complete
    (nativeFluidMediumRows source state occurrence)
    (nativeFluidMediumCoverage source state occurrence)

/-- Transparent compatibility readout of the same two finite generated rows.
Keeping this definition explicit makes the operational disposition visible
without unfolding the finite-patch dependent eliminator. -/
private def nativeFluidMediumLedgerEvolution
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (occurrence : NativeFluidMediumOccurrence source state) :
    LedgerWriteEvolutionAt (NativeFluidMediumNetwork source)
      ⟨state⟩ ⟨source.successor state⟩ where
  destination := by
    rintro ⟨responsibility, openAt⟩
    cases openAt with
    | physical _ =>
        exact ⟨nativeFluidMediumPhysicalEntry source (source.successor state),
          .transferred (.physicalAdvance occurrence) rfl rfl (Nat.zero_le 0)⟩
    | operational _ =>
        exact ⟨nativeFluidMediumOperationalEntry source (source.successor state),
          .transferred
            (nativeFluidMediumOperationalTransferReceipt source state)
            rfl rfl (Nat.zero_le 0)⟩
  origin := by
    rintro ⟨responsibility, openAt⟩
    cases openAt with
    | physical _ =>
        exact ⟨nativeFluidMediumPhysicalEntry source state,
          .transferred (.physicalAdvance occurrence) rfl rfl (Nat.zero_le 0)⟩
    | operational _ =>
        exact ⟨nativeFluidMediumOperationalEntry source state,
          .transferred
            (nativeFluidMediumOperationalTransferReceipt source state)
            rfl rfl (Nat.zero_le 0)⟩

private theorem nativeFluidMediumPatch_toLedgerWriteEvolution
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (occurrence : NativeFluidMediumOccurrence source state) :
    (nativeFluidMediumPatch source state occurrence).toLedgerWriteEvolution =
      nativeFluidMediumLedgerEvolution source state occurrence := by
  apply congrArg₂
    (fun destination origin =>
      ({ destination := destination, origin := origin } :
        LedgerWriteEvolutionAt (NativeFluidMediumNetwork source)
          ⟨state⟩ ⟨source.successor state⟩))
  · funext entry
    rcases entry with ⟨responsibility, openAt⟩
    cases openAt with
    | physical sourceOccurrence =>
        change NativeFluidMediumOccurrence source state at sourceOccurrence
        cases Subsingleton.elim sourceOccurrence
          (source.generateOccurrence state)
        rfl
    | operational sourceEffect =>
        change NativeFluidMediumExactOperationalEffectAt source state at sourceEffect
        cases Subsingleton.elim sourceEffect
          (nativeFluidMediumExactOperationalEffectAt source state)
        rfl
  · funext entry
    rcases entry with ⟨responsibility, openAt⟩
    cases openAt with
    | physical targetOccurrence =>
        change NativeFluidMediumOccurrence source (source.successor state) at targetOccurrence
        cases Subsingleton.elim targetOccurrence
          (source.generateOccurrence (source.successor state))
        rfl
    | operational targetEffect =>
        change NativeFluidMediumExactOperationalEffectAt source
          (source.successor state) at targetEffect
        cases Subsingleton.elim targetEffect
          (nativeFluidMediumExactOperationalEffectAt source
            (source.successor state))
        rfl

private def nativeFluidMediumTerminalRowSource
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    LedgerTerminalRowSourceAt (nativeFluidMediumSource source) :=
  LedgerTerminalRowSourceAt.empty _

private def nativeFluidMediumGeneratedLedgerEvolution
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    {state : source.State}
    (occurrence : (nativeFluidMediumSource source).toRootSource.actual.OccurrenceAt
      state) :
    SourceNativeLedgerEvolutionAt (nativeFluidMediumSource source) occurrence := by
  rcases occurrence with ⟨support, event⟩
  change NativeFluidMediumRootEventAt source state support at event
  cases event with
  | actual mediumOccurrence =>
      exact .nativeWrite mediumOccurrence rfl
        (nativeFluidMediumEmitted source (source.successor state))
        (nativeFluidMediumLedgerEvolution source state mediumOccurrence)

private def nativeFluidMediumLedgerCompiler
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeLedgerCompiler (nativeFluidMediumSource source) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ occurrence targetSupport sourceEntry targetEntry
    exact NativeFluidMediumExactTransitionAt occurrence sourceEntry targetEntry
  exact_incidence := by intro _ _ _ _ _ _; exact PUnit.unit
  exact_lineage := by intro _ _ _ _ _ _; rfl
  writeRowSource := nativeFluidMediumWriteRowSource source
  terminalRowSource := nativeFluidMediumTerminalRowSource source
  compile := nativeFluidMediumGeneratedLedgerEvolution source
  compilePatch := by
    intro state occurrence
    rcases occurrence with ⟨support, event⟩
    change NativeFluidMediumRootEventAt source state support at event
    cases event with
    | actual mediumOccurrence =>
        exact ⟨nativeFluidMediumPatch source state mediumOccurrence,
          nativeFluidMediumPatch_toLedgerWriteEvolution source state
            mediumOccurrence⟩

def nativeFluidMediumLedgerSource
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeLedgerSource (NativeFluidMediumNetwork source)
      (NativeFluidMediumVocabulary source) where
  source := nativeFluidMediumSource source
  ledgerCompiler := nativeFluidMediumLedgerCompiler source

private def nativeFluidMediumRestructuringLaw
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeLedgerRestructuringLaw (nativeFluidMediumSource source) :=
  identityOnlyWorldLedgerRestructuringLaw
    (nativeFluidMediumSource source) PUnit.unit
    (nativeFluidMediumOpenAt_subsingleton (source := source))

private def nativeFluidMediumRestructuringCertification
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    {state : source.State}
    (occurrence : (nativeFluidMediumSource source).toRootSource.actual.OccurrenceAt
      state) :
    SourceNativeLedgerRestructuringCertificationAt
      (nativeFluidMediumRestructuringLaw source)
      ((nativeFluidMediumLedgerCompiler source).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change NativeFluidMediumRootEventAt source state support at event
  cases event with
  | actual mediumOccurrence =>
      exact ExactLedgerRestructuringCertificationAt.ofInjective
        (by
          intro left right originEq
          rcases left with ⟨leftResponsibility, leftOpen⟩
          rcases right with ⟨rightResponsibility, rightOpen⟩
          cases leftOpen <;> cases rightOpen
          · exact nativeFluidMediumEntry_eq_of_responsibility_eq _ _ rfl
          · change
              nativeFluidMediumPhysicalEntry source state =
                nativeFluidMediumOperationalEntry source state at originEq
            have impossible :
                NativeFluidMediumResponsibility.physical =
                  NativeFluidMediumResponsibility.operational :=
              congrArg Sigma.fst originEq
            cases impossible
          · change
              nativeFluidMediumOperationalEntry source state =
                nativeFluidMediumPhysicalEntry source state at originEq
            have impossible :
                NativeFluidMediumResponsibility.operational =
                  NativeFluidMediumResponsibility.physical :=
              congrArg Sigma.fst originEq
            cases impossible
          · exact nativeFluidMediumEntry_eq_of_responsibility_eq _ _ rfl)
        (by
          intro left right destinationEq
          rcases left with ⟨leftResponsibility, leftOpen⟩
          rcases right with ⟨rightResponsibility, rightOpen⟩
          cases leftOpen <;> cases rightOpen
          · exact nativeFluidMediumEntry_eq_of_responsibility_eq _ _ rfl
          · change
              nativeFluidMediumPhysicalEntry source (source.successor state) =
                nativeFluidMediumOperationalEntry source
                  (source.successor state) at destinationEq
            have impossible :
                NativeFluidMediumResponsibility.physical =
                  NativeFluidMediumResponsibility.operational :=
              congrArg Sigma.fst destinationEq
            cases impossible
          · change
              nativeFluidMediumOperationalEntry source (source.successor state) =
                nativeFluidMediumPhysicalEntry source
                  (source.successor state) at destinationEq
            have impossible :
                NativeFluidMediumResponsibility.operational =
                  NativeFluidMediumResponsibility.physical :=
              congrArg Sigma.fst destinationEq
            cases impossible
          · exact nativeFluidMediumEntry_eq_of_responsibility_eq _ _ rfl)

private def nativeFluidMediumRestructuringCompiler
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeRestructuringLedgerCompiler
      (nativeFluidMediumSource source) where
  ledgerCompiler := nativeFluidMediumLedgerCompiler source
  restructuringLaw := nativeFluidMediumRestructuringLaw source
  certifyRestructuring := nativeFluidMediumRestructuringCertification source

private def nativeFluidMediumRestructuringSource
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeRestructuringLedgerSource (NativeFluidMediumNetwork source)
      (NativeFluidMediumVocabulary source) where
  source := nativeFluidMediumSource source
  compiler := nativeFluidMediumRestructuringCompiler source

/-! ## Same-occurrence medium and restriction faces -/

private def generatedMediumOccurrenceAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    {state : source.State}
    (occurrence : (nativeFluidMediumSource source).toRootSource.actual.OccurrenceAt
      state) : NativeFluidMediumOccurrence source state := by
  rcases occurrence with ⟨support, event⟩
  change NativeFluidMediumRootEventAt source state support at event
  cases event with
  | actual mediumOccurrence => exact mediumOccurrence

/-! ## Installed standing-valued arithmetic material -/

/-- Exact arithmetic material generated by one medium occurrence.  It is the
arithmetic projection of the complete operational effect, so a live standing
anchor cannot be replaced by the current scale readout. -/
def nativeFluidMediumArithmeticMaterialAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    {state : source.State}
    (_occurrence : NativeFluidMediumOccurrence source state) :
    RootArithmeticMaterialAt :=
  source.operationalArithmeticMaterialAt
    (source.operationalEffectAt state)

/-- The exact lower-root occurrence generates its own scale arithmetic
material before any cardinal or incidence readout is consumed. -/
def nativeFluidMediumArithmeticMaterialLaw
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeRootArithmeticMaterialLaw
      (nativeFluidMediumRestructuringSource source).toLedgerSource :=
  .create fun {_current} occurrence =>
    nativeFluidMediumArithmeticMaterialAt source
      (generatedMediumOccurrenceAt source occurrence)

private inductive NativeFluidMediumProjection
  | medium
  | classicalNS
  | constitutiveFlux
  | vorticityMass
  | mediumResidual
  | wholeRestriction
  | temporalLedger
  | patchContinuity
  | arithmetic

private def nativeFluidMediumProjectionLaw
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeProjectionLaw
      (nativeFluidMediumRestructuringSource source).toLedgerSource where
  Projection := NativeFluidMediumProjection
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .arithmetic =>
        (nativeFluidMediumArithmeticMaterialLaw source).toProjectionLaw.InactiveAt
          PUnit.unit occurrence
    | _ => PEmpty
  classify := fun projection {_current} occurrence =>
    match projection with
    | .arithmetic =>
        (nativeFluidMediumArithmeticMaterialLaw source).toProjectionLaw.classify
          PUnit.unit occurrence
    | _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence _ =>
    let medium := generatedMediumOccurrenceAt source occurrence
    match projection with
    | .medium => NativeFluidMediumOccurrence source _current
    | .classicalNS => ClassicalNSFourierReadout nu
    | .constitutiveFlux => NativeFluidVorticityTangent
    | .vorticityMass => Real
    | .mediumResidual => NativeFluidVorticityTangent
    | .wholeRestriction =>
        PLift <| medium.nativeVorticityTangent =
          classicalWholeNSVorticityTangent nu
              medium.toClassicalNS.vorticity + medium.mediumResidual
    | .temporalLedger =>
        PLift <| medium.potential - source.potentialAt (source.successor _current) =
          medium.clock * medium.density
    | .patchContinuity =>
        PLift <| ∀ patch : source.PatchAt _current,
          source.incomingBoundaryAt _current
              (source.advancePatch _current patch) =
            source.outgoingBoundaryAt _current patch
    | .arithmetic =>
        (nativeFluidMediumArithmeticMaterialLaw source).toProjectionLaw.PayloadAt
          PUnit.unit occurrence PUnit.unit
  project := by
    intro projection current occurrence _active
    let medium := generatedMediumOccurrenceAt source occurrence
    cases projection with
    | medium => exact medium
    | classicalNS => exact medium.toClassicalNS
    | constitutiveFlux => exact medium.constitutiveFlux
    | vorticityMass => exact medium.vorticityMass
    | mediumResidual => exact medium.mediumResidual
    | wholeRestriction =>
        exact ⟨medium.nativeVorticityTangent_eq_classical_add_mediumResidual⟩
    | temporalLedger => exact ⟨medium.potential_drop_eq_clock_mul_density⟩
    | patchContinuity =>
        exact ⟨fun patch => medium.generatedPatch_commutes patch⟩
    | arithmetic =>
        exact
          (nativeFluidMediumArithmeticMaterialLaw source).toProjectionLaw.project
            PUnit.unit occurrence PUnit.unit

/-- The arithmetic material law is an installed coordinate of the existing
medium projection inventory at the same exact occurrence. -/
def nativeFluidMediumArithmeticInstallation
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeProjectionLaw.InstallationAt
      (nativeFluidMediumArithmeticMaterialLaw source).toProjectionLaw
      (nativeFluidMediumProjectionLaw source) where
  embed := fun _ => .arithmetic
  embed_injective := by
    intro left right _equality
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    rfl

/-- Direct same-occurrence factorization of the generic arithmetic material
through the existing medium projection inventory. -/
theorem nativeFluidMediumArithmeticInstallation_factorizes
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    {current : source.State}
    (occurrence :
      (nativeFluidMediumSource source).toRootSource.actual.OccurrenceAt
        current) :
    HEq
      ((nativeFluidMediumProjectionLaw source).outcomeAt
        ((nativeFluidMediumArithmeticInstallation source).embed PUnit.unit)
        occurrence)
      ((nativeFluidMediumArithmeticMaterialLaw source).toProjectionLaw.outcomeAt
        PUnit.unit occurrence) :=
  (nativeFluidMediumArithmeticInstallation source).outcome_heq
    occurrence PUnit.unit

private def nativeFluidMediumAuthoritySource
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeAuthoritySource (NativeFluidMediumNetwork source)
      (NativeFluidMediumVocabulary source) where
  restructuringSource := nativeFluidMediumRestructuringSource source
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal (nativeFluidMediumRestructuringSource source)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (NativeFluidMediumNetwork source)
  projectionLaw := nativeFluidMediumProjectionLaw source

private def nativeFluidMediumAuthoritativeRoot
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeAuthoritativeRootClosure (NativeFluidMediumNetwork source)
      (NativeFluidMediumVocabulary source) where
  source := nativeFluidMediumAuthoritySource source
  emitted := nativeFluidMediumEmitted source
  compiler_commutes := by
    intro current
    change
      nativeFluidMediumEmitted source (source.successor current) =
        nativeFluidMediumEmitted source (source.successor current)
    rfl

/-- Living root whose actual source event is the complete fluid medium
occurrence.  Classical NS and both residual rows are projections of this
root, never predecessor authorities. -/
def nativeFluidMediumLivingRoot
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeLivingRootClosure (NativeFluidMediumNetwork source)
      (NativeFluidMediumVocabulary source) :=
  (nativeFluidMediumAuthoritativeRoot source).toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

/-- Whole-ledger disposition of the operational row at this exact source
state.  This reads the canonical root compiler image; it is not a projection
outcome or a second standing transition. -/
def nativeFluidMediumGeneratedOperationalDispositionAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    LedgerEntryDispositionAt (NativeFluidMediumNetwork source)
      (nativeFluidMediumOperationalEntry source state) :=
  ((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot
    ).generatedLedgerAt state |>.entryDisposition
      (nativeFluidMediumOperationalEntry source state)

/-- The public disposition is definitionally the operational entry read from
the canonical whole-ledger compiler image. -/
theorem nativeFluidMediumGeneratedOperationalDispositionAt_root_eq
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    nativeFluidMediumGeneratedOperationalDispositionAt source state =
      (((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot
        ).generatedLedgerAt state).entryDisposition
          (nativeFluidMediumOperationalEntry source state) :=
  rfl

/-- Eliminate the original operational row, rather than reading a parallel
projection, to recover its source-generated physical contact time. -/
def nativeFluidMediumGeneratedOperationalContactTime?
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) : Option Real :=
  match nativeFluidMediumGeneratedOperationalDispositionAt source state with
  | .evolved (.transferred receipt ..) =>
      nativeFluidMediumTransferContactTime? source state receipt
  | _ => none

theorem nativeFluidMediumGeneratedOperationalContactTime?_eq
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State) :
    nativeFluidMediumGeneratedOperationalContactTime? source state =
      some (nativeFluidMediumExactOperationalEffectAt source state).contactTime := by
  change nativeFluidMediumTransferContactTime? source state
      (nativeFluidMediumOperationalTransferReceipt source state) = _
  exact nativeFluidMediumOperationalTransferReceipt_contactTime source state

/-- Recognition that generic scale arithmetic is already installed inside
the existing medium living root.  It introduces no sibling root, scheduler,
or cross-occurrence transporter. -/
def nativeFluidMediumArithmeticMaterialRecognition
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeRootArithmeticIncidenceRecognitionAt
      (nativeFluidMediumLivingRoot source) where
  materialLaw := nativeFluidMediumArithmeticMaterialLaw source
  installation := nativeFluidMediumArithmeticInstallation source

/-! ## Source/action recursive root process -/

/-- Canonical causal visit at one generated medium depth.  A lawful
recurrence may revisit a medium state only through this fresh root history. -/
def nativeFluidMediumRootVisit
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) : Nat →
      RootVisit
        (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toRoot
  | 0 =>
      (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toRoot.initialVisit
  | index + 1 => (nativeFluidMediumRootVisit source index).next rfl

@[simp] theorem nativeFluidMediumRootVisit_current
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (index : Nat) :
    (nativeFluidMediumRootVisit source index).current =
      source.stateAfter index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        source.successor (nativeFluidMediumRootVisit source index).current =
          source.successor (source.stateAfter index)
      rw [inductionHypothesis]

private def nativeFluidMediumFiniteDepth?
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (current : SourceNativeLivingRootCurrentAt
      (NativeFluidMediumNetwork source)) :
    Option Nat :=
  match current.visit.history with
  | .finite history =>
      some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem nativeFluidMediumRootVisit_depth
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (index : Nat) :
    nativeFluidMediumFiniteDepth?
        ⟨NativeFluidMediumVocabulary source,
          nativeFluidMediumLivingRoot source,
          .finite (nativeFluidMediumRootVisit source index)⟩ =
      some index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        some
            (ProductiveFiniteRootHistoryAt.causalDepth
                (nativeFluidMediumRootVisit source index).history + 1) =
          some (index + 1)
      have priorDepth :
          ProductiveFiniteRootHistoryAt.causalDepth
              (nativeFluidMediumRootVisit source index).history = index := by
        change
          some
              (ProductiveFiniteRootHistoryAt.causalDepth
                (nativeFluidMediumRootVisit source index).history) =
            some index at inductionHypothesis
        exact Option.some.inj inductionHypothesis
      rw [priorDepth]

def nativeFluidMediumLivingProcess
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeLivingRootProcess (NativeFluidMediumNetwork source) where
  State := Nat
  stateAt := fun index =>
    ⟨NativeFluidMediumVocabulary source,
      nativeFluidMediumLivingRoot source,
      .finite (nativeFluidMediumRootVisit source index)⟩
  stateAt_injective := by
    intro left right equality
    have depthEq := congrArg nativeFluidMediumFiniteDepth? equality
    rw [nativeFluidMediumRootVisit_depth source left,
      nativeFluidMediumRootVisit_depth source right] at depthEq
    exact Option.some.inj depthEq
  initial := 0
  successorAt := fun index => ⟨index + 1, rfl, by rfl⟩

/-- The operational row is canonically admitted at the exact initial root
occurrence. -/
def nativeFluidMediumInitialOperationalGeneratedEntryRow
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    (((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot
      ).generatedAtTemporalVisit
        (.finite
          ((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toRoot
            ).initialVisit)).GeneratedEntryRowAt
      (nativeFluidMediumOperationalEntry source source.initial) :=
  ((((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot
      ).generatedAtTemporalVisit
        (.finite
          ((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toRoot
            ).initialVisit)).canonicalGeneratedEntryRow?
      (nativeFluidMediumOperationalEntry source source.initial)).get (by rfl)

def nativeFluidMediumInitialOperationalCausalEntryAuthority
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (nativeFluidMediumLivingRoot source)
      (.finite
        ((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toRoot
          ).initialVisit)
      (nativeFluidMediumOperationalEntry source source.initial) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (nativeFluidMediumLivingRoot source)
    (nativeFluidMediumOperationalEntry source source.initial)
    (nativeFluidMediumInitialOperationalGeneratedEntryRow source)

/-- Operational-row authority follows exactly the fixed root history.  The
target row is selected by the compiler's complete two-row ledger, never by a
parallel standing registry. -/
private def nativeFluidMediumOperationalCausalEntryAuthorityAtHistory
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    {state : source.State}
    (history :
      ((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toRoot
        ).ReachableAt state) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (nativeFluidMediumLivingRoot source)
      (.finite ⟨state, history⟩)
      (nativeFluidMediumOperationalEntry source state) :=
  match history with
  | .initial => nativeFluidMediumInitialOperationalCausalEntryAuthority source
  | @RootClosure.ReachableAt.step _ _ _ current next prior nextEq => by
      let generated :=
        (nativeFluidMediumOperationalCausalEntryAuthorityAtHistory source prior
          ).next nextEq
      have nextStateEq : next = source.successor current := by
        change some (source.successor current) = some next at nextEq
        exact (Option.some.inj nextEq).symm
      subst next
      have entryEq :
          ((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot
              ).canonicalTargetEntryAtNext nextEq
                (nativeFluidMediumOperationalEntry source current) =
            nativeFluidMediumOperationalEntry source
              (source.successor current) := by
        apply nativeFluidMediumEntry_eq_of_responsibility_eq
        change NativeFluidMediumResponsibility.operational =
          NativeFluidMediumResponsibility.operational
        rfl
      exact entryEq ▸ generated

def nativeFluidMediumOperationalCausalEntryAuthorityAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (stage : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (nativeFluidMediumLivingRoot source)
      (.finite (nativeFluidMediumRootVisit source stage))
      (nativeFluidMediumOperationalEntry source
        (nativeFluidMediumRootVisit source stage).current) :=
  nativeFluidMediumOperationalCausalEntryAuthorityAtHistory source
    (nativeFluidMediumRootVisit source stage).history

/-- Obstruction-only answer-and-next readout of one total root outcome.  `none`
means the exact source outcome was paid or a same-row generated residual;
`some` contains both the U7 demand seal and the living root's canonical next
current. -/
def NativeFluidMediumRootOperationalOutcomeAt.obstructionAnswerAndNext?
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {stage : Nat}
    (outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (nativeFluidMediumRootVisit source stage).current) :
    Option (Sigma fun obstruction :
        NativeFluidMediumOperationalObstructionAt source
          (nativeFluidMediumRootVisit source stage).current =>
      SourceGeneratedU7DemandAt (nativeFluidMediumU7Producer source)
          obstruction
          ((nativeFluidMediumU7Producer source).generateDemand obstruction) ×
        SourceNativeLivingCausalEntryAnswerAndNextAt
          (nativeFluidMediumLivingRoot source)
          (.finite (nativeFluidMediumRootVisit source stage))
          (nativeFluidMediumOperationalEntry source
            (nativeFluidMediumRootVisit source stage).current)
          (nativeFluidMediumOperationalCausalEntryAuthorityAt source stage)) :=
  match outcome with
  | .exactPayment _ _ _ => none
  | .generatedResidual _ _ _ _ _ => none
  | NativeFluidMediumRootOperationalOutcomeAt.obstruction obstructionValue demand =>
      some ⟨obstructionValue, demand,
        (nativeFluidMediumLivingRoot source).generatedCausalEntryAnswerAndNextAt
          (.finite (nativeFluidMediumRootVisit source stage))
          (nativeFluidMediumOperationalEntry source
            (nativeFluidMediumRootVisit source stage).current)
          (nativeFluidMediumOperationalCausalEntryAuthorityAt source stage)⟩

def nativeFluidMediumRootOperationalAnswerAndNextAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (stage : Nat) :=
  (nativeFluidMediumRootOperationalOutcomeAt source
      (nativeFluidMediumRootVisit source stage).current
    ).obstructionAnswerAndNext?

/-- The root process recursively closes the complete operational disposition,
not a selected paid subtype.  Paid, generated-residual and obstruction rows
are all emitted by the same source transition and keep the compiler-owned
next current. -/
def nativeFluidMediumTotalDispositionInvariantLaw
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeGeneratedInvariantLaw
      (nativeFluidMediumLivingProcess source) :=
  SourceNativeGeneratedInvariantLaw.create
    (process := nativeFluidMediumLivingProcess source)
    (InvariantAt := fun (index : Nat) =>
      ({ disposition : LedgerEntryDispositionAt
            (NativeFluidMediumNetwork source)
            (nativeFluidMediumOperationalEntry source
              (source.stateAfter index)) //
          disposition =
            nativeFluidMediumGeneratedOperationalDispositionAt source
              (source.stateAfter index) }) ×
        NativeFluidMediumRootOperationalOutcomeAt source
          (source.stateAfter index))
    (initialAt :=
      ⟨⟨nativeFluidMediumGeneratedOperationalDispositionAt source
          source.initial, rfl⟩,
        nativeFluidMediumRootOperationalOutcomeAt source source.initial⟩)
    (advanceAt := fun (index : Nat) _closed =>
      ⟨⟨nativeFluidMediumGeneratedOperationalDispositionAt source
          (source.stateAfter (index + 1)), rfl⟩,
        nativeFluidMediumRootOperationalOutcomeAt source
          (source.stateAfter (index + 1))⟩)

def nativeFluidMediumTotalDispositionHistory
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeGeneratedInvariantHistoryAt
      (nativeFluidMediumTotalDispositionInvariantLaw source) :=
  (nativeFluidMediumTotalDispositionInvariantLaw source).generateHistory

@[simp] theorem nativeFluidMediumLivingProcess_stateAfter
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (index : Nat) :
    (nativeFluidMediumLivingProcess source).stateAfter index = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (nativeFluidMediumLivingProcess source).successor
            ((nativeFluidMediumLivingProcess source).stateAfter index) =
          index + 1
      rw [inductionHypothesis]
      rfl

/-- The medium patch row is installed in the framework's generated
continuity calculus.  Only the initial patch, one local advance and its local
restriction are retained; the whole compatible family is generated by the
fixed living-root process. -/
def nativeFluidMediumGeneratedContinuityLaw
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeGeneratedContinuityLaw
      (nativeFluidMediumLivingProcess source) :=
  SourceNativeGeneratedContinuityLaw.create
    (process := nativeFluidMediumLivingProcess source)
    (PatchAt := fun index => source.PatchAt (source.stateAfter index))
    (initialAt := source.initialPatch)
    (advanceAt := fun index patch =>
      source.advancePatch (source.stateAfter index) patch)
    (restrictAt := fun index patch =>
      source.restrictPatch (source.stateAfter index) patch)
    (advance_restricts := fun index patch =>
      source.advance_restricts (source.stateAfter index) patch)

def nativeFluidMediumGeneratedContinuum
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) :
    SourceNativeGeneratedContinuumAt
      (nativeFluidMediumGeneratedContinuityLaw source) :=
  (nativeFluidMediumGeneratedContinuityLaw source).generate

/-- The recursively generated process retains exact adjacent restriction at
every causal visit. -/
theorem nativeFluidMediumLivingProcess_patch_restricts
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (index : Nat) :
    let law := nativeFluidMediumGeneratedContinuityLaw source
    let continuum := nativeFluidMediumGeneratedContinuum source
    law.restrictAt
        ((nativeFluidMediumLivingProcess source).stateAfter index)
        (continuum.patchAt (index + 1)) =
      continuum.patchAt index := by
  exact (nativeFluidMediumGeneratedContinuum source).restrict_succ_eq index

/-- Adjacent generated patches sit on the exact next current of the same
medium living root; the continuum has no independent scheduler. -/
theorem nativeFluidMediumLivingProcess_continuity_succ_is_generated
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (index : Nat) :
    let continuum := nativeFluidMediumGeneratedContinuum source
    (continuum.currentAt index).IsGeneratedSuccessor
      (continuum.currentAt (index + 1)) := by
  exact
    (nativeFluidMediumGeneratedContinuum source).current_succ_is_generated index

/-- Concrete faithful Newtonian baseline root generated from the existing
whole-restart process. -/
def classicalWholeRestartMediumLivingRoot
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :=
  nativeFluidMediumLivingRoot (classicalWholeRestartMediumSource initial)

@[simp] theorem classicalWholeRestartMediumSource_stateAfter
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    (classicalWholeRestartMediumSource initial).stateAfter stage =
      runRuntime initial stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      change
        ((classicalWholeRestartMediumSource initial).stateAfter stage).next =
          (runRuntime initial stage).next
      rw [inductionHypothesis]

/-- The operational root payload is literally the complete standing-valued
material emitted from the actual runtime occurrence. -/
theorem classicalWholeRestartRootMaterial_eq_runStandingValuedMaterial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    HEq (nativeFluidMediumExactOperationalEffectAt
      (classicalWholeRestartMediumSource initial)
      ((classicalWholeRestartMediumSource initial).stateAfter stage)).effect
        (nativeRestartStandingValuedArithmeticMaterial
          (runStandingCellEffect initial stage)) := by
  rw [classicalWholeRestartMediumSource_stateAfter]
  rfl

theorem classicalWholeRestartRootNormalForm_heq_runStandingValuedNormalForm
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    HEq
      (nativeFluidMediumExactOperationalEffectAt
        (classicalWholeRestartMediumSource initial)
        ((classicalWholeRestartMediumSource initial).stateAfter stage)
        ).parallelNormalForm
      (nativeRestartStandingValuedArithmeticMaterial
        (runStandingCellEffect initial stage)).parallelNormalForm := by
  rw [classicalWholeRestartMediumSource_stateAfter]
  rfl

theorem classicalWholeRestartOperationalEffect_netEnstrophyDebit_eq_runCellEffect
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt
      (classicalWholeRestartMediumSource initial)
      ((classicalWholeRestartMediumSource initial).stateAfter stage)) :
    effect.netEnstrophyDebit =
      (runCellEffect initial stage).debit.netEnstrophyDebit := by
  cases Subsingleton.elim effect
    (nativeFluidMediumExactOperationalEffectAt
      (classicalWholeRestartMediumSource initial)
      ((classicalWholeRestartMediumSource initial).stateAfter stage))
  unfold NativeFluidMediumExactOperationalEffectAt.netEnstrophyDebit
  rw [classicalWholeRestartMediumSource_stateAfter]
  rfl

/-- Requested direct splice: the actual run effect, exact whole-ledger
disposition and compiler-owned next current are the same root occurrence. -/
theorem classicalWholeRestart_runStandingEffect_rootStep_factorizes
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    let source := classicalWholeRestartMediumSource initial
    let visit : SourceNativeTemporalVisitAt
        (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot :=
      .finite (nativeFluidMediumRootVisit source stage)
    HEq (nativeFluidMediumExactOperationalEffectAt source
        (source.stateAfter stage)).effect
          (nativeRestartStandingValuedArithmeticMaterial
            (runStandingCellEffect initial stage)) ∧
      nativeFluidMediumGeneratedOperationalDispositionAt source
          (source.stateAfter stage) =
        (((nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot
          ).generatedLedgerAt (source.stateAfter stage)).entryDisposition
            (nativeFluidMediumOperationalEntry source
              (source.stateAfter stage)) ∧
      ((nativeFluidMediumLivingRoot source).generatedNextCurrentAt visit
        ).visit.current = source.stateAfter (stage + 1) := by
  dsimp only
  refine ⟨classicalWholeRestartRootMaterial_eq_runStandingValuedMaterial
      initial stage,
    nativeFluidMediumGeneratedOperationalDispositionAt_root_eq _ _, ?_⟩
  change
    (classicalWholeRestartMediumSource initial).successor
        (nativeFluidMediumRootVisit
          (classicalWholeRestartMediumSource initial) stage).current =
      (classicalWholeRestartMediumSource initial).successor
        ((classicalWholeRestartMediumSource initial).stateAfter stage)
  rw [nativeFluidMediumRootVisit_current]

theorem classicalWholeRestartOperationalObstruction_netEnstrophyDebit_nonpos
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (obstruction : NativeFluidMediumOperationalObstructionAt
      (classicalWholeRestartMediumSource initial)
      ((classicalWholeRestartMediumSource initial).stateAfter stage)) :
    (runCellEffect initial stage).debit.netEnstrophyDebit ≤ 0 := by
  rw [classicalWholeRestartMediumSource_stateAfter] at obstruction
  rcases obstruction with
    ⟨effect, residual, expansion, expansionEq, nonpositive,
      _expansionNonpositive⟩
  unfold NativeFluidMediumExactOperationalEffectAt.netEnstrophyDebit
    at nonpositive
  rw [effect.effect_eq] at nonpositive
  exact nonpositive

theorem classicalWholeRestartOperationalObstruction_targetMass_le_sourceMass
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat)
    (obstruction : NativeFluidMediumOperationalObstructionAt
      (classicalWholeRestartMediumSource initial)
      ((classicalWholeRestartMediumSource initial).stateAfter stage)) :
    wholeVorticityEuclideanMass
        (runCellEffect initial stage).debit.targetPhysicalState ≤
      wholeVorticityEuclideanMass
        (runCellEffect initial stage).debit.sourcePhysicalState := by
  have nonpositive :=
    classicalWholeRestartOperationalObstruction_netEnstrophyDebit_nonpos
      initial stage obstruction
  rw [← sub_nonpos,
    ← (runCellEffect initial stage).debit.netEnstrophyDebit_eq]
  exact nonpositive

end

end ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
end NavierStokes
end SaturationMonoid
