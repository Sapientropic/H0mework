import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.LivingLawAtomFieldSeparation

/-!
# Focused atom-field separation regression

The positive fixture proves that one source-owned living-law write generates an
authoritative local section at every finite depth and that restriction keeps
the same source account.  The negative fixture registers a pointwise temporal
field and proves that naked future-tail shift cannot obtain the required
living-law surface recognition.  A pointwise local map on the same infinite
function space remains accepted, so the regression rejects temporal
target-smuggling rather than infinite ambient mathematics.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawAtomFieldSeparationRegression

open ResidualProjection
open EffectiveResidualUpdate
open LivingLawEvolution

noncomputable section

/-! ## Reusable P68 presentations -/

universe u

def constantCover (Ambient : Type u) :
    SectionIndexedCover Nat Ambient (fun _ => Ambient)
      (fun _ _ => Ambient) where
  toLocal := fun _ value => value
  leftToOverlap := fun _ _ value => value
  rightToOverlap := fun _ _ value => value
  glue := fun family => family 0

theorem constantDescent (Ambient : Type u) :
    SectionDescentCertificate (constantCover Ambient) where
  globalCompatible := by
    intro value left right
    rfl
  glueRestricts := by
    intro family compatible index
    exact compatible 0 index
  glueUnique := by
    intro family compatible value restricts
    exact restricts 0

def constantPresentation (Ambient : Type u) :
    AtomFieldPresentation Ambient where
  Local := fun _ => Ambient
  Overlap := fun _ _ => Ambient
  cover := constantCover Ambient
  descent := constantDescent Ambient

/-- A constant chart exposes the whole ambient object already at scope zero. -/
def constantPresentation_completedAmbientAtZero (Ambient : Type u) :
    (constantPresentation Ambient).CompletedAmbientAt 0 where
  recover := fun finite => finite ⟨0, Nat.zero_lt_succ 0⟩
  recover_restrict := fun _ => rfl

/-- Consequently a constant chart is not a proper finite-field presentation.
It may describe one atomic value, but it cannot certify that a completed
ambient field was generated section by section. -/
theorem constantPresentation_notProper (Ambient : Type u) :
    IsEmpty (constantPresentation Ambient).ProperFiniteSections := by
  constructor
  intro proper
  exact (proper.noCompletedAmbient 0).false
    (constantPresentation_completedAmbientAtZero Ambient)

/-! ## Positive: one actual write generates every finite local section -/

def effectiveProcess : EffectiveResidualProcess ℚ ℚ ℚ where
  target := 0
  keep := LinearMap.id
  residual := fun _ => 0
  update := fun state => state + 1
  residual_transport_law := by
    intro state
    rfl

def carrier : Carrier (K := ℚ) (E := ℚ) where
  LawSurface := Unit
  State := fun _ => ℚ
  process := fun _ => effectiveProcess
  Scope := Unit
  Lineage := Unit
  Incidence := Nat
  Bearer := Unit
  LawLineage := Nat
  SourceObservation := ComplementObservation.canonicalComplementPair

abbrev C := carrier

def vocabulary : LivingLawEvolution.Vocabulary C where
  ActualEventAt := fun _ => Unit
  eventAnchor := fun {current} _ => current.anchor
  eventIncidence := fun {current} _ => current.incidence
  eventLawLineage := fun {current} _ => current.lawLineage
  eventNextBearer := fun {current} _ => current.bearer
  RouteAcceptedAt := fun _ _ _ => Unit
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => Unit
  ContinuedTransportAt := fun _ => Unit
  BorromeanRedirectAt := fun _ => Unit
  TerminalEventAt := fun _ => Unit
  terminalEventAnchor := fun {current} _ => current.anchor
  terminalEventIncidence := fun {current} _ => current.incidence
  terminalEventLawLineage := fun {current} _ => current.lawLineage
  CompleteActualDescentAt := fun _ => Unit
  FaithfulTerminalReceiptAt := fun _ => Unit
  LawObstructionAt := fun _ => Unit
  ProducerDemandAt := fun _ => Unit
  ExtensionEventAt := fun _ => Unit
  extensionEventAnchor := fun {current} _ => current.anchor
  extensionEventIncidence := fun {current} _ => current.incidence
  extensionEventLawLineage := fun {current} _ => current.lawLineage
  ExtensionRouteAcceptedAt := fun _ _ _ => Unit
  ExtensionDemandPaidAt := fun {_current} _ _ _ {_revised} _ => Unit
  LawRevisionAt := fun _ _ _ _ => Unit

abbrev V := vocabulary

def current : LivingLawEvolution.Current C where
  surface := ()
  residual := residualState effectiveProcess 0
  anchor := MinimalRegistrableSourceAnchor.canonical () ()
  incidence := (7 : Nat)
  bearer := ()
  lawLineage := (11 : Nat)

def write (source : LivingLawEvolution.Current C) :
    LivingLawEvolution.GeneratedWriteAt V source where
  event := ()
  event_anchor_eq := rfl
  event_incidence_eq := rfl
  event_lawLineage_eq := rfl
  update_ne_source := by
    cases source with
    | mk surface residual anchor incidence bearer lawLineage =>
        cases surface
        let state : ℚ := residual.state
        change effectiveProcess.update state ≠ state
        simp only [effectiveProcess]
        linarith
  bearerDisposition := .retained rfl

def total : LivingLawEvolution.FixedLawNativeTotal V where
  write := write
  native := fun _ => ()

def registry : CarrierAtomFieldRegistry C where
  state := fun _ => constantPresentation ℚ
  residual := fun _ => constantPresentation ℚ

def updateLocal : PrefixLocalMap (constantPresentation ℚ)
    (constantPresentation ℚ) effectiveProcess.update where
  localStep := fun scope finite =>
    by
      change (Fin (scope + 1) -> ℚ) at finite
      change ℚ
      exact finite ⟨0, Nat.zero_lt_succ scope⟩ + 1
  commutes := fun _ _ => rfl

def residualLocal : PrefixLocalMap (constantPresentation ℚ)
    (constantPresentation ℚ) effectiveProcess.residual where
  localStep := fun _ _ => show ℚ from 0
  commutes := fun _ _ => rfl

def keepLocal : PrefixLocalMap (constantPresentation ℚ)
    (constantPresentation ℚ) effectiveProcess.keep where
  localStep := fun scope finite =>
    by
      change (Fin (scope + 1) -> ℚ) at finite
      change ℚ
      exact finite ⟨0, Nat.zero_lt_succ scope⟩
  commutes := fun _ _ => rfl

def recognition : CarrierAtomFieldRecognition C registry where
  surface := fun _ =>
    { update_local := updateLocal
      residual_local := residualLocal
      keep_local := keepLocal }

theorem every_finite_scope_is_source_backed
    (scope : Nat) :
    ∃ localSection : GeneratedLocalSectionAt total recognition current scope,
      satisfiesC1 localSection.temporalSection ∧
        localSection.generated.target.anchor = current.anchor ∧
        localSection.generated.target.incidence = current.incidence ∧
        localSection.generated.target.lawLineage = current.lawLineage := by
  let localSection := total.generatedLocalSection recognition current scope
  exact ⟨localSection, localSection.sourceBacked,
    localSection.target_anchor_eq, localSection.target_incidence_eq,
    localSection.target_lawLineage_eq⟩

theorem arbitrary_finite_state_is_generated_by_the_same_write
    (scope : Nat) :
    let localSection := total.generatedFieldReadout recognition current scope
    HEq localSection.generated.target.residual.state
      ((Carrier.generatedTimeField C current).stateAt scope) := by
  exact (total.generatedFieldReadout recognition current scope).target_state_eq_generatedField

theorem finite_sections_are_exact_compiler_images
    (scope : Nat) :
    let localSection := total.generatedLocalSection recognition current scope
    localSection.stateSection =
        (registry.state
          localSection.generated.target.surface).cover.toLocal
            scope localSection.generated.target.residual.state ∧
      localSection.residualSection =
        (registry.residual
          localSection.generated.target.surface).cover.toLocal
            scope localSection.generated.target.residual.value := by
  exact ⟨(total.generatedLocalSection recognition current scope).stateSection_eq,
    (total.generatedLocalSection recognition current scope).residualSection_eq⟩

theorem restriction_does_not_increase_authority
    {smaller larger : Nat} (within : smaller <= larger) :
    let localSection := total.generatedLocalSection recognition current larger
    restrictSection localSection.temporalSection
        (localSection.restrict smaller within).temporalSection.scope (by
          intro index index_le_smaller
          exact index_le_smaller.trans within) =
      (localSection.restrict smaller within).temporalSection := by
  exact (total.generatedLocalSection recognition current larger).section_restrict_eq
    within

/-! ## Negative: a completed future tail cannot be the current atom -/

abbrev FutureTail (A : Type u) := Nat -> A

def pointwiseCover (A : Type u) :
    SectionIndexedCover Nat (FutureTail A) (fun _ => A)
      (fun _ _ => PUnit) where
  toLocal := fun index tail => tail index
  leftToOverlap := fun _ _ _ => PUnit.unit
  rightToOverlap := fun _ _ _ => PUnit.unit
  glue := fun family index => family index

theorem pointwiseDescent (A : Type u) :
    SectionDescentCertificate (pointwiseCover A) where
  globalCompatible := by
    intro tail left right
    rfl
  glueRestricts := by
    intro family compatible index
    rfl
  glueUnique := by
    intro family compatible tail restricts
    funext index
    exact restricts index

def pointwisePresentation (A : Type u) : AtomFieldPresentation (FutureTail A) where
  Local := fun _ => A
  Overlap := fun _ _ => PUnit
  cover := pointwiseCover A
  descent := pointwiseDescent A

def shift {A : Type u} (tail : FutureTail A) : FutureTail A :=
  fun index => tail (index + 1)

def constantTail {A : Type u} (value : A) : FutureTail A := fun _ => value

def changedAtOne {A : Type u} (base changed : A) : FutureTail A :=
  fun index => if index = 1 then changed else base

/-- Change the first coordinate strictly beyond a selected finite prefix. -/
def changedAfter {A : Type u} (scope : Nat) (base changed : A) : FutureTail A :=
  fun index => if index = scope + 1 then changed else base

/-- A pointwise temporal presentation is genuinely finite: no finite prefix
can reconstruct the whole ambient tail when the coordinate type has two
distinct values. -/
def pointwisePresentation_proper
    {A : Type u} (base changed : A) (distinct : base ≠ changed) :
    (pointwisePresentation A).ProperFiniteSections where
  noCompletedAmbient := by
    intro scope
    constructor
    intro completed
    let left : FutureTail A := constantTail base
    let right : FutureTail A := changedAfter scope base changed
    have restrict_eq :
        (pointwisePresentation A).restrict left scope =
          (pointwisePresentation A).restrict right scope := by
      funext index
      rcases index with ⟨index, index_lt⟩
      change left index = right index
      simp only [left, right, constantTail, changedAfter]
      split
      · rename_i index_eq
        omega
      · rfl
    have ambient_eq : left = right := by
      calc
        left = completed.recover
            ((pointwisePresentation A).restrict left scope) :=
          (completed.recover_restrict left).symm
        _ = completed.recover
            ((pointwisePresentation A).restrict right scope) := by
          rw [restrict_eq]
        _ = right := completed.recover_restrict right
    have coordinate_eq := congrFun ambient_eq (scope + 1)
    exact distinct (by
      simpa [left, right, constantTail, changedAfter] using coordinate_eq)

theorem shift_not_prefixLocal
    {A : Type u} (base changed : A) (distinct : base ≠ changed) :
    IsEmpty
      (PrefixLocalMap (pointwisePresentation A) (pointwisePresentation A)
        shift) := by
  constructor
  intro locality
  have sectionsEqual :
      (pointwisePresentation A).restrict (constantTail base) 0 =
        (pointwisePresentation A).restrict (changedAtOne base changed) 0 := by
    funext index
    rcases index with ⟨index, index_lt⟩
    cases index with
    | zero =>
        simp [AtomFieldPresentation.restrict, pointwisePresentation,
          pointwiseCover, constantTail, changedAtOne]
    | succ index =>
        nomatch index_lt
  have sameOutput := locality.eq_at_of_restrict_eq sectionsEqual
  change base = changed at sameOutput
  exact distinct sameOutput

/-- Pure atom/field negative control before the linear living-law fixture.  The
generic recognition theorem is audited separately from this concrete P68
presentation's Mathlib implementation dependencies. -/
theorem completed_bool_future_shift_is_rejected :
    IsEmpty
      (PrefixLocalMap (pointwisePresentation Bool) (pointwisePresentation Bool)
        shift) :=
  shift_not_prefixLocal false true (by intro equality; nomatch equality)

def shiftLinear : FutureTail ℚ →ₗ[ℚ] FutureTail ℚ where
  toFun := shift
  map_add' := by
    intro left right
    funext index
    rfl
  map_smul' := by
    intro scalar tail
    funext index
    rfl

-- `shiftLinear` is needed only as a linear keep for the living-law fixture.
-- The locality contradiction below is already carried by its underlying map.
def futureProcess : EffectiveResidualProcess ℚ (FutureTail ℚ) (FutureTail ℚ) where
  target := 0
  keep := shiftLinear
  residual := id
  update := shift
  residual_transport_law := fun _ => rfl

def futureCarrier : Carrier (K := ℚ) (E := FutureTail ℚ) where
  LawSurface := Unit
  State := fun _ => FutureTail ℚ
  process := fun _ => futureProcess
  Scope := Unit
  Lineage := Unit
  Incidence := Unit
  Bearer := Unit
  LawLineage := Unit
  SourceObservation := ComplementObservation.canonicalComplementPair

def futureRegistry : CarrierAtomFieldRegistry futureCarrier where
  state := fun _ => pointwisePresentation ℚ
  residual := fun _ => pointwisePresentation ℚ

/-- The registered pointwise field exposes the layer inversion: its update is
the forbidden shift, so the living-law surface recognition is uninhabited. -/
theorem future_tail_shift_has_no_living_surface_recognition :
    IsEmpty
      (SurfaceAtomFieldRecognition futureCarrier futureRegistry ()) := by
  constructor
  intro recognition
  have updateLocal := recognition.update_local
  change PrefixLocalMap (pointwisePresentation ℚ) (pointwisePresentation ℚ)
    shift at updateLocal
  exact (shift_not_prefixLocal (0 : ℚ) 1 zero_ne_one).false updateLocal

/-- The pointwise registry exposes the layer inversion directly: changing the
presentation would be a different readout, not a source authority operation. -/
theorem pointwise_registry_rejects_future_tail_shift :
    IsEmpty
      (CarrierAtomFieldRecognition futureCarrier futureRegistry) := by
  constructor
  intro recognition
  have surface := recognition.surface ()
  exact future_tail_shift_has_no_living_surface_recognition.false surface

/-! ## Lookalike control: infinite ambient carriers remain legal when local -/

def pointwiseIncrement (field : FutureTail ℚ) : FutureTail ℚ :=
  fun index => field index + 1

def pointwiseIncrement_prefixLocal :
    PrefixLocalMap (pointwisePresentation ℚ) (pointwisePresentation ℚ)
      pointwiseIncrement where
  localStep := fun scope finite =>
    by
      change (Fin (scope + 1) -> ℚ) at finite
      change ℚ
      exact finite ⟨scope, Nat.lt_succ_self scope⟩ + 1
  commutes := by
    intro field scope
    rfl

end
end LivingLawAtomFieldSeparationRegression
end ResponsibilityLifecycle
end SaturationMonoid
