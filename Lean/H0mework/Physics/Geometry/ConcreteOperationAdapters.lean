import H0mework.Physics.Gauge.RawGaugeSymmetry
import H0mework.Physics.Geometry.RawSectionGluing
import H0mework.Physics.Admission.StandingPullback
import H0mework.Physics.Admission.RawTemporalStanding
import H0mework.Physics.Admission.RawAuthorityStanding
import H0mework.Physics.Geometry.RawAffineScaleValidity
import H0mework.Realization.Descent.P260
import H0mework.Physics.ColorLoops.P348

/-!
# Concrete adapters for existing gauge and transition operations

The raw reconstruction deliberately did not consume certified `MulAction` or
descent structures.  This module now proves that two existing concrete
operations land in the positive raw-law region:

* P348 `SU(3)` conjugation on color-loop matrices with the trace observable;
* pointwise exact group-valued transitions from P260 combined with the raw
  identity section cover.

These are theorem-producing adapters.  They do not add proof fields to the raw
state and do not claim a concrete SU(7) source or a smooth principal bundle.
-/

namespace SaturationMonoid
namespace PhysicsCore

open StandardModelConstraint
open AffineRelaxation

/-! ## Raw source-code to concrete color-loop field -/

/-- Generate the P348 diagonal color-loop presentation from raw natural
source codes.  Unlike `primeEdgeColorLoopMatrix`, this map requires no
`PrimeExponent` or atom-coverage premise. -/
def rawCodeColorLoopMatrix
    (n leftCode rightCode : Nat) : ColorLoopField :=
  Matrix.diagonal fun i : Fin 3 =>
    if i = (0 : Fin 3) then (leftCode : ℂ)
    else if i = (1 : Fin 3) then (rightCode : ℂ)
    else -((2 * n : Nat) : ℂ)

theorem rawCodeColorLoop_trace_eq
    (n leftCode rightCode : Nat) :
    colorLoopTrace (rawCodeColorLoopMatrix n leftCode rightCode) =
      (leftCode : ℂ) + (rightCode : ℂ) - ((2 * n : Nat) : ℂ) := by
  simp [colorLoopTrace, rawCodeColorLoopMatrix, Matrix.trace,
    Fin.sum_univ_three]
  ring

theorem rawCodeColorLoop_trace_zero_iff
    (n leftCode rightCode : Nat) :
    colorLoopTrace (rawCodeColorLoopMatrix n leftCode rightCode) = 0 ↔
      2 * n = leftCode + rightCode := by
  rw [rawCodeColorLoop_trace_eq]
  constructor
  · intro hzero
    have hcast :
        (((leftCode + rightCode : Nat) : ℂ)) = ((2 * n : Nat) : ℂ) := by
      norm_num at hzero ⊢
      linear_combination hzero
    exact_mod_cast hcast.symm
  · intro hbalance
    rw [hbalance]
    norm_num

theorem rawCodeColorLoop_traceExact_iff_balance
    (n leftCode rightCode : Nat) :
    ColorLoopTraceExact (rawCodeColorLoopMatrix n leftCode rightCode) ↔
      2 * n = leftCode + rightCode := by
  exact rawCodeColorLoop_trace_zero_iff n leftCode rightCode

theorem rawCodeColorLoop_traceExact_gaugeInvariant
    (gauge : GaugeProjection.SU3Gauge)
    (n leftCode rightCode : Nat) :
    ColorLoopTraceExact
        (colorLoopGaugeAction gauge
          (rawCodeColorLoopMatrix n leftCode rightCode)) ↔
      ColorLoopTraceExact
        (rawCodeColorLoopMatrix n leftCode rightCode) :=
  colorLoopTraceExact_gaugeInvariant gauge
    (rawCodeColorLoopMatrix n leftCode rightCode)

/-- Common raw carrier for the concrete P348 color-loop systems. -/
abbrev ColorLoopRawGaugeSystem :=
  RawGaugeOperations (Additive GaugeProjection.SU3Gauge)
    ColorLoopField ℂ ℂ

/-- Read the multiplicative `SU(3)` gauge group in additive notation only so
it can instantiate the neutral `RawGaugeOperations` interface. -/
def colorLoopRawGaugeOperations : ColorLoopRawGaugeSystem where
  act := fun gauge field =>
    colorLoopGaugeAction (Additive.toMul gauge) field
  actionFunctional := colorLoopTrace
  observable := colorLoopTrace

theorem colorLoopRawGaugeOperations_actionLawful :
    RawGaugeOperations.GaugeActionLawful
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopRawGaugeOperations := by
  constructor
  · intro field
    exact colorLoopGaugeAction_one field
  · intro gauge₁ gauge₂ field
    exact colorLoopGaugeAction_mul
      (Additive.toMul gauge₁) (Additive.toMul gauge₂) field

theorem colorLoopRawGaugeOperations_actionFunctionalInvariant :
    RawGaugeOperations.ActionFunctionalGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopRawGaugeOperations := by
  intro gauge field
  exact colorLoopTrace_gaugeInvariant (Additive.toMul gauge) field

theorem colorLoopRawGaugeOperations_observableInvariant :
    RawGaugeOperations.ObservableGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopRawGaugeOperations :=
  colorLoopRawGaugeOperations_actionFunctionalInvariant

/-- Concrete P348 positive instance of all three raw gauge laws. -/
theorem colorLoopRawGaugeOperations_admissible :
    RawGaugeOperations.GaugeAdmissible
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopRawGaugeOperations :=
  ⟨colorLoopRawGaugeOperations_actionLawful,
    colorLoopRawGaugeOperations_actionFunctionalInvariant,
    colorLoopRawGaugeOperations_observableInvariant⟩

/-! ## Gauge transformations as native standing operations -/

/-- P348 conjugation generates change-of-representation standing identity on
the color-loop field carrier. -/
def colorLoopGaugeStandingOperations :
    NativeStandingOperations ColorLoopField
      (Additive GaugeProjection.SU3Gauge) where
  apply := fun gauge field =>
    some (colorLoopGaugeAction (Additive.toMul gauge) field)

/-- Loop trace is a concrete operation-preserved anchor.  It is useful for
typed pullbacks but is not claimed to classify complete SU(3) gauge orbits. -/
def colorLoopTraceAnchoredStandingOperations :
    AnchoredStandingOperations ColorLoopField
      (Additive GaugeProjection.SU3Gauge) ℂ where
  toNativeStandingOperations := colorLoopGaugeStandingOperations
  anchor := colorLoopTrace
  anchor_preserved := by
    intro gauge source result happlies
    change
      some (colorLoopGaugeAction (Additive.toMul gauge) source) =
        some result at happlies
    injection happlies with hresult
    subst result
    exact colorLoopTrace_gaugeInvariant (Additive.toMul gauge) source

theorem colorLoopTraceExact_nativeMoveInvariant :
    NativeMoveInvariant colorLoopGaugeStandingOperations
      ColorLoopTraceExact := by
  intro gauge source result happlies
  change
    some (colorLoopGaugeAction (Additive.toMul gauge) source) =
      some result at happlies
  injection happlies with hresult
  subst result
  exact
    (colorLoopTraceExact_gaugeInvariant
      (Additive.toMul gauge) source).symm

/-- The exact trace property is standing-relevant under concrete SU(3)
representation changes. -/
theorem colorLoopTraceExact_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity colorLoopGaugeStandingOperations)
      ColorLoopTraceExact :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    colorLoopGaugeStandingOperations ColorLoopTraceExact).mpr
      colorLoopTraceExact_nativeMoveInvariant

/-! ## Raw source codes and gauge presentations on one trace anchor -/

/-- Minimal raw source data needed by the diagonal color-loop generator.  No
prime, atom, projection, or final balance proof is stored. -/
structure RawColorLoopSource where
  fiber : Nat
  leftCode : Nat
  rightCode : Nat
  deriving DecidableEq, Repr

namespace RawColorLoopSource

def field (source : RawColorLoopSource) : ColorLoopField :=
  rawCodeColorLoopMatrix source.fiber source.leftCode source.rightCode

def traceAnchor (source : RawColorLoopSource) : ℂ :=
  colorLoopTrace source.field

/-- The source presentation itself has only an identity move; nontrivial
source dynamics must be supplied by a future SU7/crystal adapter. -/
def anchoredStandingOperations :
    AnchoredStandingOperations RawColorLoopSource Unit ℂ where
  toNativeStandingOperations := {
    apply := fun _ source => some source
  }
  anchor := traceAnchor
  anchor_preserved := by
    intro move source result happlies
    simp only [Option.some.injEq] at happlies
    subst result
    rfl

end RawColorLoopSource

/-- A source-code presentation and a gauge-field presentation sharing the
same concrete trace anchor. -/
abbrev RawCodeGaugePresentation :=
  AnchoredStandingPullback
    RawColorLoopSource.anchoredStandingOperations
    colorLoopTraceAnchoredStandingOperations

/-- Canonical source-generated field point in the equal-trace pullback. -/
def rawCodeGaugePresentation
    (source : RawColorLoopSource) : RawCodeGaugePresentation :=
  ⟨(source, source.field), rfl⟩

theorem rawCodeGaugePresentation_traceExact_iff_balance
    (source : RawColorLoopSource) :
    ColorLoopTraceExact (rawCodeGaugePresentation source).1.2 ↔
      2 * source.fiber = source.leftCode + source.rightCode := by
  exact rawCodeColorLoop_traceExact_iff_balance
    source.fiber source.leftCode source.rightCode

/-- Gauge-invariant trace exactness lifts to the common source/gauge
presentation carrier. -/
theorem rawCodeGauge_traceExact_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity
        (AnchoredStandingPullback.operations
          RawColorLoopSource.anchoredStandingOperations
          colorLoopTraceAnchoredStandingOperations))
      (fun presentation : RawCodeGaugePresentation =>
        ColorLoopTraceExact presentation.1.2) :=
  AnchoredStandingPullback.rightLift_standingInvariant
    RawColorLoopSource.anchoredStandingOperations
    colorLoopTraceAnchoredStandingOperations
    colorLoopTraceExact_standingInvariant

namespace RawCodeGaugePresentation

/-- Concrete gauge change inside the equal-trace source presentation. -/
def gaugeTransform
    (gauge : Additive GaugeProjection.SU3Gauge)
    (presentation : RawCodeGaugePresentation) :
    RawCodeGaugePresentation :=
  ⟨(presentation.1.1,
      colorLoopGaugeAction (Additive.toMul gauge) presentation.1.2),
    by
      calc
        presentation.1.1.traceAnchor =
            colorLoopTrace presentation.1.2 := presentation.2
        _ = colorLoopTrace
            (colorLoopGaugeAction (Additive.toMul gauge)
              presentation.1.2) :=
          (colorLoopTrace_gaugeInvariant
            (Additive.toMul gauge) presentation.1.2).symm⟩

/-- Re-anchor the source/gauge presentation by the complete raw source record;
gauge transformations preserve that record definitionally. -/
def anchoredBySource :
    AnchoredStandingOperations RawCodeGaugePresentation
      (Additive GaugeProjection.SU3Gauge) RawColorLoopSource where
  toNativeStandingOperations := {
    apply := fun gauge presentation => some (gaugeTransform gauge presentation)
  }
  anchor := fun presentation => presentation.1.1
  anchor_preserved := by
    intro gauge source result happlies
    change some (gaugeTransform gauge source) = some result at happlies
    injection happlies with hresult
    subst result
    rfl

theorem traceExact_nativeMoveInvariant_anchoredBySource :
    NativeMoveInvariant anchoredBySource.toNativeStandingOperations
      (fun presentation => ColorLoopTraceExact presentation.1.2) := by
  intro gauge source result happlies
  change some (gaugeTransform gauge source) = some result at happlies
  injection happlies with hresult
  subst result
  exact
    (colorLoopTraceExact_gaugeInvariant
      (Additive.toMul gauge) source.1.2).symm

theorem traceExact_standingInvariant_anchoredBySource :
    StandingInvariant
      (generatedStandingIdentity anchoredBySource.toNativeStandingOperations)
      (fun presentation => ColorLoopTraceExact presentation.1.2) :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    anchoredBySource.toNativeStandingOperations _).mpr
      traceExact_nativeMoveInvariant_anchoredBySource

end RawCodeGaugePresentation

/-- Temporal presentations tagged by the same complete raw source record. -/
def rawSourceTaggedTemporalOperations :
    AnchoredStandingOperations
      (RawColorLoopSource × RawTemporalStanding) Nat RawColorLoopSource :=
  AnchoredStandingPullback.taggedOperations
    (Anchor := RawColorLoopSource) RawTemporalStanding.standingOperations

/-- One carrier joining source-generated gauge presentation and temporal
standing metadata over exactly the same raw source record. -/
abbrev RawCodeGaugeTemporalPresentation :=
  AnchoredStandingPullback
    RawCodeGaugePresentation.anchoredBySource
    rawSourceTaggedTemporalOperations

namespace RawCodeGaugeTemporalPresentation

def source (presentation : RawCodeGaugeTemporalPresentation) :
    RawColorLoopSource :=
  presentation.1.1.1.1

def gaugeField (presentation : RawCodeGaugeTemporalPresentation) :
    ColorLoopField :=
  presentation.1.1.1.2

def temporal (presentation : RawCodeGaugeTemporalPresentation) :
    RawTemporalStanding :=
  presentation.1.2.2

end RawCodeGaugeTemporalPresentation

def rawCodeGaugeTemporalPresentation
    (source : RawColorLoopSource)
    (temporal : RawTemporalStanding) :
    RawCodeGaugeTemporalPresentation :=
  ⟨(rawCodeGaugePresentation source, (source, temporal)), rfl⟩

def rawCodeGaugeTemporalOperations :
    NativeStandingOperations RawCodeGaugeTemporalPresentation
      (Sum (Additive GaugeProjection.SU3Gauge) Nat) :=
  AnchoredStandingPullback.operations
    RawCodeGaugePresentation.anchoredBySource
    rawSourceTaggedTemporalOperations

theorem rawCodeGaugeTemporal_traceExact_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity rawCodeGaugeTemporalOperations)
      (fun presentation : RawCodeGaugeTemporalPresentation =>
        ColorLoopTraceExact presentation.1.1.1.2) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    RawCodeGaugePresentation.anchoredBySource
    rawSourceTaggedTemporalOperations
    RawCodeGaugePresentation.traceExact_standingInvariant_anchoredBySource

theorem rawSourceTaggedTemporal_freshness_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity
        rawSourceTaggedTemporalOperations.toNativeStandingOperations)
      (fun presentation : RawColorLoopSource × RawTemporalStanding =>
        presentation.2.StandingFresh) :=
  AnchoredStandingPullback.taggedLift_standingInvariant
    (Anchor := RawColorLoopSource)
    RawTemporalStanding.standingOperations
    RawTemporalStanding.standingInvariant_standingFresh

theorem rawCodeGaugeTemporal_freshness_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity rawCodeGaugeTemporalOperations)
      (fun presentation : RawCodeGaugeTemporalPresentation =>
        presentation.1.2.2.StandingFresh) :=
  AnchoredStandingPullback.rightLift_standingInvariant
    RawCodeGaugePresentation.anchoredBySource
    rawSourceTaggedTemporalOperations
    rawSourceTaggedTemporal_freshness_standingInvariant

/-- The source/gauge/time pullback remains anchored by the full raw source and
can therefore be combined with further source-tagged audit axes. -/
def rawCodeGaugeTemporalAnchoredBySource :
    AnchoredStandingOperations RawCodeGaugeTemporalPresentation
      (Sum (Additive GaugeProjection.SU3Gauge) Nat)
      RawColorLoopSource :=
  AnchoredStandingPullback.anchoredOperations
    RawCodeGaugePresentation.anchoredBySource
    rawSourceTaggedTemporalOperations

def rawSourceTaggedAuthorityOperations :
    AnchoredStandingOperations
      (RawColorLoopSource × RawAuthorityStanding)
      RawAuthorityStanding.Move RawColorLoopSource :=
  AnchoredStandingPullback.taggedOperations
    (Anchor := RawColorLoopSource)
    RawAuthorityStanding.standingOperations

abbrev RawCodeGaugeTemporalAuthorityPresentation :=
  AnchoredStandingPullback
    rawCodeGaugeTemporalAnchoredBySource
    rawSourceTaggedAuthorityOperations

namespace RawCodeGaugeTemporalAuthorityPresentation

def gaugeField
    (presentation : RawCodeGaugeTemporalAuthorityPresentation) :
    ColorLoopField :=
  presentation.1.1.gaugeField

def temporal
    (presentation : RawCodeGaugeTemporalAuthorityPresentation) :
    RawTemporalStanding :=
  presentation.1.1.temporal

def authority
    (presentation : RawCodeGaugeTemporalAuthorityPresentation) :
    RawAuthorityStanding :=
  presentation.1.2.2

end RawCodeGaugeTemporalAuthorityPresentation

def rawCodeGaugeTemporalAuthorityPresentation
    (source : RawColorLoopSource)
    (temporal : RawTemporalStanding)
    (authority : RawAuthorityStanding) :
    RawCodeGaugeTemporalAuthorityPresentation :=
  ⟨(rawCodeGaugeTemporalPresentation source temporal,
      (source, authority)), rfl⟩

def rawCodeGaugeTemporalAuthorityOperations :
    NativeStandingOperations RawCodeGaugeTemporalAuthorityPresentation
      (Sum (Sum (Additive GaugeProjection.SU3Gauge) Nat)
        RawAuthorityStanding.Move) :=
  AnchoredStandingPullback.operations
    rawCodeGaugeTemporalAnchoredBySource
    rawSourceTaggedAuthorityOperations

theorem rawCodeGaugeTemporalAuthority_traceExact_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity rawCodeGaugeTemporalAuthorityOperations)
      (fun presentation : RawCodeGaugeTemporalAuthorityPresentation =>
        ColorLoopTraceExact presentation.gaugeField) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    rawCodeGaugeTemporalAnchoredBySource
    rawSourceTaggedAuthorityOperations
    rawCodeGaugeTemporal_traceExact_standingInvariant

theorem rawCodeGaugeTemporalAuthority_freshness_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity rawCodeGaugeTemporalAuthorityOperations)
      (fun presentation : RawCodeGaugeTemporalAuthorityPresentation =>
        presentation.temporal.StandingFresh) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    rawCodeGaugeTemporalAnchoredBySource
    rawSourceTaggedAuthorityOperations
    rawCodeGaugeTemporal_freshness_standingInvariant

theorem rawSourceTaggedAuthority_authorized_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity
        rawSourceTaggedAuthorityOperations.toNativeStandingOperations)
      (fun presentation : RawColorLoopSource × RawAuthorityStanding =>
        presentation.2.StandingAuthorized) :=
  AnchoredStandingPullback.taggedLift_standingInvariant
    (Anchor := RawColorLoopSource)
    RawAuthorityStanding.standingOperations
    RawAuthorityStanding.authorized_standingInvariant

theorem rawCodeGaugeTemporalAuthority_authorized_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity rawCodeGaugeTemporalAuthorityOperations)
      (fun presentation : RawCodeGaugeTemporalAuthorityPresentation =>
        presentation.authority.StandingAuthorized) :=
  AnchoredStandingPullback.rightLift_standingInvariant
    rawCodeGaugeTemporalAnchoredBySource
    rawSourceTaggedAuthorityOperations
    rawSourceTaggedAuthority_authorized_standingInvariant

def rawCodeGaugeTemporalAuthorityAnchoredBySource :
    AnchoredStandingOperations RawCodeGaugeTemporalAuthorityPresentation
      (Sum (Sum (Additive GaugeProjection.SU3Gauge) Nat)
        RawAuthorityStanding.Move)
      RawColorLoopSource :=
  AnchoredStandingPullback.anchoredOperations
    rawCodeGaugeTemporalAnchoredBySource
    rawSourceTaggedAuthorityOperations

noncomputable def rawSourceTaggedScaleOperations
    (scale : RawAffineScaleValidity) :
    AnchoredStandingOperations
      (RawColorLoopSource × ℝ) Unit RawColorLoopSource :=
  AnchoredStandingPullback.taggedOperations
    (Anchor := RawColorLoopSource) scale.standingOperations

abbrev RawCodeGaugeTemporalAuthorityScalePresentation
    (scale : RawAffineScaleValidity) :=
  AnchoredStandingPullback
    rawCodeGaugeTemporalAuthorityAnchoredBySource
    (rawSourceTaggedScaleOperations scale)

namespace RawCodeGaugeTemporalAuthorityScalePresentation

def gaugeField
    {scale : RawAffineScaleValidity}
    (presentation : RawCodeGaugeTemporalAuthorityScalePresentation scale) :
    ColorLoopField :=
  presentation.1.1.gaugeField

def temporal
    {scale : RawAffineScaleValidity}
    (presentation : RawCodeGaugeTemporalAuthorityScalePresentation scale) :
    RawTemporalStanding :=
  presentation.1.1.temporal

def authority
    {scale : RawAffineScaleValidity}
    (presentation : RawCodeGaugeTemporalAuthorityScalePresentation scale) :
    RawAuthorityStanding :=
  presentation.1.1.authority

def scaleValue
    {scale : RawAffineScaleValidity}
    (presentation : RawCodeGaugeTemporalAuthorityScalePresentation scale) : ℝ :=
  presentation.1.2.2

end RawCodeGaugeTemporalAuthorityScalePresentation

def rawCodeGaugeTemporalAuthorityScalePresentation
    (scale : RawAffineScaleValidity)
    (source : RawColorLoopSource)
    (temporal : RawTemporalStanding)
    (authority : RawAuthorityStanding)
    (value : ℝ) :
    RawCodeGaugeTemporalAuthorityScalePresentation scale :=
  ⟨(rawCodeGaugeTemporalAuthorityPresentation source temporal authority,
      (source, value)), rfl⟩

noncomputable def rawCodeGaugeTemporalAuthorityScaleAnchoredBySource
    (scale : RawAffineScaleValidity) :
    AnchoredStandingOperations
      (RawCodeGaugeTemporalAuthorityScalePresentation scale)
      (Sum
        (Sum (Sum (Additive GaugeProjection.SU3Gauge) Nat)
          RawAuthorityStanding.Move)
        Unit)
      RawColorLoopSource :=
  AnchoredStandingPullback.anchoredOperations
    rawCodeGaugeTemporalAuthorityAnchoredBySource
    (rawSourceTaggedScaleOperations scale)

@[simp] theorem rawCodeGaugeTemporalAuthorityScalePresentation_anchor
    (scale : RawAffineScaleValidity)
    (source : RawColorLoopSource)
    (temporal : RawTemporalStanding)
    (authority : RawAuthorityStanding)
    (value : ℝ) :
    (rawCodeGaugeTemporalAuthorityScaleAnchoredBySource scale).anchor
        (rawCodeGaugeTemporalAuthorityScalePresentation
          scale source temporal authority value) = source := by
  rfl

noncomputable def rawCodeGaugeTemporalAuthorityScaleOperations
    (scale : RawAffineScaleValidity) :
    NativeStandingOperations
      (RawCodeGaugeTemporalAuthorityScalePresentation scale)
      (Sum
        (Sum (Sum (Additive GaugeProjection.SU3Gauge) Nat)
          RawAuthorityStanding.Move)
        Unit) :=
  (rawCodeGaugeTemporalAuthorityScaleAnchoredBySource scale).toNativeStandingOperations

theorem rawCodeGaugeTemporalAuthorityScale_traceExact_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant
      (generatedStandingIdentity
        (rawCodeGaugeTemporalAuthorityScaleOperations scale))
      (fun presentation :
          RawCodeGaugeTemporalAuthorityScalePresentation scale =>
        ColorLoopTraceExact presentation.gaugeField) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    rawCodeGaugeTemporalAuthorityAnchoredBySource
    (rawSourceTaggedScaleOperations scale)
    rawCodeGaugeTemporalAuthority_traceExact_standingInvariant

theorem rawCodeGaugeTemporalAuthorityScale_freshness_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant
      (generatedStandingIdentity
        (rawCodeGaugeTemporalAuthorityScaleOperations scale))
      (fun presentation :
          RawCodeGaugeTemporalAuthorityScalePresentation scale =>
        presentation.temporal.StandingFresh) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    rawCodeGaugeTemporalAuthorityAnchoredBySource
    (rawSourceTaggedScaleOperations scale)
    rawCodeGaugeTemporalAuthority_freshness_standingInvariant

theorem rawCodeGaugeTemporalAuthorityScale_authorized_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant
      (generatedStandingIdentity
        (rawCodeGaugeTemporalAuthorityScaleOperations scale))
      (fun presentation :
          RawCodeGaugeTemporalAuthorityScalePresentation scale =>
        presentation.authority.StandingAuthorized) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    rawCodeGaugeTemporalAuthorityAnchoredBySource
    (rawSourceTaggedScaleOperations scale)
    rawCodeGaugeTemporalAuthority_authorized_standingInvariant

theorem rawSourceTaggedScale_eqTarget_standingInvariant
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingInvariant
      (generatedStandingIdentity
        (rawSourceTaggedScaleOperations scale).toNativeStandingOperations)
      (fun presentation : RawColorLoopSource × ℝ =>
        presentation.2 = scale.target) :=
  AnchoredStandingPullback.taggedLift_standingInvariant
    (Anchor := RawColorLoopSource) scale.standingOperations
    (scale.eqTarget_standingInvariant hvalid)

theorem rawCodeGaugeTemporalAuthorityScale_eqTarget_standingInvariant
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingInvariant
      (generatedStandingIdentity
        (rawCodeGaugeTemporalAuthorityScaleOperations scale))
      (fun presentation :
          RawCodeGaugeTemporalAuthorityScalePresentation scale =>
        presentation.scaleValue = scale.target) :=
  AnchoredStandingPullback.rightLift_standingInvariant
    rawCodeGaugeTemporalAuthorityAnchoredBySource
    (rawSourceTaggedScaleOperations scale)
    (rawSourceTaggedScale_eqTarget_standingInvariant scale hvalid)

/-! ## Concrete same-carrier gauge independence -/

/-- One off-diagonal color-loop component.  It changes sign under
`colorFlip01` conjugation. -/
def colorLoopEntry02 (field : ColorLoopField) : ℂ :=
  field 0 2

def colorLoopEntry02Probe : ColorLoopField :=
  fun i j => if i = 0 ∧ j = 2 then 1 else 0

theorem colorFlip01_mul_self : colorFlip01 * colorFlip01 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorFlip01, colorFlip01Raw]

theorem colorFlip01_inv : colorFlip01⁻¹ = colorFlip01 :=
  inv_eq_of_mul_eq_one_right colorFlip01_mul_self

/-- Both readouts are constant, but the zero action violates the identity
law on the nonzero probe. -/
def colorLoopActionLawFailureOperations : ColorLoopRawGaugeSystem where
  act := fun _ _ => 0
  actionFunctional := fun _ => 0
  observable := fun _ => 0

/-- Genuine P348 conjugation with a deliberately gauge-sensitive action
functional and the invariant trace observable. -/
def colorLoopActionFunctionalFailureOperations : ColorLoopRawGaugeSystem where
  act := fun gauge field =>
    colorLoopGaugeAction (Additive.toMul gauge) field
  actionFunctional := colorLoopEntry02
  observable := colorLoopTrace

/-- Genuine P348 conjugation with invariant trace action functional and a
deliberately gauge-sensitive observable. -/
def colorLoopObservableFailureOperations : ColorLoopRawGaugeSystem where
  act := fun gauge field =>
    colorLoopGaugeAction (Additive.toMul gauge) field
  actionFunctional := colorLoopTrace
  observable := colorLoopEntry02

theorem colorLoopEntry02Probe_value :
    colorLoopEntry02 colorLoopEntry02Probe = 1 := by
  simp [colorLoopEntry02, colorLoopEntry02Probe]

theorem colorLoopEntry02Probe_flip :
    colorLoopEntry02
        (colorLoopGaugeAction colorFlip01 colorLoopEntry02Probe) = -1 := by
  unfold colorLoopEntry02 colorLoopGaugeAction
  rw [colorFlip01_inv]
  simp [colorLoopEntry02Probe, colorFlip01, colorFlip01Raw,
    Matrix.mul_apply, Fin.sum_univ_three]

theorem colorLoopActionLawFailureOperations_not_actionLawful :
    ¬ RawGaugeOperations.GaugeActionLawful
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopActionLawFailureOperations := by
  intro hlaw
  have hidentity := hlaw.1 colorLoopEntry02Probe
  have hcomponent := congrArg colorLoopEntry02 hidentity
  change (0 : ℂ) = colorLoopEntry02Probe 0 2 at hcomponent
  have hprobe : colorLoopEntry02Probe 0 2 = 1 := by
    simp [colorLoopEntry02Probe]
  rw [hprobe] at hcomponent
  norm_num at hcomponent

theorem colorLoopActionLawFailureOperations_actionFunctionalInvariant :
    RawGaugeOperations.ActionFunctionalGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopActionLawFailureOperations := by
  intro gauge field
  rfl

theorem colorLoopActionLawFailureOperations_observableInvariant :
    RawGaugeOperations.ObservableGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopActionLawFailureOperations := by
  intro gauge field
  rfl

theorem colorLoopActionFunctionalFailureOperations_actionLawful :
    RawGaugeOperations.GaugeActionLawful
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopActionFunctionalFailureOperations := by
  exact colorLoopRawGaugeOperations_actionLawful

theorem colorLoopActionFunctionalFailureOperations_not_invariant :
    ¬ RawGaugeOperations.ActionFunctionalGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopActionFunctionalFailureOperations := by
  intro hinvariant
  have hvalue :=
    hinvariant (Additive.ofMul colorFlip01) colorLoopEntry02Probe
  change
    colorLoopEntry02
        (colorLoopGaugeAction colorFlip01 colorLoopEntry02Probe) =
      colorLoopEntry02 colorLoopEntry02Probe at hvalue
  rw [colorLoopEntry02Probe_flip, colorLoopEntry02Probe_value] at hvalue
  norm_num at hvalue

theorem colorLoopActionFunctionalFailureOperations_observableInvariant :
    RawGaugeOperations.ObservableGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopActionFunctionalFailureOperations := by
  intro gauge field
  exact colorLoopTrace_gaugeInvariant (Additive.toMul gauge) field

theorem colorLoopObservableFailureOperations_actionLawful :
    RawGaugeOperations.GaugeActionLawful
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopObservableFailureOperations := by
  exact colorLoopRawGaugeOperations_actionLawful

theorem colorLoopObservableFailureOperations_actionFunctionalInvariant :
    RawGaugeOperations.ActionFunctionalGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopObservableFailureOperations := by
  intro gauge field
  exact colorLoopTrace_gaugeInvariant (Additive.toMul gauge) field

theorem colorLoopObservableFailureOperations_not_invariant :
    ¬ RawGaugeOperations.ObservableGaugeInvariant
      (Gauge := Additive GaugeProjection.SU3Gauge)
      colorLoopObservableFailureOperations := by
  intro hinvariant
  have hvalue :=
    hinvariant (Additive.ofMul colorFlip01) colorLoopEntry02Probe
  change
    colorLoopEntry02
        (colorLoopGaugeAction colorFlip01 colorLoopEntry02Probe) =
      colorLoopEntry02 colorLoopEntry02Probe at hvalue
  rw [colorLoopEntry02Probe_flip, colorLoopEntry02Probe_value] at hvalue
  norm_num at hvalue

theorem colorLoopActionLawFailureOperations_onlyFails :
    RawGaugeOperations.OnlyFails colorLoopActionLawFailureOperations
      .actionLaw := by
  refine ⟨colorLoopActionLawFailureOperations_not_actionLawful, ?_⟩
  intro c hc
  cases c with
  | actionLaw => exact (hc rfl).elim
  | actionFunctionalInvariance =>
      exact colorLoopActionLawFailureOperations_actionFunctionalInvariant
  | observableInvariance =>
      exact colorLoopActionLawFailureOperations_observableInvariant

theorem colorLoopActionFunctionalFailureOperations_onlyFails :
    RawGaugeOperations.OnlyFails colorLoopActionFunctionalFailureOperations
      .actionFunctionalInvariance := by
  refine ⟨colorLoopActionFunctionalFailureOperations_not_invariant, ?_⟩
  intro c hc
  cases c with
  | actionLaw =>
      exact colorLoopActionFunctionalFailureOperations_actionLawful
  | actionFunctionalInvariance => exact (hc rfl).elim
  | observableInvariance =>
      exact colorLoopActionFunctionalFailureOperations_observableInvariant

theorem colorLoopObservableFailureOperations_onlyFails :
    RawGaugeOperations.OnlyFails colorLoopObservableFailureOperations
      .observableInvariance := by
  refine ⟨colorLoopObservableFailureOperations_not_invariant, ?_⟩
  intro c hc
  cases c with
  | actionLaw => exact colorLoopObservableFailureOperations_actionLawful
  | actionFunctionalInvariance =>
      exact colorLoopObservableFailureOperations_actionFunctionalInvariant
  | observableInvariance => exact (hc rfl).elim

theorem every_colorLoopGaugeCoordinate_has_only_one_failure_model
    (c : RawGaugeOperations.GaugeCoordinate) :
    ∃ S : ColorLoopRawGaugeSystem, RawGaugeOperations.OnlyFails S c := by
  cases c with
  | actionLaw =>
      exact ⟨colorLoopActionLawFailureOperations,
        colorLoopActionLawFailureOperations_onlyFails⟩
  | actionFunctionalInvariance =>
      exact ⟨colorLoopActionFunctionalFailureOperations,
        colorLoopActionFunctionalFailureOperations_onlyFails⟩
  | observableInvariance =>
      exact ⟨colorLoopObservableFailureOperations,
        colorLoopObservableFailureOperations_onlyFails⟩

/-! ## Pointwise exact topological transitions -/

/-- Combine the raw identity section cover with a pointwise P260 exact
transition.  No `SectionDescentCertificate` is accepted. -/
def exactTopologicalRawSectionTransition
    {B G : Type*} [Group G]
    (potential : Bool → B → G) (x : B) :
    RawSectionTransitionInstance Bool ℤ ℤ ℤ (Additive G) where
  cover := RawSectionTransitionInstance.RawSectionGluingToy.identityOverlapCover
  localFamily := fun _ => 0
  transition := fun i j =>
    Additive.ofMul (topologicalPrincipalExactTransition potential i j x)

theorem exactTopologicalRawSectionTransition_overlap
    {B G : Type*} [Group G]
    (potential : Bool → B → G) (x : B) :
    (exactTopologicalRawSectionTransition potential x).CurrentOverlapCompatible := by
  intro i j
  rfl

theorem exactTopologicalRawSectionTransition_glueCorrect
    {B G : Type*} [Group G]
    (potential : Bool → B → G) (x : B) :
    (exactTopologicalRawSectionTransition potential x).CurrentGlueCorrect := by
  intro i
  rfl

theorem exactTopologicalRawSectionTransition_glueUnique
    {B G : Type*} [Group G]
    (potential : Bool → B → G) (x : B) :
    (exactTopologicalRawSectionTransition potential x).CurrentGlueUnique := by
  intro global hrestricts
  have hfalse := hrestricts false
  simpa [exactTopologicalRawSectionTransition,
    RawSectionTransitionInstance.RawSectionGluingToy.identityOverlapCover]
    using hfalse

theorem exactTopologicalRawSectionTransition_flat
    {B G : Type*} [Group G]
    (potential : Bool → B → G) (x : B) :
    (exactTopologicalRawSectionTransition potential x).TransitionFlat := by
  intro i j k
  change
    topologicalPrincipalExactTransition potential j k x *
        topologicalPrincipalExactTransition potential i j x =
      topologicalPrincipalExactTransition potential i k x
  simp [topologicalPrincipalExactTransition, mul_assoc]

/-- Pointwise exact P260 transitions and raw section operations satisfy all
four current section/transition coordinates. -/
theorem exactTopologicalRawSectionTransition_admissible
    {B G : Type*} [Group G]
    (potential : Bool → B → G) (x : B) :
    (exactTopologicalRawSectionTransition potential x).SectionTransitionAdmissible :=
  ⟨exactTopologicalRawSectionTransition_overlap potential x,
    exactTopologicalRawSectionTransition_glueCorrect potential x,
    exactTopologicalRawSectionTransition_glueUnique potential x,
    exactTopologicalRawSectionTransition_flat potential x⟩

end PhysicsCore
end SaturationMonoid
