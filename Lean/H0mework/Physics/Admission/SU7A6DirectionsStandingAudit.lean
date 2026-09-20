import H0mework.Physics.Admission.SU7A6SixDirectionStandingCarrier
import H0mework.Realization.Fields.SectionCover

/-!
# Seven-direction standing audit over the endpoint-stable SU7/A6 carrier

The seven primitive labels are used here as a structural standing-audit basis,
not as a seven-part ontology of the physical state.  In particular, the
historical `omegaGluing` slot is interpreted by a generic local/global section
presentation of the same nonconstant source lineage.  It is not identified
with a Plebanski or Lorentz connection.

The raw two-chart presentation includes incompatible local pairs.  Restriction
is always legal from a global presentation, while gluing is legal exactly when
the two local lineage sections agree.  Thus local gluing is a genuine computed
predicate, not a stored certificate.  A separate P68 descent theorem verifies
the compatible identity cover.

Equal-anchor pullback attaches this axis to the genuine SU7/A6 source, SU3
representation, temporal, authority, and contraction carrier.  The resulting
single carrier supports all seven native kinds of presentation change and
proves standing soundness plus completeness for one explicitly selected
standing-relevance family.  Exact lineage remains available through the
source anchor, an exact-match relation, and a reference-relative residual;
legal standing transport preserves that residual.  No Lorentz-connection producer, full filtered
current-shell source object, atom independence, P104 pullback, or P203 database
certificate is claimed.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7A6SevenDirectionStandingAudit

open StandardModelConstraint

noncomputable section

abbrev Lineage := SU7A6SixDirectionStandingCarrier.Lineage
abbrev SixState (scale : RawAffineScaleValidity) :=
  SU7A6SixDirectionStandingCarrier.State scale
abbrev SixMove :=
  Sum
    (Sum
      (Sum SU7A6SixDirectionStandingCarrier.BaseMove Nat)
      RawAuthorityStanding.Move)
    Unit

/-! ## A raw two-chart lineage presentation -/

/-- The P68 identity cover for a source lineage. -/
def lineageCover :
    SectionIndexedCover Bool Lineage (fun _ => Lineage)
      (fun _ _ => Lineage) where
  toLocal := fun _ lineage => lineage
  leftToOverlap := fun _ _ lineage => lineage
  rightToOverlap := fun _ _ lineage => lineage
  glue := fun localFamily => localFamily false

/-- Compatible local lineage sections glue uniquely.  This is theorem output,
not a field of the raw presentation below. -/
theorem lineageDescent : SectionDescentCertificate lineageCover where
  globalCompatible := by
    intro lineage left right
    rfl
  glueRestricts := by
    intro localFamily hcompatible index
    simpa [lineageCover] using hcompatible false index
  glueUnique := by
    intro localFamily _hcompatible lineage hrestricts
    simpa [lineageCover] using hrestricts false

/-- Either one global lineage presentation or two independently supplied local
lineage sections.  The latter are deliberately not assumed compatible. -/
inductive GluingPresentation where
  | global (lineage : Lineage)
  | localPair (left right : Lineage)
  deriving Repr

namespace GluingPresentation

/-- The left chart fixes the object anchor even when the local pair is
incompatible. -/
def anchor : GluingPresentation → Lineage
  | .global lineage => lineage
  | .localPair left _right => left

/-- Computed local/global consistency. -/
def Consistent : GluingPresentation → Prop
  | .global _lineage => True
  | .localPair left right => left = right

end GluingPresentation

inductive GluingMove where
  | restrict
  | glue
  deriving DecidableEq, Repr

/-- Restrict a global lineage to two identical charts.  Glue a raw local pair
only when its overlap equation is true. -/
def gluingApply :
    GluingMove → GluingPresentation → Option GluingPresentation
  | .restrict, .global lineage => some (.localPair lineage lineage)
  | .restrict, .localPair _left _right => none
  | .glue, .global _lineage => none
  | .glue, .localPair left right =>
      if left = right then some (.global left) else none

def gluingOperations :
    AnchoredStandingOperations GluingPresentation GluingMove Lineage where
  toNativeStandingOperations := { apply := gluingApply }
  anchor := GluingPresentation.anchor
  anchor_preserved := by
    intro move source result happlies
    cases move with
    | restrict =>
        cases source with
        | global lineage =>
            simp only [gluingApply, Option.some.injEq] at happlies
            subst result
            rfl
        | localPair left right => simp [gluingApply] at happlies
    | glue =>
        cases source with
        | global lineage => simp [gluingApply] at happlies
        | localPair left right =>
            simp only [gluingApply] at happlies
            split at happlies
            · simp only [Option.some.injEq] at happlies
              subst result
              rfl
            · simp at happlies

theorem consistent_nativeMoveInvariant :
    NativeMoveInvariant gluingOperations.toNativeStandingOperations
      GluingPresentation.Consistent := by
  intro move source result happlies
  cases move with
  | restrict =>
      cases source with
      | global lineage =>
          simp only [gluingOperations, gluingApply, Option.some.injEq]
            at happlies
          subst result
          simp [GluingPresentation.Consistent]
      | localPair left right =>
          simp [gluingOperations, gluingApply] at happlies
  | glue =>
      cases source with
      | global lineage => simp [gluingOperations, gluingApply] at happlies
      | localPair left right =>
          simp only [gluingOperations, gluingApply] at happlies
          split at happlies
          · rename_i hcompatible
            simp only [Option.some.injEq] at happlies
            subst result
            simp [GluingPresentation.Consistent, hcompatible]
          · simp at happlies

theorem consistent_standingInvariant :
    StandingInvariant
      (generatedStandingIdentity
        gluingOperations.toNativeStandingOperations)
      GluingPresentation.Consistent :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    gluingOperations.toNativeStandingOperations _).mpr
      consistent_nativeMoveInvariant

/-! ## Equal-lineage attachment to the genuine six-direction carrier -/

abbrev State (scale : RawAffineScaleValidity) :=
  AnchoredStandingPullback
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations

namespace State

def six {scale : RawAffineScaleValidity} (state : State scale) :
    SixState scale :=
  state.1.1

def gluing {scale : RawAffineScaleValidity} (state : State scale) :
    GluingPresentation :=
  state.1.2

end State

def globalPresentation
    (scale : RawAffineScaleValidity) (six : SixState scale) : State scale :=
  let lineage :=
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale).anchor six
  ⟨(six, .global lineage), rfl⟩

def diagonalLocalPresentation
    (scale : RawAffineScaleValidity) (six : SixState scale) : State scale :=
  let lineage :=
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale).anchor six
  ⟨(six, .localPair lineage lineage), rfl⟩

def anchoredOperations (scale : RawAffineScaleValidity) :
    AnchoredStandingOperations (State scale) (Sum SixMove GluingMove)
      Lineage :=
  AnchoredStandingPullback.anchoredOperations
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations

def nativeOperations (scale : RawAffineScaleValidity) :
    NativeStandingOperations (State scale) (Sum SixMove GluingMove) :=
  AnchoredStandingPullback.operations
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations

def identity (scale : RawAffineScaleValidity) :
    NativeStandingIdentity (State scale) :=
  generatedStandingIdentity (nativeOperations scale)

/-! ## All seven native predicates are standing-invariant -/

theorem sourceReachable_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant (identity scale)
      (fun state : State scale => state.six.base.sourceReachable) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (SU7A6SixDirectionStandingCarrier.sourceReachable_standingInvariant scale)

theorem authorized_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant (identity scale)
      (fun state : State scale => state.six.authority.StandingAuthorized) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (SU7A6SixDirectionStandingCarrier.authorized_standingInvariant scale)

theorem sourceConfluent_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant (identity scale)
      (fun state : State scale => state.six.base.sourceConfluent) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (SU7A6SixDirectionStandingCarrier.sourceConfluent_standingInvariant scale)

theorem traceExact_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant (identity scale)
      (fun state : State scale => ColorLoopTraceExact state.six.base.field) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (SU7A6SixDirectionStandingCarrier.traceExact_standingInvariant scale)

theorem contraction_standingInvariant
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingInvariant (identity scale)
      (fun state : State scale => state.six.scaleValue = scale.target) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (SU7A6SixDirectionStandingCarrier.contraction_standingInvariant
      scale hvalid)

theorem gluing_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant (identity scale)
      (fun state : State scale => state.gluing.Consistent) :=
  AnchoredStandingPullback.rightLift_standingInvariant
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations consistent_standingInvariant

theorem freshness_standingInvariant
    (scale : RawAffineScaleValidity) :
    StandingInvariant (identity scale)
      (fun state : State scale => state.six.temporal.StandingFresh) :=
  AnchoredStandingPullback.leftLift_standingInvariant
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (SU7A6SixDirectionStandingCarrier.freshness_standingInvariant scale)

/-! ## The historical seven labels as a structural audit vocabulary -/

/-- `omegaConsistent` is only the historical field name inherited from P10.
Its value here is generic two-chart local/global consistency, not a claim that
the audited object is a Lorentz connection. -/
def predicates (scale : RawAffineScaleValidity) :
    CSafePredicates (State scale) where
  sourceBacked := fun state => state.six.base.sourceReachable
  authoritySafe := fun state => state.six.authority.StandingAuthorized
  graphConfluent := fun state => state.six.base.sourceConfluent
  gaugeNonleaking := fun state => ColorLoopTraceExact state.six.base.field
  contractionSafe := fun state => state.six.scaleValue = scale.target
  omegaConsistent := fun state => state.gluing.Consistent
  freshnessSafe := fun state => state.six.temporal.StandingFresh

def semantics (scale : RawAffineScaleValidity) :
    ObligationSemantics (State scale) SemanticAtom :=
  semanticObligationSemantics (predicates scale)

theorem auditSound
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingAuditSound (identity scale) (semantics scale) := by
  rw [standingAuditSound_iff_atoms_standingInvariant]
  intro atom
  cases atom with
  | sourceReachability => exact sourceReachable_standingInvariant scale
  | authorityMonotonicity => exact authorized_standingInvariant scale
  | graphConfluence => exact sourceConfluent_standingInvariant scale
  | gaugeInvariance => exact traceExact_standingInvariant scale
  | contractionCertification =>
      exact contraction_standingInvariant scale hvalid
  | omegaGluing => exact gluing_standingInvariant scale
  | freshnessValidity => exact freshness_standingInvariant scale

def SevenStandingSafe
    (scale : RawAffineScaleValidity) (state : State scale) : Prop :=
  state.six.base.sourceReachable ∧
    state.six.authority.StandingAuthorized ∧
      state.six.base.sourceConfluent ∧
        ColorLoopTraceExact state.six.base.field ∧
          state.six.scaleValue = scale.target ∧
            state.gluing.Consistent ∧
              state.six.temporal.StandingFresh

theorem sevenStandingSafe_iff_csafe
    (scale : RawAffineScaleValidity) (state : State scale) :
    SevenStandingSafe scale state ↔ CSafe (predicates scale) state := by
  rfl

theorem sevenStandingSafe_standingInvariant
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingInvariant (identity scale) (SevenStandingSafe scale) := by
  intro source result hstanding
  have hsource := sourceReachable_standingInvariant scale hstanding
  have hauthority := authorized_standingInvariant scale hstanding
  have hconfluence := sourceConfluent_standingInvariant scale hstanding
  have hgauge := traceExact_standingInvariant scale hstanding
  have hcontraction := contraction_standingInvariant scale hvalid hstanding
  have hgluing := gluing_standingInvariant scale hstanding
  have hfreshness := freshness_standingInvariant scale hstanding
  constructor
  · rintro ⟨hs, ha, hc, hg, hx, ho, hf⟩
    exact ⟨hsource.mp hs, hauthority.mp ha, hconfluence.mp hc,
      hgauge.mp hg, hcontraction.mp hx, hgluing.mp ho,
      hfreshness.mp hf⟩
  · rintro ⟨hs, ha, hc, hg, hx, ho, hf⟩
    exact ⟨hsource.mpr hs, hauthority.mpr ha, hconfluence.mpr hc,
      hgauge.mpr hg, hcontraction.mpr hx, hgluing.mpr ho,
      hfreshness.mpr hf⟩

/-- One explicit, independently stated standing contract: predicates
extensionally equal to the conjunction of the seven domain-generated standing
conditions.  This is deliberately narrower than all domain properties. -/
def relevance
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingRelevance (identity scale) where
  relevant := fun target =>
    ∀ state, target state ↔ SevenStandingSafe scale state
  invariant := by
    intro target htarget source result hstanding
    calc
      target source ↔ SevenStandingSafe scale source := htarget source
      _ ↔ SevenStandingSafe scale result :=
        sevenStandingSafe_standingInvariant scale hvalid hstanding
      _ ↔ target result := (htarget result).symm

theorem atomCoverage
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    AtomCoverageCertificate (semantics scale)
      (relevance scale hvalid).relevant where
  invariant := by
    intro target htarget source result hatoms
    have hsource := hatoms .sourceReachability
    have hauthority := hatoms .authorityMonotonicity
    have hconfluence := hatoms .graphConfluence
    have hgauge := hatoms .gaugeInvariance
    have hcontraction := hatoms .contractionCertification
    have hgluing := hatoms .omegaGluing
    have hfreshness := hatoms .freshnessValidity
    have hsafe :
        SevenStandingSafe scale source ↔
          SevenStandingSafe scale result := by
      constructor
      · rintro ⟨hs, ha, hc, hg, hx, ho, hf⟩
        exact ⟨hsource.mp hs, hauthority.mp ha, hconfluence.mp hc,
          hgauge.mp hg, hcontraction.mp hx, hgluing.mp ho,
          hfreshness.mp hf⟩
      · rintro ⟨hs, ha, hc, hg, hx, ho, hf⟩
        exact ⟨hsource.mpr hs, hauthority.mpr ha, hconfluence.mpr hc,
          hgauge.mpr hg, hcontraction.mpr hx, hgluing.mpr ho,
          hfreshness.mpr hf⟩
    exact (htarget source).trans (hsafe.trans (htarget result).symm)

theorem finiteCompleteForSelectedStandingRelevance
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    FiniteFacetCompleteFor (semantics scale)
      (relevance scale hvalid).relevant := by
  classical
  exact
    (finiteFacetCompleteFor_standingRelevance_iff_atomCoverage
      (identity scale) (relevance scale hvalid) (semantics scale)).mpr
        (atomCoverage scale hvalid)

theorem semanticAtom_cardinality : Fintype.card SemanticAtom = 7 := by
  decide

/-! ## Both the source and local/global axes remain executable -/

def sourceLowerMove
    (simpleRoot : SU7A6GaugeStableRootGraphAdapter.StableRootIndex) :
    Sum SixMove GluingMove :=
  .inl
    (SU7A6SixDirectionStandingCarrier.sourceLowerMove simpleRoot)

theorem sourceLower_applies
    (scale : RawAffineScaleValidity)
    (base : SU7A6SixDirectionStandingCarrier.BasePresentation)
    (simpleRoot : SU7A6GaugeStableRootGraphAdapter.StableRootIndex)
    (temporal : RawTemporalStanding)
    (authority : RawAuthorityStanding)
    (value : Real) :
    ∃ result : State scale,
      (nativeOperations scale).apply (sourceLowerMove simpleRoot)
        (globalPresentation scale
          (SU7A6SixDirectionStandingCarrier.presentation
            scale base temporal authority value)) = some result := by
  let six :=
    SU7A6SixDirectionStandingCarrier.presentation
      scale base temporal authority value
  rcases SU7A6SixDirectionStandingCarrier.sourceLower_applies
      scale base simpleRoot temporal authority value with
    ⟨sixResult, hsix⟩
  exact AnchoredStandingPullback.exists_apply_inl_of_left_apply
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (source := globalPresentation scale six) hsix

theorem restrict_applies
    (scale : RawAffineScaleValidity) (six : SixState scale) :
    ∃ result : State scale,
      (nativeOperations scale).apply (.inr .restrict)
        (globalPresentation scale six) = some result := by
  apply AnchoredStandingPullback.exists_apply_inr_of_right_apply
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
  rfl

theorem glue_applies
    (scale : RawAffineScaleValidity) (six : SixState scale) :
    ∃ result : State scale,
      (nativeOperations scale).apply (.inr .glue)
        (diagonalLocalPresentation scale six) = some result := by
  let lineage :=
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale).anchor six
  have hglue :
      gluingOperations.apply .glue (.localPair lineage lineage) =
        some (.global lineage) := by
    simp [gluingOperations, gluingApply]
  exact AnchoredStandingPullback.exists_apply_inr_of_right_apply
    (SU7A6SixDirectionStandingCarrier.anchoredOperations scale)
    gluingOperations
    (source := diagonalLocalPresentation scale six) hglue

/-! ## Exact lineage lives in relation and residual, not in the seven atoms -/

/-- A signed, reference-relative discrepancy for the lineage anchor.  The
first component records the fiber displacement and the second records the
six A6-label coordinate displacements. -/
abbrev LineageResidual := Int × SU7A6WeightLabel

/-- Exact lineage is a relation between a reference and a state.  It is not
an eighth structural standing atom. -/
def LineageMatches {scale : RawAffineScaleValidity}
    (reference : Lineage) (state : State scale) : Prop :=
  (anchoredOperations scale).anchor state = reference

/-- The exact-lineage residual retains the discrepancy that the seven
Boolean standing projections deliberately do not encode. -/
def lineageResidual {scale : RawAffineScaleValidity}
    (reference : Lineage) (state : State scale) : LineageResidual :=
  ( ((anchoredOperations scale).anchor state).1 - reference.1,
    fun i => ((anchoredOperations scale).anchor state).2 i - reference.2 i )

/-- A reference-relative lineage residual vanishes exactly at a lineage
match.  Thus omission from the seven Boolean atoms is not information loss. -/
theorem lineageResidual_eq_zero_iff
    {scale : RawAffineScaleValidity}
    (reference : Lineage) (state : State scale) :
    lineageResidual reference state = 0 ↔
      LineageMatches reference state := by
  constructor
  · intro hzero
    have hfiber := congrArg Prod.fst hzero
    have hlabel := congrArg Prod.snd hzero
    change
      (((anchoredOperations scale).anchor state).1 : Int) -
          (reference.1 : Int) = 0 at hfiber
    change
      (fun i =>
        ((anchoredOperations scale).anchor state).2 i - reference.2 i) =
          0 at hlabel
    change (anchoredOperations scale).anchor state = reference
    apply Prod.ext
    · exact_mod_cast (sub_eq_zero.mp hfiber)
    · funext i
      have hi := congrFun hlabel i
      exact sub_eq_zero.mp hi
  · intro hmatch
    change (anchoredOperations scale).anchor state = reference at hmatch
    apply Prod.ext
    · simp [lineageResidual, hmatch]
    · funext i
      simp [lineageResidual, hmatch]

theorem lineageMatches_standingInvariant
    {scale : RawAffineScaleValidity} (reference : Lineage) :
    StandingInvariant (identity scale) (LineageMatches reference) := by
  intro source result hstanding
  have hanchor :=
    (anchoredOperations scale).anchor_eq_of_generatedStandingEquiv hstanding
  change
    ((anchoredOperations scale).anchor source = reference) ↔
      ((anchoredOperations scale).anchor result = reference)
  rw [hanchor]

/-- Legal standing transport and repair preserve the full lineage residual,
not merely the seven Boolean projections. -/
theorem lineageResidual_eq_of_sameStanding
    {scale : RawAffineScaleValidity} (reference : Lineage)
    {source result : State scale}
    (hstanding : (identity scale).sameStanding source result) :
    lineageResidual reference source = lineageResidual reference result := by
  have hanchor :=
    (anchoredOperations scale).anchor_eq_of_generatedStandingEquiv hstanding
  unfold lineageResidual
  rw [hanchor]

/-- Distinct lineage anchors are separated by a residual relative to the
first anchor, even when all seven standing atoms happen to agree. -/
theorem lineageResidual_separates
    {scale : RawAffineScaleValidity} {x y : State scale}
    (hlineage :
      (anchoredOperations scale).anchor x ≠
        (anchoredOperations scale).anchor y) :
    lineageResidual ((anchoredOperations scale).anchor x) x ≠
      lineageResidual ((anchoredOperations scale).anchor x) y := by
  intro hequal
  have hxZero :
      lineageResidual ((anchoredOperations scale).anchor x) x = 0 :=
    (lineageResidual_eq_zero_iff
      ((anchoredOperations scale).anchor x) x).2 rfl
  have hyZero :
      lineageResidual ((anchoredOperations scale).anchor x) y = 0 := by
    rw [← hequal]
    exact hxZero
  have hyMatch :=
    (lineageResidual_eq_zero_iff
      ((anchoredOperations scale).anchor x) y).1 hyZero
  exact hlineage hyMatch.symm

/-! ## Boolean exact-lineage coverage boundary after all seven directions -/

namespace LineageCounterexample

abbrev scale : RawAffineScaleValidity :=
  RawAffineScaleValidity.RawAffineScaleValidityToy.admissibleSystem

def rootLabelZero : SU7A6WeightLabel :=
  su7A6EndpointSourceLabel 0 0 0

def rootLabelOne : SU7A6WeightLabel :=
  su7A6EndpointSourceLabel 0 0 1

def baseZero : SU7A6SixDirectionStandingCarrier.BasePresentation where
  fiber := 0
  rootLabel := rootLabelZero
  moves := 0
  gaugeFrame := 1

def baseOne : SU7A6SixDirectionStandingCarrier.BasePresentation where
  fiber := 0
  rootLabel := rootLabelOne
  moves := 0
  gaugeFrame := 1

def sixZero : SixState scale :=
  SU7A6SixDirectionStandingCarrier.presentation scale baseZero
    RawTemporalStanding.Toy.fresh
    RawAuthorityStanding.Toy.authorized
    scale.target

def sixOne : SixState scale :=
  SU7A6SixDirectionStandingCarrier.presentation scale baseOne
    RawTemporalStanding.Toy.fresh
    RawAuthorityStanding.Toy.authorized
    scale.target

def stateZero : State scale := globalPresentation scale sixZero
def stateOne : State scale := globalPresentation scale sixOne

theorem rootLabels_distinct : rootLabelZero ≠ rootLabelOne := by
  intro hequal
  have hcoordinate := congrFun hequal (2 : Fin 6)
  change
    su7A6EndpointSourceLabel 0 0 0 (2 : Fin 6) =
      su7A6EndpointSourceLabel 0 0 1 (2 : Fin 6) at hcoordinate
  simp only [su7A6EndpointSourceLabel_two_num] at hcoordinate
  norm_num [su7A6EndpointSourceEnergyCorrection] at hcoordinate

theorem baseZero_traceExact : ColorLoopTraceExact baseZero.field := by
  change ColorLoopTraceExact
    (colorLoopGaugeAction 1
      (SU7A6GaugeStableRootGraphAdapter.rawField 0 rootLabelZero 0))
  rw [colorLoopTraceExact_gaugeInvariant]
  simpa [rootLabelZero,
    SU7A6GaugeStableRootGraphAdapter.rawField,
    SU7A6GaugeStableRootGraphAdapter.generatedLabel_zero,
    su7A6EndpointSourceLabel_leftCode,
    su7A6EndpointSourceLabel_rightCode] using
      ((rawCodeColorLoop_traceExact_iff_balance 0 0 0).mpr rfl)

theorem baseOne_traceExact : ColorLoopTraceExact baseOne.field := by
  change ColorLoopTraceExact
    (colorLoopGaugeAction 1
      (SU7A6GaugeStableRootGraphAdapter.rawField 0 rootLabelOne 0))
  rw [colorLoopTraceExact_gaugeInvariant]
  simpa [rootLabelOne,
    SU7A6GaugeStableRootGraphAdapter.rawField,
    SU7A6GaugeStableRootGraphAdapter.generatedLabel_zero,
    su7A6EndpointSourceLabel_leftCode,
    su7A6EndpointSourceLabel_rightCode] using
      ((rawCodeColorLoop_traceExact_iff_balance 0 0 0).mpr rfl)

theorem stateZero_safe : SevenStandingSafe scale stateZero := by
  refine ⟨?_, RawAuthorityStanding.Toy.authorized_valid, ?_,
    baseZero_traceExact, rfl, trivial,
    RawTemporalStanding.Toy.fresh_valid⟩
  · exact SU7A6GaugeStableRootGraphAdapter.everyState_reachable
      rootLabelZero 0 0
  · exact SU7A6GaugeStableRootGraphAdapter.graphConfluent
      rootLabelZero 0

theorem stateOne_safe : SevenStandingSafe scale stateOne := by
  refine ⟨?_, RawAuthorityStanding.Toy.authorized_valid, ?_,
    baseOne_traceExact, rfl, trivial,
    RawTemporalStanding.Toy.fresh_valid⟩
  · exact SU7A6GaugeStableRootGraphAdapter.everyState_reachable
      rootLabelOne 0 0
  · exact SU7A6GaugeStableRootGraphAdapter.graphConfluent
      rootLabelOne 0

theorem states_atomEquiv :
    AtomEquiv (semantics scale) stateZero stateOne := by
  intro atom
  exact iff_of_true
    ((semanticSafe_iff_csafe (predicates scale) stateZero).mpr
      ((sevenStandingSafe_iff_csafe scale stateZero).mp stateZero_safe) atom)
    ((semanticSafe_iff_csafe (predicates scale) stateOne).mpr
      ((sevenStandingSafe_iff_csafe scale stateOne).mp stateOne_safe) atom)

def lineageRelevance (reference : Lineage) :
    StandingRelevance (identity scale) where
  relevant := fun target =>
    ∀ state, target state ↔ LineageMatches reference state
  invariant := by
    intro target htarget source result hstanding
    calc
      target source ↔ LineageMatches reference source := htarget source
      _ ↔ LineageMatches reference result :=
        lineageMatches_standingInvariant reference hstanding
      _ ↔ target result := (htarget result).symm

theorem stateZero_matches :
    LineageMatches (0, rootLabelZero) stateZero := by
  rfl

theorem stateOne_not_matches :
    ¬ LineageMatches (0, rootLabelZero) stateOne := by
  intro hmatch
  apply rootLabels_distinct
  have hlabels := congrArg Prod.snd hmatch
  exact hlabels.symm

theorem stateZero_lineageResidual_zero :
    lineageResidual (0, rootLabelZero) stateZero = 0 :=
  (lineageResidual_eq_zero_iff (0, rootLabelZero) stateZero).2
    stateZero_matches

theorem stateOne_lineageResidual_ne_zero :
    lineageResidual (0, rootLabelZero) stateOne ≠ 0 := by
  intro hzero
  exact stateOne_not_matches
    ((lineageResidual_eq_zero_iff (0, rootLabelZero) stateOne).1 hzero)

theorem states_lineageResidual_distinct :
    lineageResidual (0, rootLabelZero) stateZero ≠
      lineageResidual (0, rootLabelZero) stateOne := by
  intro hequal
  apply stateOne_lineageResidual_ne_zero
  rw [← hequal]
  exact stateZero_lineageResidual_zero

/-- All seven structural audit predicates agree, so they cannot express this
exact-lineage target as a Boolean combination.  The preceding residual
theorems nevertheless distinguish the states.  This is a layer boundary for
the selected atom-coverage policy, not evidence that the full framework loses
lineage information or needs an eighth structural primitive. -/
theorem no_atomCoverage_for_lineageRelevance :
    ¬ AtomCoverageCertificate (semantics scale)
        (lineageRelevance (0, rootLabelZero)).relevant := by
  intro coverage
  have hcovered := coverage.invariant
    (LineageMatches (0, rootLabelZero))
    (by intro state; rfl)
    states_atomEquiv
  exact stateOne_not_matches (hcovered.mp stateZero_matches)

end LineageCounterexample

end
end SU7A6SevenDirectionStandingAudit
end PhysicsCore
end SaturationMonoid
