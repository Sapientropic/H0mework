import H0mework.Versions.X.NavierStokes.WindowPhysics.HeatEvolution
import H0mework.NavierStokes.Restart.NativeAccumulationRoot
import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Foundation.Authority.Representation
import H0mework.Versions.X.NavierStokes.SourceAction.SourceView.Formation.Ledger

set_option autoImplicit false
open scoped Topology ENNReal NNReal Convolution ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowRootCarrier

open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeCompleteHeatTransport

noncomputable section

variable {nu : Viscosity}

def clockAt (initial : GeneratedWholeRestartCurrent nu) : NativeTemporalCurrent initial → ℝ
  | .finite index => elapsedTime initial index
  | .cofinal => wholeRestartVelocityAccumulationTime initial
  | .galerkin _ => wholeRestartVelocityAccumulationTime initial

theorem clockAt_nonnegative (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) :
    0 ≤ clockAt initial current := by
  have accumulation : 0 ≤ wholeRestartVelocityAccumulationTime initial := by
    by_cases bounded : BddAbove (Set.range (elapsedTime initial))
    · exact (elapsedTime_nonneg initial 0).trans (le_ciSup bounded 0)
    · rw [wholeRestartVelocityAccumulationTime, ciSup_of_not_bddAbove bounded]
      simp only [Real.sSup_empty, le_refl]
  cases current with
  | finite index => exact elapsedTime_nonneg initial index
  | cofinal => exact accumulation
  | galerkin _ => exact accumulation

abbrev Occurrence (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) :=
  (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt current

structure CarrierAt (initial : GeneratedWholeRestartCurrent nu) {current : NativeTemporalCurrent initial}
    (occurrence : Occurrence initial current) where
  ledger : SourceNativeLedgerEvolutionAt (nativeTemporalSource initial) occurrence
  ledger_eq : ledger = (nativeTemporalLedgerCompiler initial).compile occurrence
  history : ℝ → FullSpace
  history_eq : history = fun time => NativeUnifiedCompleteSource.source initial (clockAt initial current + time)

/-- The mother law forms the complete original occurrence and history; the original compiler writes its ledger. -/
def generatedCarrier (initial : GeneratedWholeRestartCurrent nu) {current : NativeTemporalCurrent initial}
    (occurrence : Occurrence initial current) : CarrierAt initial occurrence where
  ledger := NativeWindowMotherLedgerConsumer.ledger initial ⟨current,occurrence⟩
  ledger_eq := NativeWindowMotherLedgerConsumer.ledger_eq initial ⟨current,occurrence⟩
  history time := NativeWindowMotherActualLaw.raw initial (⟨current,occurrence⟩,⟨time,0,0⟩)
  history_eq := by
    have clock : NativeWindowMotherOccurrenceMaterial.sourceClock initial current=clockAt initial current := by
      cases current <;> rfl
    simpa only [clock] using!
      NativeWindowMotherActualLaw.full_history initial ⟨current,occurrence⟩

def CarrierAt.view {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current} (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (time : ℝ) : FullSpace :=
  fullHeatCLM nu lag
    ((NativeForwardWindowSource.kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ] carrier.history) time)

theorem CarrierAt.view_generated {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current} (carrier : CarrierAt initial occurrence) (lag : ℝ≥0) (time : ℝ) :
    carrier.view lag time = NativeWindowHeatEvolution.source initial lag (clockAt initial current + time) := by
  rw [CarrierAt.view, carrier.history_eq, NativeWindowHeatEvolution.source,
    NativeForwardWindowSource.source_integrand]
  apply congrArg (fullHeatCLM nu lag)
  change (∫ shift : ℝ, NativeForwardWindowSource.kernel shift •
    NativeUnifiedCompleteSource.source initial (clockAt initial current + (time - shift))) = _
  simp only [add_sub_assoc]

abbrev HeatQuery := { lag : ℝ≥0 // 0 < lag }

def component (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeProjectionLaw (nativeTemporalAuthoritativeRoot initial).toLedgerRoot.source where
  Projection := HeatQuery
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} occurrence _ => CarrierAt initial occurrence
  project := fun _ {_} occurrence _ => generatedCarrier initial occurrence

def world (initial : GeneratedWholeRestartCurrent nu) : SourceNativeAuthoritativeRootClosure (N initial) (V initial) where
  source := (nativeTemporalAuthoritativeRoot initial).source.withProjectionCoface (component initial)
  emitted := (nativeTemporalAuthoritativeRoot initial).emitted
  compiler_commutes := (nativeTemporalAuthoritativeRoot initial).compiler_commutes

def installation (initial : GeneratedWholeRestartCurrent nu) :
    SourceNativeProjectionLaw.InstallationAt (component initial) (world initial).source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (nativeTemporalAuthoritativeRoot initial).source (component initial)

def living (initial : GeneratedWholeRestartCurrent nu) : SourceNativeLivingRootClosure (N initial) (V initial) :=
  (world initial).toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem same_generated_next (initial : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial)) :
    HEq ((living initial).generatedNextCurrentAt visit).visit.current
      ((nativeTemporalLivingRoot initial).generatedNextCurrentAt visit).visit.current := by
  rcases visit with ⟨current, history⟩
  cases current <;> rfl

theorem same_ledger_root (initial : GeneratedWholeRestartCurrent nu) :
    (world initial).toLedgerRoot = nativeTemporalRoot initial := rfl

theorem same_whole_ledger (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) :
    (world initial).generatedLedgerAt current = (nativeTemporalRoot initial).generatedLedgerAt current := rfl

theorem authority_consumes (initial : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial)) (query : HeatQuery) :
    let authority := (world initial).authoritativeEvolutionAt visit
    authority.toLedgerReadout = (world initial).toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (authority.toLedgerReadout.projectionOutcome (world := world initial) ((installation initial).embed query))
        ((component initial).outcomeAt query ((world initial).emitted visit.current)) :=
  ((world initial).authoritativeEvolutionAt visit).installedSubsystemAuthority_factorizes (installation initial) query

theorem CarrierAt.physical_hasDerivAt {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current} (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ)
    (valid : -1 < clockAt initial current + time) :
    HasDerivAt (fun sample => NativeNegativeFourMomentum.embed (carrier.view query.1 sample).fst)
      (momentumCLM nu (carrier.view query.1 time)) time := by
  have original := (NativeWindowHeatEvolution.state_hasDerivAt initial query.1
    (clockAt initial current + time) valid).scomp time
      ((hasDerivAt_id time).const_add (clockAt initial current))
  simpa only [Function.comp_def, one_smul, NativeWindowHeatEvolution.state_embedded,
    CarrierAt.view_generated] using! original

theorem finite_next_view (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) (query : HeatQuery) (time : ℝ) :
    (generatedCarrier initial (nativeTemporalEmitted initial (.finite (index + 1)))).view query.1 time =
      (generatedCarrier initial (nativeTemporalEmitted initial (.finite index))).view query.1
        ((run initial index).contact.time.1 + time) := by
  rw [CarrierAt.view_generated, CarrierAt.view_generated]
  change NativeWindowHeatEvolution.source initial query.1 (elapsedTime initial (index + 1) + time) = _
  rw [elapsedTime_succ, add_assoc]
  rfl

theorem cofinal_next_view (initial : GeneratedWholeRestartCurrent nu) (query : HeatQuery) :
    (generatedCarrier initial (nativeTemporalEmitted initial (.galerkin 0))).view query.1 =
      (generatedCarrier initial (nativeTemporalEmitted initial .cofinal)).view query.1 := by
  funext time
  rw [CarrierAt.view_generated, CarrierAt.view_generated]
  rfl

theorem galerkin_next_view (initial : GeneratedWholeRestartCurrent nu) (radius : ℕ) (query : HeatQuery) :
    (generatedCarrier initial (nativeTemporalEmitted initial (.galerkin (radius + 1)))).view query.1 =
      (generatedCarrier initial (nativeTemporalEmitted initial (.galerkin radius))).view query.1 := by
  funext time
  rw [CarrierAt.view_generated, CarrierAt.view_generated]
  rfl

end
end SaturationMonoid.NavierStokes.NativeWindowRootCarrier
