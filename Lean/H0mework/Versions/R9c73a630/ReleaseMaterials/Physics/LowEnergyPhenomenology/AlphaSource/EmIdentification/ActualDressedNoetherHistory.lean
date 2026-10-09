import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCauchy

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoether
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open SourcePropagationNativeEulerHistory ActualDressedFullCoulomb ActualEMCauchyDynamic
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] actualPreparedHistoryKernel dressedEulerObserver dressedNoetherJet

/-- The source supplies a positive common interval for both nonlinear time legs. -/
def dressedHistoryDuration (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun t=>(signal t).value) 0) : ℝ :=
  preparedHistoryDuration (dressedKinematicPoint event transfer) (fun t=>(signal t).value) smooth

theorem dressed_history_duration_positive (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun t=>(signal t).value) 0) :
    0<dressedHistoryDuration event transfer signal smooth :=
  preparedHistoryDuration_positive _ _ _

/-- This observes the actual nonlinear preparation before amplitude differentiation. -/
def dressedNonlinearSource (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun t=>(signal t).value) 0)
    (amplitude t : ℝ) (i : Fin 289) : ℂ :=
  dressedEulerObserver event
    (actualPreparedHistoryKernel (dressedKinematicPoint event transfer) (fieldUnit i)
      (fun s=>(signal s).value) smooth amplitude t)

/-- The same created unit/background and two nonlinear time legs generate the full Noether response. -/
theorem dressed_nonlinear_source_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun t=>(signal t).value) 0)
    (t : ℝ) (nonnegative : 0≤t) (inside : t<dressedHistoryDuration event transfer signal smooth)
    (i : Fin 289) :
    HasDerivAt (fun amplitude=>dressedNonlinearSource event transfer signal smooth amplitude t i)
      (dressedNoetherJet event transfer signal t i).value 0 := by
  have original:=actualPreparedHistoryKernel_generated (dressedKinematicPoint event transfer) (fieldUnit i)
    signal smooth event.nonreal event.nonreal t nonnegative inside
  have observed:=((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 original
  with_reducible_and_instances
    simpa only [dressedNonlinearSource,dressedNoetherJet,ContinuousLinearMap.coe_restrictScalars',
      Function.comp_def] using observed

def dressedHistoryForcing (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun t=>(signal t).value) 0)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*
    deriv (fun amplitude=>dressedNonlinearSource event transfer signal smooth amplitude t i) 0

/-- The finite quantum forcing integrates the derivative of the original nonlinear source. -/
theorem dressed_history_forcing_noether (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun t=>(signal t).value) 0)
    (lambda : ℂ) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<dressedHistoryDuration event transfer signal smooth) :
    dressedHistoryForcing event transfer signal smooth lambda T=
      dressedNoetherForcing event transfer signal lambda T := by
  funext i
  unfold dressedHistoryForcing dressedNoetherForcing
  apply intervalIntegral.integral_congr
  intro t member
  rw [uIcc_of_le nonnegative] at member
  dsimp only
  rw [(dressed_nonlinear_source_generated event transfer signal smooth t member.1
    (member.2.trans_lt inside) i).deriv]

private theorem voltage_history_smooth (spatial : Fin 3→ℂ) (imaginary : Bool) :
    ContDiffAt ℝ 1 (fun t=>(voltageNativeTimeJet spatial imaginary t).value) 0 := by
  unfold voltageNativeTimeJet
  exact (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))

def dressedVoltageDuration (event : DressedEvent) (transfer : PhysicalMomentum) : ℝ :=
  min
    (dressedHistoryDuration event transfer (voltageNativeTimeJet (physicalSpatial transfer) false)
      (voltage_history_smooth _ false))
    (dressedHistoryDuration event transfer (voltageNativeTimeJet (physicalSpatial transfer) true)
      (voltage_history_smooth _ true))

theorem dressed_voltage_duration_positive (event : DressedEvent) (transfer : PhysicalMomentum) :
    0<dressedVoltageDuration event transfer :=
  lt_min (dressed_history_duration_positive _ _ _ _) (dressed_history_duration_positive _ _ _ _)

/-- Both real Cauchy families generate the same complex quantum update, on their source-generated common interval. -/
theorem dressed_voltage_forcing_nonlinear (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (nonnegative : 0≤T) (inside : T<dressedVoltageDuration event transfer) :
    dressedVoltageForcing event transfer lambda T=
      dressedHistoryForcing event transfer (voltageNativeTimeJet (physicalSpatial transfer) false)
        (voltage_history_smooth _ false) lambda T+
      Complex.I • dressedHistoryForcing event transfer (voltageNativeTimeJet (physicalSpatial transfer) true)
        (voltage_history_smooth _ true) lambda T := by
  exact congrArg₂ (fun a b : Fin 289→ℂ=>a+Complex.I • b)
    (dressed_history_forcing_noether event transfer _ _ lambda T nonnegative (lt_min_iff.mp inside).1).symm
    (dressed_history_forcing_noether event transfer _ _ lambda T nonnegative (lt_min_iff.mp inside).2).symm

end LowEnergy.GaussComposite.ActualDressedNoether
