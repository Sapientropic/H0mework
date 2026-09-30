import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerDensityProduct
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerBound
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerContinuity

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherLowerProduct
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (polynomial)
open NativeWindowMotherJetProduct (energy energy_nonnegative)
open NativeWindowGreenTestForm (SpinFiber)
open NativeWindowAbsoluteLowerBound (Full lift cap)
open NativeCanonicalFluidCoframe (density)
open PhysicsCore DiracExteriorMatterAction
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def point (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (x : Torus) : Module.End ℂ DiracExteriorMatterCarrier :=
  NativeWindowAbsoluteTimePhysicalMatter.lower (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)
    (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid.le x)

theorem jet_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (x : Torus) :
    NativeWindowStageTenWholeFirstJet.sourceJet seed time valid.le x=
      NativeWindowGreenSourceForm.fullJet seed time valid x := rfl

theorem jet_measurable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) :
    AEStronglyMeasurable (fun x : Torus => NativeWindowStageTenWholeFirstJet.sourceJet seed time valid.le x) volume := by
  simp only [jet_original seed time valid]
  apply AEMeasurable.aestronglyMeasurable
  apply aemeasurable_pi_lambda
  intro d
  exact ((Lp.memLp (NativeWindowMotherJetProduct.vector seed time valid d)).1.congr
    (NativeWindowMotherJetProduct.vector_ae seed time valid d)).aemeasurable

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  5*cap^2*(NativeWindowMotherDensityProduct.budget seed horizon+
    12*NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeWindowMotherJetProduct.budget seed horizon)

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ budget seed horizon := by
  unfold budget
  positivity [NativeWindowMotherDensityProduct.budget_nonnegative seed horizon,
    NativeWindowMotherJetProduct.budget_nonnegative seed horizon]

def weight (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) (x : Torus) : ℝ :=
  density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)^2*‖polynomial F u x‖^2+
    ∑ d : Fin 4,‖NativeWindowGreenSourceForm.fullJet seed time valid x d‖^2*‖polynomial F u x‖^2

theorem source_weight (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    Integrable (weight seed time valid F u) ∧
      5*cap^2*(∫ x : Torus,weight seed time valid F u x) ≤ budget seed horizon*energy F u := by
  have mass:=NativeWindowMotherDensityProduct.source_product seed time horizon valid before F u
  have jets (d : Fin 4):=NativeWindowMotherJetProduct.source_vector_product seed time horizon valid before d F u
  refine ⟨mass.1.add (integrable_finsetSum Finset.univ fun d _ => (jets d).1),?_⟩
  dsimp only [weight]
  rw [integral_add mass.1 (integrable_finsetSum Finset.univ fun d _ => (jets d).1),
    integral_finsetSum _ (fun d _ => (jets d).1)]
  have all:=Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun d _ => (jets d).2)
  have paid:=mul_le_mul_of_nonneg_left (add_le_add mass.2 all) (by positivity : 0 ≤ 5*cap^2)
  exact paid.trans_eq (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,budget]; ring)

theorem point_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) (x : Torus) :
    ‖lift (point seed time valid x) (polynomial F u x)‖^2 ≤ 5*cap^2*weight seed time valid F u x := by
  have paid:=NativeWindowAbsoluteLowerBound.lower_square_bound
    (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)
    (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid.le x) (polynomial F u x)
  simpa only [point,jet_original seed time valid x,weight,add_mul,Finset.sum_mul,mul_assoc,mul_add] using paid

theorem source_product (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    MemLp (fun x : Torus => lift (point seed time valid x) (polynomial F u x)) 2 volume ∧
      (∫ x : Torus,‖lift (point seed time valid x) (polynomial F u x)‖^2) ≤ budget seed horizon*energy F u := by
  have source:=source_weight seed time horizon valid before F u
  have measured:AEStronglyMeasurable (fun x : Torus => lift (point seed time valid x) (polynomial F u x)) volume := by
    let action : PhysicalSpace × (Fin 4 → PhysicalSpace) × SpinFiber E → Full E :=
      fun data => lift (NativeWindowAbsoluteTimePhysicalMatter.lower data.1 data.2.1) data.2.2
    have continuous:Continuous action:=NativeWindowMotherLowerContinuity.continuous_lift
    have input:AEStronglyMeasurable (fun x : Torus =>
        (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x,
          NativeWindowStageTenWholeFirstJet.sourceJet seed time valid.le x,polynomial F u x)) volume :=
      (Lp.memLp (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time)).1.prodMk
        ((jet_measurable seed time valid).prodMk (polynomial F u).continuous.aestronglyMeasurable)
    simpa only [Function.comp_apply,action,point] using! continuous.comp_aestronglyMeasurable input
  have upper:=source.1.const_mul (5*cap^2)
  have integrable:Integrable (fun x : Torus => ‖lift (point seed time valid x) (polynomial F u x)‖^2) :=
    upper.mono' (measured.norm.pow 2) (Eventually.of_forall fun x => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using point_bound seed time valid F u x)
  refine ⟨(memLp_two_iff_integrable_sq_norm measured).mpr integrable,?_⟩
  have bound:=integral_mono_ae integrable upper (Eventually.of_forall (point_bound seed time valid F u))
  rw [integral_const_mul] at bound
  exact bound.trans source.2

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem point_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (x : Torus) :
    point seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) x=
      point step.1 time (by linarith) x := by
  unfold point
  rw [NativeCanonicalFriedrichsEnergy.sourceVelocity_next seed step generated time nonnegative]
  congr 1
  funext d
  refine Fin.cases ?_ (fun j => ?_) d
  · simp only [NativeWindowStageTenWholeFirstJet.sourceJet,Fin.cases_zero,
      NativeForwardWindowEvolution.velocityJet,NativeForwardWindowJets.jet_next seed 1 step generated time nonnegative]
  · simp only [NativeWindowStageTenWholeFirstJet.sourceJet,Fin.cases_succ,
      NativeWindowHistoryFirstJet.physicalJet_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowMotherLowerProduct
