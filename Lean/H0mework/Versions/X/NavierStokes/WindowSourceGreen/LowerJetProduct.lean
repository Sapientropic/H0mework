import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerCoefficientSpectrum
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.HilbertHalfProduct
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassMeanJet

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherJetProduct
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedSexticLatticePower (radical radical_positive)
open NativePhysicalFourier (Torus ScalarField)
open NativeWindowAbsoluteTimeFourier (polynomial)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def energy (F : Finset IntegerWavevector) (u : IntegerWavevector → E) : ℝ :=
  ∑ p∈F,radical p^4*‖u p‖^2

omit [InnerProductSpace ℂ E] in
theorem energy_nonnegative (F : Finset IntegerWavevector) (u : IntegerWavevector → E) : 0 ≤ energy F u :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))

theorem spatial_product (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (j i : Coordinate)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    (∫ x : Torus,‖NativeWindowHistoryFirstJet.physicalJet seed time valid.le j i x • polynomial F u x‖^2) ≤
      NativeWindowHistoryAdjointSpatialHalf.cap^2*energy F u*
        ((2*Real.pi)^2*NativeWindowSobolevVelocity.budget seed 0 horizon) := by
  have paid:=NativeWindowHilbertHalfProduct.scalar_product_of_spectrum
    (NativeWindowHistoryFirstJet.physicalJet seed time valid.le j i)
    (NativeWindowMotherCoefficientSpectrum.spatial seed time valid j i)
    (NativeWindowMotherCoefficientSpectrum.spatial_fourier seed time valid j i) F u
  exact paid.trans (mul_le_mul_of_nonneg_left
    (NativeWindowMotherCoefficientSpectrum.spatial_bound seed time horizon valid before j i)
    (mul_nonneg (sq_nonneg _) (energy_nonnegative F u)))

theorem temporal_product (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (i : Coordinate)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    (∫ x : Torus,‖NativePhysicalFourier.scalarField (NativeEndpointVelocityCarrier.wholeVelocity
      (NativeForwardWindowEvolution.velocityJet seed order time)) i x • polynomial F u x‖^2) ≤
      NativeWindowHistoryAdjointSpatialHalf.cap^2*energy F u*NativeWindowSobolevVelocity.budget seed order horizon := by
  have paid:=NativeWindowHilbertHalfProduct.scalar_product_of_spectrum
    (NativePhysicalFourier.scalarField (NativeEndpointVelocityCarrier.wholeVelocity
      (NativeForwardWindowEvolution.velocityJet seed order time)) i)
    (NativeWindowMotherCoefficientSpectrum.temporal seed order time valid i)
    (NativeWindowMotherCoefficientSpectrum.temporal_fourier seed order time valid i) F u
  exact paid.trans (mul_le_mul_of_nonneg_left
    (NativeWindowMotherCoefficientSpectrum.temporal_bound seed order time horizon valid before i)
    (mul_nonneg (sq_nonneg _) (energy_nonnegative F u)))

def coefficient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (d : Fin 4) (i : Coordinate) : ScalarField :=
  Fin.cases (NativePhysicalFourier.scalarField (NativeEndpointVelocityCarrier.wholeVelocity
    (NativeForwardWindowEvolution.velocityJet seed 1 time)) i)
    (fun j => NativeWindowHistoryFirstJet.physicalJet seed time valid.le j i) d

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  max 0 (NativeWindowSobolevVelocity.budget seed 1 horizon)+
    (2*Real.pi)^2*max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon)

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ budget seed horizon := by
  unfold budget
  positivity

theorem source_product (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (d : Fin 4) (i : Coordinate)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    (∫ x : Torus,‖coefficient seed time valid d i x • polynomial F u x‖^2) ≤
      NativeWindowHistoryAdjointSpatialHalf.cap^2*energy F u*budget seed horizon := by
  refine Fin.cases ?_ (fun j => ?_) d
  · apply (temporal_product seed 1 time horizon valid before i F u).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (energy_nonnegative F u))
    exact (le_max_right _ _).trans (le_add_of_nonneg_right (by positivity))
  · apply (spatial_product seed time horizon valid before j i F u).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (energy_nonnegative F u))
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _)).trans
      (le_add_of_nonneg_left (le_max_left _ _))

def vector (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (d : Fin 4) : Lp PhysicalSpace 2 (volume : Measure Torus) :=
  Fin.cases (NativeCanonicalGreenNormalization.sourceField seed 1 time)
    (fun j => NativeWindowMeanSpatialJet.gradient seed time valid j) d

theorem vector_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (d : Fin 4) :
    vector seed time valid d=ᵐ[volume] fun x => NativeWindowGreenSourceForm.fullJet seed time valid x d := by
  refine Fin.cases (Eventually.of_forall fun _ => rfl) (fun j => ?_) d
  exact NativeWindowMeanSpatialJet.gradient_ae seed time valid j

theorem vector_components (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (d : Fin 4) :
    (fun x => NativeWindowGreenSourceForm.fullJet seed time valid x d)=ᵐ[volume]
      fun x => WithLp.toLp 2 (fun i => (coefficient seed time valid d i x).re) := by
  refine Fin.cases ?_ (fun _ => Eventually.of_forall fun _ => rfl) d
  exact NativePhysicalFourier.realField_apply (NativeEndpointVelocityCarrier.wholeVelocity
    (NativeForwardWindowEvolution.velocityJet seed 1 time))

private theorem real_vector_square (z : Coordinate → ℂ) :
    ‖(WithLp.toLp 2 (fun i => (z i).re) : PhysicalSpace)‖^2 ≤ ∑ i : Coordinate,‖z i‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.norm_eq_abs,sq_abs,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  nlinarith only [sq_nonneg (z i).im]

theorem source_vector_product (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (d : Fin 4)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    Integrable (fun x : Torus => ‖NativeWindowGreenSourceForm.fullJet seed time valid x d‖^2*‖polynomial F u x‖^2) ∧
      (∫ x : Torus,‖NativeWindowGreenSourceForm.fullJet seed time valid x d‖^2*‖polynomial F u x‖^2) ≤
        3*NativeWindowHistoryAdjointSpatialHalf.cap^2*energy F u*budget seed horizon := by
  let sum:=fun x : Torus => ∑ i : Coordinate,‖coefficient seed time valid d i x • polynomial F u x‖^2
  have each (i : Coordinate) : Integrable (fun x : Torus => ‖coefficient seed time valid d i x • polynomial F u x‖^2) :=
    (NativeWindowHilbertHalfProduct.product_memLp (polynomial F u) (coefficient seed time valid d i)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have paid:Integrable sum := integrable_finsetSum Finset.univ (fun i _ => each i)
  have bounded:∀ᵐ x : Torus,‖NativeWindowGreenSourceForm.fullJet seed time valid x d‖^2*‖polynomial F u x‖^2 ≤ sum x := by
    filter_upwards [vector_components seed time valid d] with x actual
    rw [actual]
    have bound:=mul_le_mul_of_nonneg_right (real_vector_square (fun i => coefficient seed time valid d i x)) (sq_nonneg ‖polynomial F u x‖)
    simpa only [sum,Finset.sum_mul,norm_smul,mul_pow] using bound
  have measured:AEStronglyMeasurable
      (fun x : Torus => ‖NativeWindowGreenSourceForm.fullJet seed time valid x d‖^2*‖polynomial F u x‖^2) volume :=
    ((((Lp.memLp (vector seed time valid d)).1.congr (vector_ae seed time valid d)).norm.pow 2).mul
      ((polynomial F u).continuous.norm.pow 2).aestronglyMeasurable)
  have integrable:=paid.mono' measured (by
    filter_upwards [bounded] with x bound
    have positive:0 ≤ ‖NativeWindowGreenSourceForm.fullJet seed time valid x d‖^2*‖polynomial F u x‖^2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa only [Real.norm_of_nonneg positive] using bound)
  refine ⟨integrable,(integral_mono_ae integrable paid bounded).trans ?_⟩
  rw [integral_finsetSum _ (fun i _ => each i)]
  have bound:=Finset.sum_le_sum (s := (Finset.univ:Finset Coordinate))
    (fun i _ => source_product seed time horizon valid before d i F u)
  exact bound.trans_eq (by simp; ring)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem coefficient_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (d : Fin 4) (i : Coordinate) :
    coefficient seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) d i=
      coefficient step.1 time (by linarith) d i := by
  refine Fin.cases ?_ (fun j => ?_) d
  · simp only [coefficient,Fin.cases_zero,NativeForwardWindowEvolution.velocityJet,
      NativeForwardWindowJets.jet_next seed 1 step generated time nonnegative]
  · simp only [coefficient,Fin.cases_succ,NativeWindowHistoryFirstJet.physicalJet_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowMotherJetProduct
