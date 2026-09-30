import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerJetProduct
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.HilbertSquareProduct

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherDensityProduct
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedSexticLatticePower (radical radical_fourth)
open NativePhysicalFourier (Torus ScalarField)
open NativeWindowAbsoluteTimeFourier (polynomial polynomial_square)
open NativeWindowMotherJetProduct (energy energy_nonnegative)
open NativeCanonicalFluidCoframe (density)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def component (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i : Coordinate) : ScalarField :=
  NativePhysicalFourier.scalarField (NativeWindowGreenSourceForm.velocity seed time) i

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  8+3*(NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant)*
    (max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon))^2

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ budget seed horizon := by
  unfold budget
  positivity [NativeUnheatedRieszKernel.constant_nonnegative]

theorem component_product (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (i : Coordinate)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    MemLp (fun x => (‖component seed time i x‖^2:ℂ) • polynomial F u x) 2 (volume : Measure Torus) ∧
      (∫ x : Torus,‖(‖component seed time i x‖^2:ℂ) • polynomial F u x‖^2) ≤
        (NativeWindowHistoryAdjointSpatialHalf.cap^2*NativeUnheatedRieszKernel.constant)*
          energy F u*(max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon))^2 := by
  have paid:=NativeWindowHilbertSquareProduct.norm_square_of_spectrum
    (component seed time i) (NativeWindowMotherCoefficientSpectrum.hOne seed 0 time valid i)
    (NativeWindowMotherCoefficientSpectrum.hOne_fourier seed 0 time valid i) F u
  refine ⟨paid.1,paid.2.trans ?_⟩
  have bound:‖NativeWindowMotherCoefficientSpectrum.hOne seed 0 time valid i‖^2 ≤
      max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon) :=
    (NativeWindowMotherCoefficientSpectrum.hOne_bound seed 0 time horizon valid before i).trans (le_max_right _ _)
  have square:=pow_le_pow_left₀ (sq_nonneg ‖NativeWindowMotherCoefficientSpectrum.hOne seed 0 time valid i‖) bound 2
  rw [← pow_mul] at square
  exact mul_le_mul_of_nonneg_left square
    (mul_nonneg (mul_nonneg (sq_nonneg _) NativeUnheatedRieszKernel.constant_nonnegative) (energy_nonnegative F u))

private theorem real_density_square (z : Coordinate → ℂ) :
    density (WithLp.toLp 2 (fun i => (z i).re))^2 ≤ 8+∑ i : Coordinate,‖z i‖^4 := by
  have vector:‖(WithLp.toLp 2 (fun i => (z i).re) : PhysicalSpace)‖^2 ≤ ∑ i : Coordinate,‖z i‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.norm_eq_abs,sq_abs,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    nlinarith only [sq_nonneg (z i).im]
  have square:=pow_le_pow_left₀ (sq_nonneg ‖(WithLp.toLp 2 (fun i => (z i).re) : PhysicalSpace)‖) vector 2
  have sum:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate) (fun _ => (1:ℝ)) (fun i => ‖z i‖^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,← pow_mul] at sum
  unfold density
  have nonnegative:0 ≤ ∑ i : Coordinate,‖z i‖^4:=Finset.sum_nonneg fun _ _ => by positivity
  nlinarith only [square,sum,nonnegative,sq_nonneg (‖(WithLp.toLp 2 (fun i => (z i).re) : PhysicalSpace)‖^2-16)]

theorem polynomial_mass (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    (∫ x : Torus,‖polynomial F u x‖^2) ≤ energy F u := by
  rw [polynomial_square]
  apply Finset.sum_le_sum
  intro k _
  rw [radical_fourth]
  dsimp only [NativeUnheatedSexticLatticePower.mass]
  nlinarith only [mul_nonneg (integerWaveNormSq_nonneg k) (sq_nonneg ‖u k‖)]

theorem source_product (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → E) :
    Integrable (fun x : Torus => density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)^2*‖polynomial F u x‖^2) ∧
      (∫ x : Torus,density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)^2*‖polynomial F u x‖^2) ≤
        budget seed horizon*energy F u := by
  let summand:=fun (i : Coordinate) (x : Torus) => ‖(‖component seed time i x‖^2:ℂ) • polynomial F u x‖^2
  let upper:=fun x : Torus => 8*‖polynomial F u x‖^2+∑ i : Coordinate,summand i x
  have each (i : Coordinate) : Integrable (summand i) :=
    (component_product seed time horizon valid before i F u).1.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have plain:Integrable (fun x : Torus => ‖polynomial F u x‖^2) :=
    (ContinuousMap.memLp volume ℂ (polynomial F u) : MemLp _ 2 _).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have integrableUpper:Integrable upper := (plain.const_mul 8).add (integrable_finsetSum Finset.univ fun i _ => each i)
  have point:∀ᵐ x : Torus,density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)^2*‖polynomial F u x‖^2 ≤ upper x := by
    filter_upwards [NativePhysicalFourier.realField_apply (NativeWindowGreenSourceForm.velocity seed time)] with x actual
    change NativePhysicalFourier.realField (NativeWindowGreenSourceForm.velocity seed time) x=_ at actual
    change density (NativePhysicalFourier.realField (NativeWindowGreenSourceForm.velocity seed time) x)^2*‖polynomial F u x‖^2 ≤ _
    rw [actual]
    have paid:=mul_le_mul_of_nonneg_right (real_density_square (fun i => component seed time i x)) (sq_nonneg ‖polynomial F u x‖)
    simpa only [upper,summand,add_mul,Finset.sum_mul,norm_smul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),← pow_mul,Nat.reduceMul,component,NativePhysicalFourier.realValue] using! paid
  have measured:AEStronglyMeasurable
      (fun x : Torus => density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)^2*‖polynomial F u x‖^2) volume := by
    have densityContinuous:Continuous density:=by unfold density; fun_prop
    exact ((densityContinuous.comp_aestronglyMeasurable
      (Lp.memLp (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time)).1).pow 2).mul
      ((polynomial F u).continuous.norm.pow 2).aestronglyMeasurable
  have member:=integrableUpper.mono' measured (by
    filter_upwards [point] with x paid
    have nonnegative:0 ≤ density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)^2*‖polynomial F u x‖^2:=mul_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa only [Real.norm_of_nonneg nonnegative] using paid)
  refine ⟨member,(integral_mono_ae member integrableUpper point).trans ?_⟩
  rw [integral_add (plain.const_mul 8) (integrable_finsetSum Finset.univ fun i _ => each i),
    integral_const_mul,integral_finsetSum _ (fun i _ => each i)]
  have bound:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun i _ => (component_product seed time horizon valid before i F u).2)
  have paid:=add_le_add (mul_le_mul_of_nonneg_left (polynomial_mass F u) (by norm_num : (0:ℝ)≤8)) bound
  exact paid.trans_eq (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,budget]; ring)

end
end SaturationMonoid.NavierStokes.NativeWindowMotherDensityProduct
