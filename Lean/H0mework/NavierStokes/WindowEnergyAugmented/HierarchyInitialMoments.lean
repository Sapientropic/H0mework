import H0mework.NavierStokes.WindowEnergyAugmented.HierarchySource
import H0mework.NavierStokes.WindowSourcePreparation.InitialSource
import H0mework.NavierStokes.WindowSourceSobolev.PreparationSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStageNineInitialMoments
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWindowStageNineWords (word multiplier)
open NativeWindowStageNineSource (coefficient)
open NativeFullOrderAction (frequencySize frequencySize_nonneg)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section

theorem multiplier_bound (directions : List Coordinate) (wave : IntegerWavevector) :
    ‖multiplier directions wave‖^2≤(2*Real.pi)^(2*directions.length)*frequencySize wave^(2*directions.length) := by
  induction directions with
  | nil => simp [multiplier]
  | cons j rest ih =>
    rw [multiplier,norm_mul,mul_pow]
    have coordinate : (wave j : ℝ)^2≤frequencySize wave^2 :=
      (Finset.single_le_sum (fun i _ => sq_nonneg (wave i : ℝ)) (Finset.mem_univ j)).trans
        (NativeFullOrderSynthesis.normSq_le_frequencySize_sq wave)
    have first := mul_le_mul_of_nonneg_left coordinate (sq_nonneg (2*Real.pi))
    rw [← NativePhysicalGradient.multiplier_norm_sq] at first
    exact (mul_le_mul first ih (sq_nonneg _) (by positivity)).trans_eq (by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one,pow_add]
      ring)

theorem initial_row (M : ℕ) (directions : List Coordinate) (wave : IntegerWavevector) (inside : wave∈modes M) :
    (coefficient stackedShortCurrent M directions 0).1 wave=
      multiplier directions wave • NativeWindowPreparationInitial.velocity wave := by
  funext i
  rw [NativeWindowStageNineSource.coefficient_row stackedShortCurrent M directions 0 le_rfl wave inside]
  rw [← NativeWindowPreparedSobolevSource.initial_row,NativeUnheatedTriadRows.velocity_original]
  rfl

def massBudget (directions : List Coordinate) : ℝ := (2*Real.pi)^(2*directions.length)*
  NativeFullOrderInitial.initialMomentBudget directions.length

theorem initial_mass (M : ℕ) (directions : List Coordinate) :
    pairing (modes M) (coefficient stackedShortCurrent M directions 0) (coefficient stackedShortCurrent M directions 0)≤
      massBudget directions := by
  rw [pairing_eq]
  have row (wave : IntegerWavevector) (inside : wave∈modes M) :
      complexCoordinateRealInner ((coefficient stackedShortCurrent M directions 0).1 wave)
        ((coefficient stackedShortCurrent M directions 0).1 wave)≤
      (2*Real.pi)^(2*directions.length)*(frequencySize wave^(2*directions.length)*
        complexCoordinateAmplitudeSq (NativeWindowPreparationInitial.velocity wave)) := by
    rw [initial_row M directions wave inside,complexCoordinateRealInner_self,complexCoordinateVectorNormSq_smul,Complex.normSq_eq_norm_sq]
    exact (mul_le_mul_of_nonneg_right (multiplier_bound directions wave)
      (complexCoordinateVectorNormSq_nonneg _)).trans_eq (by
        change _=_*(_*complexCoordinateVectorNormSq (NativeWindowPreparationInitial.velocity wave))
        ring)
  apply (Finset.sum_le_sum row).trans
  rw [← Finset.mul_sum]
  have initial := (NativeWindowPreparationInitial.square_moments directions.length).sum_le_tsum (modes M)
    (fun wave _ => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) _) (complexCoordinateAmplitudeSq_nonneg _))
  rw [NativeWindowPreparationInitial.square_budget] at initial
  exact mul_le_mul_of_nonneg_left initial (by positivity)

def gradientBudget (directions : List Coordinate) : ℝ := (2*Real.pi)^(2*directions.length)*
  NativeFullOrderInitial.initialMomentBudget (directions.length+1)

theorem initial_gradient (M : ℕ) (directions : List Coordinate) :
    NativeUnheatedStressProduct.gradientMass (complexSharpSupportProjection (modes M)
      (coefficient stackedShortCurrent M directions 0).1)≤gradientBudget directions := by
  rw [NativeUnheatedStressProduct.projection_mass]
  have row (wave : IntegerWavevector) (inside : wave∈modes M) :
      NativeUnheatedStressProduct.density (coefficient stackedShortCurrent M directions 0).1 wave≤
      (2*Real.pi)^(2*directions.length)*(frequencySize wave^(2*(directions.length+1))*
        complexCoordinateAmplitudeSq (NativeWindowPreparationInitial.velocity wave)) := by
    have mass : NativeUnheatedStressProduct.density (coefficient stackedShortCurrent M directions 0).1 wave=
        integerWaveNormSq wave*complexCoordinateVectorNormSq ((coefficient stackedShortCurrent M directions 0).1 wave) := by
      simp only [NativeUnheatedStressProduct.density,NativeUnheatedStressProduct.amplitude,
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.euclideanCoordinateRow_norm_sq]
      rfl
    rw [mass,initial_row M directions wave inside,complexCoordinateVectorNormSq_smul,Complex.normSq_eq_norm_sq]
    rw [← mul_assoc]
    have first := mul_le_mul (NativeFullOrderSynthesis.normSq_le_frequencySize_sq wave) (multiplier_bound directions wave)
      (sq_nonneg _) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_right first (complexCoordinateVectorNormSq_nonneg (NativeWindowPreparationInitial.velocity wave))).trans_eq (by
      change _=_*(_*complexCoordinateVectorNormSq (NativeWindowPreparationInitial.velocity wave))
      simp only [Nat.mul_add,Nat.mul_one,pow_add]
      ring)
  apply (Finset.sum_le_sum row).trans
  rw [← Finset.mul_sum]
  have initial := (NativeWindowPreparationInitial.square_moments (directions.length+1)).sum_le_tsum (modes M)
    (fun wave _ => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) _) (complexCoordinateAmplitudeSq_nonneg _))
  rw [NativeWindowPreparationInitial.square_budget] at initial
  exact mul_le_mul_of_nonneg_left initial (by positivity)

end
end SaturationMonoid.NavierStokes.NativeWindowStageNineInitialMoments
