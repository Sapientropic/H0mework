import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalRead

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalCurrent
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open NativeRecoveryTimeCanonical (canonicalDual gamma matterProgram)
open NativePhysicalFourier (Torus)
open NativeWholeH1Mixed (modes modes_closed)
open NativeWindowAbsoluteTimeFourier (Fiber field)
open NativeWindowAbsoluteTimePhysicalMatter (matter background)
open NativeWindowAbsoluteTimePhysicalRead
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem current_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : E) (u : Coordinate → E) (m : Coordinate → ℝ) (S : Coordinate → Coordinate → ℝ)
    (vacuum : inner ℂ b b=1) (left : ∀ i,inner ℂ b (u i)=(m i : ℂ))
    (right : ∀ i,inner ℂ (u i) b=(m i : ℂ))
    (pair : ∀ i j,inner ℂ (u i) (u j)=(S i j : ℂ))
    (symmetric : ∀ i j,S i j=S j i) (direction : Fin 4) :
    canonicalDual (matterProgram (fun _ => b) (fun _ => u) 0)
      (gamma (diracGamma direction) (matterProgram (fun _ => b) (fun _ => u) 0))=
        Fin.cases (2+(∑ i : Coordinate,(S i i : ℂ))/8) (fun j => (m j : ℂ)) direction := by
  have nb : (‖b‖ : ℂ)^2=1 := by
    simpa only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow] using! vacuum
  have diagonal (i : Coordinate) : (‖u i‖ : ℂ)^2=(S i i : ℂ) := by
    simpa only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow] using! pair i i
  have reverse10:=symmetric 1 0
  have reverse20:=symmetric 2 0
  have reverse21:=symmetric 2 1
  refine Fin.cases ?_ (fun spatial => ?_) direction <;>
    simp only [Fin.cases_zero,Fin.cases_succ]
  all_goals try fin_cases spatial
  all_goals
    simp [canonicalDual,gamma,matterProgram,diracAdjointSpinSwap,diracGamma,
      diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,Fin.sum_univ_four,Fin.sum_univ_two,
      inner_sub_right,inner_smul_right,left,right,pair,Fin.sum_univ_three,nb,diagonal,reverse10,reverse20,reverse21]
  · linear_combination -(S 1 1 : ℂ)/8*Complex.I_sq
  · ring
  · linear_combination -(m 1 : ℂ)*Complex.I_sq
  · ring

theorem matter_program (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    (fun spin color => matter seed M time spin color x)=
      matterProgram (fun _ => background time)
        (fun _ i => field (modes M) i (NativeWindowAbsoluteTimeSource.history seed time) x) 0 := by
  funext spin color
  fin_cases spin <;> fin_cases color <;>
    simp [matter,NativeWindowAbsoluteTimePhysicalMatter.baseWeight,
      NativeRecoveryTimeCanonicalWrite.matterMatrix,matterProgram,Fin.sum_univ_three] <;> module

theorem background_mass (time : ℝ) : inner ℂ (background time) (background time)=1 := by
  rw [background_map,(scalarMap time).inner_map_map,L2.inner_def]
  calc
    _ = ∫ _lag : ℝ,(1 : ℂ) ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const (p := 2) (μ := averageMeasure) (1 : ℂ)] with lag one
      change ((Lp.constL 2 averageMeasure ℂ (1 : ℂ)) : Lag) lag=(1 : ℂ) at one
      rw [one]
      simp
    _ = _ := by simp

theorem mean_real (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (i : Coordinate) (x : Torus) :
    inner ℂ (background time) (field (modes M) i (NativeWindowAbsoluteTimeSource.history seed time) x)=
      (NativeWindowFiniteGramFourier.read (modes M) i (NativeForwardWindowSource.source seed time) x : ℂ) := by
  rw [source_mean]
  apply complexRead_real
  exact ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.complexSharpSupportProjection_reality
    (modes M) _ (modes_closed M)
    (NativeEndpointVelocityCarrier.wholeVelocity_reality _ (NativeForwardWindowPairingReadout.mean_reality seed time))

theorem stress_symmetric (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (i j : Coordinate) (x : Torus) :
    NativeWindowFiniteGramFourier.stress seed time (modes M) i j x=
      NativeWindowFiniteGramFourier.stress seed time (modes M) j i x := by
  rw [NativeWindowFiniteGramFourier.stress_apply,NativeWindowFiniteGramFourier.stress_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => mul_comm _ _

def current (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) (x : Torus) : ℂ :=
  canonicalDual (fun spin color => matter seed M time spin color x)
    (gamma (diracGamma direction) (fun spin color => matter seed M time spin color x))

theorem source_current (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (direction : Fin 4) (x : Torus) :
    current seed M time direction x=Fin.cases
      (2+(∑ i : Coordinate,(NativeWindowFiniteGramFourier.stress seed time (modes M) i i x : ℂ))/8)
      (fun i => (NativeWindowFiniteGramFourier.read (modes M) i (NativeForwardWindowSource.source seed time) x : ℂ)) direction := by
  rw [current,matter_program]
  refine current_algebra (E := Fiber) (background time)
    (fun i => field (modes M) i (NativeWindowAbsoluteTimeSource.history seed time) x)
    (fun i => NativeWindowFiniteGramFourier.read (modes M) i (NativeForwardWindowSource.source seed time) x)
    (fun i j => NativeWindowFiniteGramFourier.stress seed time (modes M) i j x)
    (background_mass time) (fun i => mean_real seed M time i x) ?_ ?_ ?_ direction
  · intro i
    rw [← inner_conj_symm,mean_real]
    simp
  · intro i j
    exact source_pair seed (modes M) (modes_closed M) time i j x
  · exact fun i j => stress_symmetric seed M time i j x

def currentRead (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Fin 4 → C(Torus,ℝ) :=
  Fin.cases (ContinuousMap.const Torus 2+(1/8:ℝ) •
    ∑ i : Coordinate,NativeWindowFiniteGramFourier.stress seed time (modes M) i i)
    (fun i => NativeWindowFiniteGramFourier.read (modes M) i (NativeForwardWindowSource.source seed time))

theorem current_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (direction : Fin 4) (x : Torus) : current seed M time direction x=(currentRead seed M time direction x : ℂ) := by
  rw [source_current]
  refine Fin.cases ?_ (fun _ => rfl) direction
  simp only [currentRead,Fin.cases_zero,ContinuousMap.add_apply,ContinuousMap.const_apply,
    ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul,Complex.ofReal_add,
    Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

def stressCoefficient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : IntegerWavevector) (i j : Coordinate) : ℂ :=
  ∫ lag,NativeCompleteStressCarrier.read (NativeUnheatedWindowStress.finiteStress seed (modes M) (time-lag)) k i j ∂averageMeasure

theorem current_fourier (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (direction : Fin 4) (k : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (current seed M time direction) k=
      NativePairedCurrentFourier.coefficient
        (ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.complexSharpSupportProjection (modes M)
          (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst))
        (stressCoefficient seed M time) direction k := by
  have same : current seed M time direction=fun x => (currentRead seed M time direction x : ℂ) :=
    funext (current_read seed M time direction)
  rw [same,← NativeWindowFiniteGramFourier.fourierRead_apply]
  refine Fin.cases ?_ (fun i => ?_) direction
  · simp only [currentRead,NativePairedCurrentFourier.coefficient,Fin.cases_zero,map_add,map_smul,map_sum]
    have baseline : NativeWindowFiniteGramFourier.fourierRead k (ContinuousMap.const Torus 2)=
        NativePairedCurrentFourier.baseline k := by
      rw [NativeWindowFiniteGramFourier.fourierRead_apply]
      rfl
    have each (i : Coordinate) : NativeWindowFiniteGramFourier.fourierRead k
        (NativeWindowFiniteGramFourier.stress seed time (modes M) i i)= -stressCoefficient seed M time k i i := by
      rw [NativeWindowFiniteGramFourier.fourierRead_apply,
        NativeWindowFiniteGramFourier.stress_fourier seed time (modes M) (modes_closed M) i i k]
      rfl
    rw [baseline]
    simp only [each,Finset.sum_neg_distrib,NativePairedCurrentFourier.trace,Complex.real_smul,
      Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    ring
  · simp only [currentRead,NativePairedCurrentFourier.coefficient,Fin.cases_succ]
    rw [NativeWindowFiniteGramFourier.fourierRead_apply]
    simp only [NativeWindowFiniteGramFourier.read_original]
    apply NativePhysicalContinuous.continuousField_fourier
    · exact NativeCorrectionPhysical.finite_amplitude_paid _ _
    · exact ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.complexSharpSupportProjection_reality
        (modes M) _ (modes_closed M)
        (NativeEndpointVelocityCarrier.wholeVelocity_reality _ (NativeForwardWindowPairingReadout.mean_reality seed time))

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalCurrent
