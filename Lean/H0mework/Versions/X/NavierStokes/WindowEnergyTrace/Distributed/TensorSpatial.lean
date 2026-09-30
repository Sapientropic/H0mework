import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Tensor
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatialTransport
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatial

set_option autoImplicit false
open scoped Topology BigOperators

namespace SaturationMonoid.NavierStokes.NativeResponseTensorPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint
noncomputable section
variable {nu : Viscosity}

def spatial (M : ℕ) (j : Coordinate) (u : physicalSpace (modes M)) :=
  NativeWindowAugmentedGradient.derivative (modes M) (modes_zero M) (modes_closed M) j u

private theorem flux_spatial (M : ℕ) (j : Coordinate) (u z : physicalSpace (modes M))
    (k : IntegerWavevector) (output input : Coordinate) :
    NativeHigherTimeJets.mixedFlux (spatial M j u).1 z.1 k output input+
      NativeHigherTimeJets.mixedFlux u.1 (spatial M j z).1 k output input =
        NativePhysicalGradient.multiplier k j*NativeHigherTimeJets.mixedFlux u.1 z.1 k output input := by
  have first := NativeHigherTimeJets.mixed_pair_summable (spatial M j u).1 z.1 k output input
  have last := NativeHigherTimeJets.mixed_pair_summable u.1 (spatial M j z).1 k output input
  simp only [NativeHigherTimeJets.mixedFlux,← neg_add,← first.tsum_add last,mul_neg,← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro p
  simp only [spatial,NativeWindowAugmentedGradient.derivative_apply,Pi.smul_apply,smul_eq_mul]
  have split : NativePhysicalGradient.multiplier k j =
      NativePhysicalGradient.multiplier p j+NativePhysicalGradient.multiplier (k-p) j := by
    simpa only [add_sub_cancel] using NativeWindowHighPressureCurrent.multiplier_add p (k-p) j
  rw [split]
  ring

theorem pairTensor_spatial_row (M : ℕ) (j : Coordinate) (u z : physicalSpace (modes M))
    (k : IntegerWavevector) :
    (pairTensor M (spatial M j u) z+pairTensor M u (spatial M j z)) k =
      NativePhysicalGradient.multiplier k j • pairTensor M u z k := by
  apply PiLp.ext
  intro pair
  change NativeWindowSobolevStress.quarter k •
      NativeHigherTimeJets.mixedFlux (spatial M j u).1 z.1 k pair.1 pair.2+
    NativeWindowSobolevStress.quarter k •
      NativeHigherTimeJets.mixedFlux u.1 (spatial M j z).1 k pair.1 pair.2 =
    NativePhysicalGradient.multiplier k j *
      (NativeWindowSobolevStress.quarter k • NativeHigherTimeJets.mixedFlux u.1 z.1 k pair.1 pair.2)
  rw [← smul_add,flux_spatial]
  simp only [Complex.real_smul]
  ring

private theorem tensor_spatial_skew (j : Coordinate)
    (first last firstJet lastJet : NativeCompleteStressCarrier.Space)
    (hf : ∀ k,firstJet k=NativePhysicalGradient.multiplier k j • first k)
    (hl : ∀ k,lastJet k=NativePhysicalGradient.multiplier k j • last k) :
    inner ℝ first lastJet = -inner ℝ firstJet last := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum,← tsum_neg]
  apply tsum_congr
  intro k
  rw [hf,hl]
  erw [real_inner_eq_re_inner (𝕜 := ℂ),real_inner_eq_re_inner (𝕜 := ℂ),
    inner_smul_left,inner_smul_right]
  simp only [starRingEnd_apply,NativeWindowStressHeatEnergy.multiplier_star,neg_mul,map_neg,neg_neg]

theorem opposite_diffusion_direction (M : ℕ) (j : Coordinate)
    (u z : physicalSpace (modes M)) :
    inner ℝ (pairTensor M u z)
      (pairTensor M (spatial M j (spatial M j u)) z-
        pairTensor M u (spatial M j (spatial M j z))) =
      ‖pairTensor M u (spatial M j z)‖^2-‖pairTensor M (spatial M j u) z‖^2 := by
  let A := pairTensor M (spatial M j u) z
  let B := pairTensor M u (spatial M j z)
  have jet (k : IntegerWavevector) :
      (pairTensor M (spatial M j (spatial M j u)) z-
        pairTensor M u (spatial M j (spatial M j z))) k =
      NativePhysicalGradient.multiplier k j • (A-B) k := by
    have left := pairTensor_spatial_row M j (spatial M j u) z k
    have right := pairTensor_spatial_row M j u (spatial M j z) k
    have difference := congrArg₂ (fun x y : NativeCompleteStressCarrier.Tensor => x-y) left right
    simp only [lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply,← smul_sub] at difference ⊢
    change _ = NativePhysicalGradient.multiplier k j • (A k-B k) at difference
    dsimp only [A,B] at difference
    convert difference using 1
    abel
  have green := tensor_spatial_skew j (pairTensor M u z) (A-B) (A+B)
    (pairTensor M (spatial M j (spatial M j u)) z-
      pairTensor M u (spatial M j (spatial M j z)))
    (pairTensor_spatial_row M j u z) jet
  rw [green]
  simp only [inner_add_left,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm A B]
  dsimp only [A,B]
  ring

theorem laplacian_spatial (M : ℕ) (u : physicalSpace (modes M)) :
    NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u =
      -∑ j : Coordinate,spatial M j (spatial M j u) := by
  have scalar (k : IntegerWavevector) :
      (∑ j : Coordinate,NativePhysicalGradient.multiplier k j*NativePhysicalGradient.multiplier k j) =
        -(integerWaveViscousMultiplier k : ℂ) := by
    have row (j : Coordinate) :
        NativePhysicalGradient.multiplier k j*NativePhysicalGradient.multiplier k j =
          -(‖NativePhysicalGradient.multiplier k j‖^2 : ℂ) := by
      have actual := Complex.normSq_eq_conj_mul_self (z := NativePhysicalGradient.multiplier k j)
      change (Complex.normSq (NativePhysicalGradient.multiplier k j) : ℂ) =
        star (NativePhysicalGradient.multiplier k j)*NativePhysicalGradient.multiplier k j at actual
      rw [NativeWindowStressHeatEnergy.multiplier_star,neg_mul,Complex.normSq_eq_norm_sq] at actual
      simpa only [neg_neg,Complex.ofReal_pow] using (congrArg Neg.neg actual).symm
    simp only [row,Finset.sum_neg_distrib,← Complex.ofReal_pow,← Complex.ofReal_sum]
    rw [NativePhysicalGradient.multiplier_sum_norm_sq]
    rfl
  apply Subtype.ext
  apply lp.ext
  funext k
  funext i
  simp only [NativeWindowOperatorGreen.laplacian_row,Submodule.coe_neg,Submodule.coe_sum,
    lp.coeFn_neg,lp.coeFn_sum,Pi.neg_apply,Finset.sum_apply,spatial,
    NativeWindowAugmentedGradient.derivative_apply,Pi.smul_apply,smul_eq_mul,Complex.real_smul]
  change (integerWaveViscousMultiplier k : ℂ)*u.1 k i =
    -∑ j : Coordinate,NativePhysicalGradient.multiplier k j*(NativePhysicalGradient.multiplier k j*u.1 k i)
  simp only [← mul_assoc,← Finset.sum_mul,scalar,neg_mul,neg_neg]

theorem opposite_diffusion_square (M : ℕ) (u z : physicalSpace (modes M)) :
    let L := NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
    2*inner ℝ (pairTensor M u z)
      (pairTensor M ((-nu.coeff) • L u) z+pairTensor M u (nu.coeff • L z)) =
      2*nu.coeff*(∑ j : Coordinate,‖pairTensor M u (spatial M j z)‖^2-
        ∑ j : Coordinate,‖pairTensor M (spatial M j u) z‖^2) := by
  intro L
  have heat : pairTensor M ((-nu.coeff) • L u) z+pairTensor M u (nu.coeff • L z) =
      nu.coeff • ∑ j : Coordinate,(pairTensor M (spatial M j (spatial M j u)) z-
        pairTensor M u (spatial M j (spatial M j z))) := by
    change pairTensorCLM M ((-nu.coeff) • L u) z+
      pairTensorCLM M u (nu.coeff • L z) = _
    dsimp only [L]
    rw [laplacian_spatial,laplacian_spatial]
    simp only [map_smul,map_neg,map_sum,smul_apply,sum_apply,
      pairTensorCLM_apply,Finset.sum_sub_distrib,smul_sub,neg_smul,smul_neg,neg_neg]
    rfl
  rw [heat,real_inner_smul_right,inner_sum]
  simp only [opposite_diffusion_direction,Finset.sum_sub_distrib]
  ring

open NativePhysicalFourier
open scoped ENNReal
open NativeWindowHistoryCreationGeometry (square transport)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowStressHeatSource (physical)
open NativeWindowFiniteGramFourier (fourierRead)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem mixed_product_fourier (M : ℕ) (u z : physicalSpace (modes M))
    (output input : Coordinate) (k : IntegerWavevector) :
    fourierRead k (evaluate (modes M) (modes M) output z*evaluate (modes M) (modes M) input u) =
      -NativeHigherTimeJets.mixedFlux u.1 z.1 k output input := by
  rw [NativeWindowHistoryCreationGeometry.product_fourier (modes M) (modes_closed M),
    NativeHigherTimeJets.mixedFlux,neg_neg]
  rw [tsum_eq_sum (s := modes M) (fun q outside => by
    simp only [physical_supported u q outside,Pi.zero_apply,zero_mul])]
  apply Finset.sum_congr rfl
  intro q _
  by_cases inside : k-q∈modes M
  · rw [if_pos inside,mul_comm]
  · simp only [if_neg inside,physical_supported z (k-q) inside,Pi.zero_apply,mul_zero]

private theorem mixed_product_norm (M : ℕ) (u z : physicalSpace (modes M))
    (output input : Coordinate) :
    ‖physical (evaluate (modes M) (modes M) output z*evaluate (modes M) (modes M) input u)‖ ≤
      ‖pairTensor M u z‖ := by
  rw [← (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.norm_map]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
  intro k
  rw [UnitAddTorus.mFourierBasis_repr,NativeWindowTraceTerminalCubic.physical_fourier,
    mixed_product_fourier,norm_neg]
  have component := PiLp.norm_apply_le (pairTensor M u z k) (output,input)
  change ‖NativeWindowSobolevStress.quarter k • NativeHigherTimeJets.mixedFlux u.1 z.1 k output input‖ ≤
    ‖pairTensor M u z k‖ at component
  apply le_trans ?_ component
  rw [norm_smul,Real.norm_of_nonneg (NativeWindowSobolevStress.quarter_nonnegative k)]
  apply le_mul_of_one_le_left (norm_nonneg _)
  unfold NativeWindowSobolevStress.quarter
  rw [Real.one_le_sqrt,Real.one_le_sqrt]
  linarith [integerWaveNormSq_nonneg k]

theorem physical_mixed_square_bound (M : ℕ) (u z : physicalSpace (modes M)) :
    (∫ point : Torus,square (modes M) u point*square (modes M) z point) ≤
      9*‖pairTensor M u z‖^2 := by
  let f (i j : Coordinate) := evaluate (modes M) (modes M) i z*evaluate (modes M) (modes M) j u
  have paid (i j : Coordinate) : Integrable (fun x : Torus => (f i j x)^2) :=
    ((f i j).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have expansion (point : Torus) :
      square (modes M) u point*square (modes M) z point =
        ∑ i : Coordinate,∑ j : Coordinate,(f i j point)^2 := by
    simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply,f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [expansion]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => paid i j))]
  simp only [integral_finsetSum Finset.univ (fun j _ => paid _ j),
    ← NativeWindowTraceTerminalSynthesis.physical_square]
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun i _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (mixed_product_norm M u z i j) 2
  convert bound using 1
  · rfl
  · simp
    ring


end
end SaturationMonoid.NavierStokes.NativeResponseTensorPayment
