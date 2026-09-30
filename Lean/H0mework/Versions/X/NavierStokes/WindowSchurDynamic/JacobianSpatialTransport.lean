import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.Kernel
import H0mework.Versions.X.NavierStokes.WindowHistory.SpatialWords

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySpatialTransport
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowOperatorGreen
open NativeWindowHistoryCreationGeometry (advection transport transport_row product_fourier)
open NativeWindowAugmentedGradient (derivative derivative_apply)
open NativePhysicalGradient (multiplier)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryMeanAction (frozen)
noncomputable section

theorem advection_row (M : Finset IntegerWavevector) (zero : 0 ∉ M) (closed : FiniteModeNegClosed M)
    (u v : physicalSpace M) (i : Coordinate) (k : IntegerWavevector) :
    fourierRead k (advection M zero closed u v i)=
      -∑ j : Coordinate,∑ q ∈ M,if k-q ∈ M then u.1 (k-q) j*(multiplier q j*v.1 q i) else 0 := by
  simp only [advection,map_neg,map_sum,product_fourier M closed,derivative_apply,Pi.smul_apply,smul_eq_mul]

theorem advection_derivative (M : Finset IntegerWavevector) (zero : 0 ∉ M) (closed : FiniteModeNegClosed M)
    (u v : physicalSpace M) (direction i : Coordinate) (k : IntegerWavevector) :
    multiplier k direction*fourierRead k (advection M zero closed u v i)=
      fourierRead k (advection M zero closed (derivative M zero closed direction u) v i)+
      fourierRead k (advection M zero closed u (derivative M zero closed direction v) i) := by
  simp only [advection_row,derivative_apply,Pi.smul_apply,smul_eq_mul,mul_neg,Finset.mul_sum,
    ← neg_add,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro q _
  by_cases inside : k-q ∈ M
  · simp only [if_pos inside]
    have split : multiplier k direction=multiplier (k-q) direction+multiplier q direction := by
      simpa only [sub_add_cancel] using NativeWindowHighPressureCurrent.multiplier_add (k-q) q direction
    rw [split]
    ring
  · simp only [if_neg inside,mul_zero,add_zero]

theorem transport_derivative (M : Finset IntegerWavevector) (zero : 0 ∉ M) (closed : FiniteModeNegClosed M)
    (nu : Viscosity) (u v : physicalSpace M) (j : Coordinate) :
    derivative M zero closed j (transport M zero closed nu u v)=
      transport M zero closed nu (derivative M zero closed j u) v+
      transport M zero closed nu u (derivative M zero closed j v) := by
  apply Subtype.ext
  apply lp.ext
  funext k
  simp only [derivative_apply,Submodule.coe_add,lp.coeFn_add,Pi.add_apply,transport_row]
  by_cases inside : k ∈ M
  · simp only [if_pos inside]
    change multiplier k j • (transverseProjectionLinearMap k) _=
      (transverseProjectionLinearMap k) _+(transverseProjectionLinearMap k) _
    rw [← map_smul,← map_add]
    congr 1
    funext i
    exact advection_derivative M zero closed u v j i k
  · simp only [if_neg inside,smul_zero,add_zero]

def finite (M : ℕ) (j : Coordinate) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) :=
  LinearMap.toContinuousLinearMap (NativeWindowStageNineWords.spatialGenerator (modes M) (modes_zero M) (modes_closed M) j)

theorem finite_laplacian (nu : Viscosity) (M : ℕ) (j : Coordinate) (v : physicalSpace (modes M)) :
    finite M j (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)=
      laplacian (modes M) (modes_zero M) (modes_closed M) nu (finite M j v) := by
  apply Subtype.ext
  apply lp.ext
  funext k
  change (derivative (modes M) (modes_zero M) (modes_closed M) j (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)).1 k=
    (laplacian (modes M) (modes_zero M) (modes_closed M) nu (derivative (modes M) (modes_zero M) (modes_closed M) j v)).1 k
  rw [derivative_apply,laplacian_row,laplacian_row,derivative_apply]
  exact smul_comm _ _ _

theorem frozen_split (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M)) :
    frozen nu M u v=(-nu.coeff) • laplacian (modes M) (modes_zero M) (modes_closed M) nu v+
      transport (modes M) (modes_zero M) (modes_closed M) nu u v := by
  have split := congrArg (fun A : Module.End ℝ (physicalSpace (modes M)) => A v)
    (operator_split (modes M) (modes_zero M) (modes_closed M) nu (NativeWindowTraceAdjoint.curlMap M u)
      (NativeWindowHistoryDynamicKernel.curl_reality M u))
  simpa only [frozen,NativeWindowHistoryCreationGeometry.transport,NativeWindowTraceAdjoint.curlMap_apply,
    LinearMap.add_apply,LinearMap.smul_apply] using! split

theorem frozen_derivative (nu : Viscosity) (M : ℕ) (j : Coordinate) (u v : physicalSpace (modes M)) :
    finite M j (frozen nu M u v)=frozen nu M u (finite M j v)+
      NativeWindowHistoryDynamicKernel.transport nu M (finite M j u) v := by
  rw [frozen_split,map_add,map_smul,finite_laplacian,frozen_split,NativeWindowHistoryDynamicKernel.transport_apply]
  have product := transport_derivative (modes M) (modes_zero M) (modes_closed M) nu u v j
  change finite M j (transport _ _ _ nu u v)=transport _ _ _ nu (finite M j u) v+transport _ _ _ nu u (finite M j v) at product
  rw [product]
  abel

theorem kernel_derivative (nu : Viscosity) (M : ℕ) (j : Coordinate) (u v : physicalSpace (modes M)) :
    finite M j (NativeWindowHistoryDynamicKernel.kernel nu M u v)-
      NativeWindowHistoryDynamicKernel.kernel nu M u (finite M j v)=
      NativeWindowHistoryDynamicKernel.kernel nu M u
        (NativeWindowHistoryDynamicKernel.transport nu M (finite M j u)
          (NativeWindowHistoryDynamicKernel.kernel nu M u v)) := by
  let K := NativeWindowHistoryDynamicKernel.kernel nu M u
  have equation := congrArg (finite M j) (NativeWindowHistoryDynamicKernel.write nu M u v)
  change finite M j (K v-frozen nu M u (K v))=finite M j v at equation
  rw [map_sub,frozen_derivative] at equation
  have rearranged : NativeWindowHistoryDynamicKernel.implicit nu M u (finite M j (K v))=
      finite M j v+NativeWindowHistoryDynamicKernel.transport nu M (finite M j u) (K v) := by
    change finite M j (K v)-frozen nu M u (finite M j (K v))=_
    rw [← equation]
    abel
  have applied := congrArg K rearranged
  rw [NativeWindowHistoryDynamicKernel.inverse,map_add] at applied
  change finite M j (K v)-K (finite M j v)=_
  rw [applied]
  abel

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySpatialTransport
