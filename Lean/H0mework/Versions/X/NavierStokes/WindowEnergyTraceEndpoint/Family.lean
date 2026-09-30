import H0mework.Versions.X.NavierStokes.WindowEnergyTraceEndpoint.Action

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceEndpointFamily
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeWindowStressOseenTest
open NativeWindowTraceAdjoint (forward dual backward)
open NativeWindowTraceEndpointTransfer (flow flow_initial flow_derivative flow_continuous)
noncomputable section
variable {nu : Viscosity}

def basis (M : ℕ) := Module.finBasis ℝ (physicalSpace (modes M))

def dualBasis (M : ℕ) (i : Fin (Module.finrank ℝ (physicalSpace (modes M)))) : physicalSpace (modes M) :=
  (duality (modes M)).symm ((basis M).coord i)

theorem dualBasis_pairing (M : ℕ) (i : Fin (Module.finrank ℝ (physicalSpace (modes M))))
    (x : physicalSpace (modes M)) : pairing (modes M) x (dualBasis M i)=(basis M).repr x i := by
  have same := congrArg (fun f : Module.Dual ℝ (physicalSpace (modes M)) => f x)
    ((duality (modes M)).apply_symm_apply ((basis M).coord i))
  change pairing (modes M) (dualBasis M i) x=_ at same
  rw [pairing_symmetric] at same
  exact same

def endpoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (sample : ℝ) (terminal : physicalSpace (modes M)) : physicalSpace (modes M) :=
  ∑ i, pairing (modes M) (flow seed M a b ab (basis M i) sample) terminal • dualBasis M i

theorem endpoint_basis (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (sample : ℝ) (terminal : physicalSpace (modes M)) (i : Fin (Module.finrank ℝ (physicalSpace (modes M)))) :
    pairing (modes M) (basis M i) (endpoint seed M a b ab sample terminal)=
      pairing (modes M) (flow seed M a b ab (basis M i) sample) terminal := by
  classical
  simp only [endpoint,map_sum,map_smul,smul_eq_mul,dualBasis_pairing,Module.Basis.repr_self,Finsupp.single_apply]
  simp

theorem pair_constant (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (sample : ℝ) (inside : sample ∈ Icc a b) (initial terminal : physicalSpace (modes M)) :
    pairing (modes M) (flow seed M a b ab initial sample) terminal=
      pairing (modes M) initial (backward seed M a sample inside.1 terminal a) := by
  let x := flow seed M a b ab initial
  let p := backward seed M a sample inside.1 terminal
  let paired := fun t => pairing (modes M) (x t) (p t)
  have interval : Icc a sample ⊆ Icc a b := Icc_subset_Icc le_rfl inside.2
  have continuous : ContinuousOn paired (Icc a sample) :=
    ((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
      ((flow_continuous seed M a b ab initial).mono interval)).inner
        ((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
          (NativeWindowTraceAdjoint.backward_continuous seed M a sample inside.1 terminal))
  have derivative (t : ℝ) (ht : t ∈ Ioo a sample) : HasDerivAt paired 0 t := by
    let co := LinearMap.toContinuousLinearMap (coefficients (modes M))
    have first := co.hasFDerivAt.comp_hasDerivAt t
      (((flow_derivative seed M a b ab initial t (interval (Ioo_subset_Icc_self ht))).mono interval).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))
    have last := co.hasFDerivAt.comp_hasDerivAt t
      ((NativeWindowTraceAdjoint.backward_derivative seed M a sample inside.1 terminal t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))
    have actual := first.inner ℝ last
    convert! actual using 1
    change 0=pairing (modes M) (x t) (-dual seed M t (p t))+
      pairing (modes M) (forward seed M t (x t)) (p t)
    rw [map_neg,NativeWindowTraceAdjoint.adjoint_pairing]
    ring
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1 continuous derivative (intervalIntegrable_const (c := (0 : ℝ)))
  rw [intervalIntegral.integral_zero] at written
  have same := sub_eq_zero.mp written.symm
  simpa only [paired,x,p,NativeWindowTraceAdjoint.backward_terminal,flow_initial] using same

theorem endpoint_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (sample : ℝ) (inside : sample ∈ Icc a b) (terminal : physicalSpace (modes M)) :
    endpoint seed M a b ab sample terminal=backward seed M a sample inside.1 terminal a := by
  apply NativeWindowStressOseenTest.pairing_injective (modes M)
  apply (basis M).ext
  intro i
  rw [pairing_symmetric (modes M) (endpoint seed M a b ab sample terminal) (basis M i),endpoint_basis,
    pairing_symmetric (modes M) (backward seed M a sample inside.1 terminal a) (basis M i)]
  exact pair_constant seed M a b ab sample inside (basis M i) terminal

theorem endpoint_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (terminal : ℝ → physicalSpace (modes M)) (continuous : ContinuousOn terminal (Icc a b)) :
    ContinuousOn (fun sample => endpoint seed M a b ab sample (terminal sample)) (Icc a b) := by
  unfold endpoint
  apply continuousOn_finsetSum
  intro i _
  exact (((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
    (flow_continuous seed M a b ab (basis M i))).inner (𝕜 := ℝ)
      ((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn continuous)).smul (continuousOn_const (c := dualBasis M i))

theorem endpoint_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (sample : ℝ) (inside : sample ∈ Icc a b) (initial terminal : physicalSpace (modes M)) :
    pairing (modes M) initial (endpoint seed M a b ab sample terminal)=
      pairing (modes M) (flow seed M a b ab initial sample) terminal := by
  rw [endpoint_original seed M a b ab sample inside]
  exact (pair_constant seed M a b ab sample inside initial terminal).symm

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem endpoint_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M : ℕ)
    (a b : ℝ) (ab : a ≤ b) (nonnegative : 0 ≤ a) (sample : ℝ) (inside : sample ∈ Icc a b)
    (terminal : physicalSpace (modes M)) :
    endpoint seed M (step.2.clockAdvance+a) (step.2.clockAdvance+b) (by linarith)
        (step.2.clockAdvance+sample) terminal=endpoint step.1 M a b ab sample terminal := by
  have shifted : step.2.clockAdvance+sample ∈ Icc (step.2.clockAdvance+a) (step.2.clockAdvance+b) := by
    constructor <;> linarith [inside.1,inside.2]
  rw [endpoint_original seed M _ _ _ _ shifted,endpoint_original step.1 M a b ab sample inside]
  exact NativeWindowTraceCoupled.backward_next seed step generated M a sample inside.1 nonnegative terminal
    (left_mem_Icc.mpr inside.1)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceEndpointFamily
