import H0mework.NavierStokes.WindowEnergyTraceCoupled.CoupledNext

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceEndpointTransfer
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWindowTraceAdjoint (value forward dual)
open NativeUnheatedIntegralBilinear PhysicsCore.StageNineDiracMatterGalerkinEvolution
noncomputable section
variable {nu : Viscosity}

def flow (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    (initial : physicalSpace (modes M)) : ℝ →physicalSpace (modes M) :=
  (exists_galerkinLinearCoefficientCurve_on_Icc (forward seed M) (NativeWindowTraceAdjoint.forward_continuous seed M) initial a b ab).choose

theorem flow_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    (initial : physicalSpace (modes M)) : flow seed M a b ab initial a=initial :=
  (exists_galerkinLinearCoefficientCurve_on_Icc (forward seed M) (NativeWindowTraceAdjoint.forward_continuous seed M) initial a b ab).choose_spec.1

theorem flow_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    (initial : physicalSpace (modes M)) (t : ℝ) (ht : t∈Icc a b) :
    HasDerivWithinAt (flow seed M a b ab initial) (forward seed M t (flow seed M a b ab initial t)) (Icc a b) t :=
  (exists_galerkinLinearCoefficientCurve_on_Icc (forward seed M) (NativeWindowTraceAdjoint.forward_continuous seed M) initial a b ab).choose_spec.2 t ht

theorem flow_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    (initial : physicalSpace (modes M)) : ContinuousOn (flow seed M a b ab initial) (Icc a b) :=
  fun t ht => (flow_derivative seed M a b ab initial t ht).continuousWithinAt

theorem flow_ac (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    (initial : physicalSpace (modes M)) : AbsolutelyContinuousOnInterval (flow seed M a b ab initial) a b := by
  let x:=flow seed M a b ab initial
  let rate:=fun t => forward seed M t (x t)
  have cont:=flow_continuous seed M a b ab initial
  have paid:ContinuousOn rate (Icc a b) := (NativeWindowTraceAdjoint.forward_continuous seed M).continuousOn.clm_apply cont
  have write (s t : ℝ) (hs : s∈Icc a b) (ht : t∈Icc a b) (st : s≤t) : x t-x s=∫r in s..t,rate r := by
    have subset:Icc s t⊆Icc a b := Icc_subset_Icc hs.1 ht.2
    have normed:=paid.mono subset
    rw [← uIcc_of_le st] at normed
    apply (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le st (cont.mono subset) _ normed.intervalIntegrable).symm
    intro r hr
    exact ((flow_derivative seed M a b ab initial r (subset (Ioo_subset_Icc_self hr))).mono subset).hasDerivAt
      (Icc_mem_nhds hr.1 hr.2)
  apply written_ac x rate (by rw [← uIcc_of_le ab] at paid; exact paid.intervalIntegrable)
  intro s hs t ht
  rw [uIcc_of_le ab] at hs ht
  by_cases st:s≤t
  · exact write s t hs ht st
  · rw [intervalIntegral.integral_symm,← write t s ht hs (le_of_not_ge st)]; abel

def potential (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :=
  NativeWindowTraceOperator.jointTest seed observation (modes M) F radius+
    nu.coeff • NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu

theorem potential_physical (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace (modes M)) :
    pairing (modes M) x (potential seed observation M F radius y)=
      ∑ i : Coordinate,inner ℝ (NativeWindowTraceEnergy.relative seed F radius observation)
        (NativeWindowStressHeatSource.physical (NativeWindowStressOseenTest.evaluate (modes M) F i x*
          NativeWindowStressOseenTest.evaluate (modes M) F i y)) := by
  rw [potential,LinearMap.add_apply,map_add,LinearMap.smul_apply,map_smul,
    NativeWindowTraceOperatorAction.jointTest_physical seed observation (modes M) F radius (modes_zero M) (modes_closed M)]
  simp only [smul_eq_mul]
  ring

def pairingValue (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    (initial : physicalSpace (modes M)) (t : ℝ) := pairing (modes M) (flow seed M a b ab initial t) (value seed M t)

def jointRow (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (a b : ℝ) (ab : a≤b) (initial : physicalSpace (modes M)) (t : ℝ) :=
  pairing (modes M) (flow seed M a b ab initial t) (NativeWindowTraceOperator.jointTest seed observation (modes M) F radius (value seed M t))

def potentialRow (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (a b : ℝ) (ab : a≤b) (initial : physicalSpace (modes M)) (t : ℝ) :=
  pairing (modes M) (flow seed M a b ab initial t) (potential seed observation M F radius (value seed M t))

def forcingRow (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    (initial : physicalSpace (modes M)) (t : ℝ) :=
  pairing (modes M) (flow seed M a b ab initial t) (NativeWindowStageNineSource.forcing seed M t)

theorem pairing_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (a b : ℝ) (ab : a≤b) (a0 : 0≤a) (initial : physicalSpace (modes M)) : ∀ᵐ t : ℝ,t∈Ioo a b →
    HasDerivAt (pairingValue seed M a b ab initial)
      (2*jointRow seed observation M F radius a b ab initial t-2*potentialRow seed observation M F radius a b ab initial t+
        forcingRow seed M a b ab initial t) t := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,NativeWindowTraceAdjoint.source_action_ae seed M]
    with t source sourceAction ht
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  have first:=co.hasFDerivAt.comp_hasDerivAt t ((flow_derivative seed M a b ab initial t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2))
  have last:=co.hasFDerivAt.comp_hasDerivAt t ((NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt t source)
  have actual:=first.inner ℝ last
  change HasDerivAt (pairingValue seed M a b ab initial)
    (pairing (modes M) (flow seed M a b ab initial t) (NativeWindowStageNineSource.lift (modes M) (NativeUnheatedGlobalNegativeOne.rate seed t))+
      pairing (modes M) (forward seed M t (flow seed M a b ab initial t)) (value seed M t)) t at actual
  rw [sourceAction (a0.trans ht.1.le),NativeWindowTraceAdjoint.adjoint_pairing,
    eq_sub_of_add_eq (NativeWindowTraceCoupled.action_sum seed M t (value seed M t))] at actual
  convert actual using 1
  simp only [jointRow,potentialRow,forcingRow,potential,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_sub,map_smul,smul_eq_mul]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowTraceEndpointTransfer
