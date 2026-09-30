import H0mework.NavierStokes.WindowEnergyTraceCoupled.CoupledEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeCommonAdvectorAction
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeWholeResolvent NativePhysicalPairing NativeWholeH1Pairing
noncomputable section
variable {nu : Viscosity}

def gradientTest (M : ℕ) (v : physicalSpace (modes M)) : State :=
  gradientValue (includeCLM (modes M) (modes_closed M) v)
    (h1_of_curl_summable _ (NativeSourceResolvent.physical_curl_summable _ v))

theorem gradientTest_norm (M : ℕ) (v : physicalSpace (modes M)) :
    ‖gradientTest M v‖^2=curlPair (modes M) v.1 v.1 := by
  rw [norm_sq_sum]
  have row (k : Wave) : ‖gradientTest M v k‖^2=curlDensity (puncturedEuclideanize v.1) k := by
    change ‖Real.sqrt (integerWaveViscousMultiplier k.1) • (puncturedEuclideanize v.1) k‖^2=_
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (multiplier_positive k).le]
    rfl
  simp_rw [row]
  exact NativeSourceResolvent.physical_curl_sum _ (modes_zero M) v

theorem input_pairing (M : ℕ) (data : State) (v : physicalSpace (modes M)) :
    pairing (modes M) (NativeWindowStageNineSource.lift (modes M) data) v=inner ℝ data (gradientTest M v) := by
  rw [NativeWindowStageNineSource.lift_pairing,lp.inner_eq_tsum]
  let density (k : IntegerWavevector) := ∑ i : Coordinate,inner ℝ (NativeUnheatedTriadRows.decode k i data) (v.1 k i)
  have row (k : Wave) : inner ℝ (data k) (gradientTest M v k)=density k.1 := by
    change inner ℝ (data k) (Real.sqrt (integerWaveViscousMultiplier k.1) • euclideanCoordinateRow (v.1 k.1))=_
    rw [real_inner_smul_right,PiLp.inner_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [NativeUnheatedTriadRows.decode_apply,NativeUnheatedPairNegativeKernel.root,
      wholeVelocity_nonzero data k,real_inner_smul_left]
    rfl
  simp_rw [row]
  symm
  calc
    (∑' k : Wave,density k.1)=∑ k∈(modes M).subtype (fun k => k≠0),density k.1 := by
      apply tsum_eq_sum
      intro k outside
      have absent:k.1∉modes M := by simpa only [Finset.mem_subtype] using outside
      simp only [density,physical_supported v k.1 absent,Pi.zero_apply,inner_zero_right,Finset.sum_const_zero]
    _ =∑ k∈modes M,density k := Finset.sum_subtype_of_mem density (fun k member zero => modes_zero M (zero ▸ member))

theorem input_pairing_bound (M : ℕ) (data : State) (v : physicalSpace (modes M)) :
    |pairing (modes M) (NativeWindowStageNineSource.lift (modes M) data) v|≤‖data‖*Real.sqrt (curlPair (modes M) v.1 v.1) := by
  rw [input_pairing,← gradientTest_norm,Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

theorem source_input_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ outerRadius M,∀ observation∈Icc 0 horizon,∀ᵐ time : ℝ,0≤time →∀ w,
      let F:=integerWaveFrequencyCube outerRadius
      |2*pairing (modes M) (NativeWindowTraceDualEvolution.lifted seed M F radius observation w)
        (NativeWindowStageNineSource.lift (modes M) (input seed M time))|≤
          2*cap nu*(1+NativeUnheatedSourceGradient.mass seed time)*
            Real.sqrt (2*NativeWindowTraceDualEvolution.energy seed M F radius observation w/nu.coeff) := by
  obtain ⟨low,C,C0,paid⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M observation observed => ?_⟩
  filter_upwards [input_bound_ae seed] with time normed time0 w
  dsimp only
  let F:=integerWaveFrequencyCube outerRadius
  let z:=NativeWindowTraceDualEvolution.lifted seed M F radius observation w
  let E:=NativeWindowTraceDualEvolution.energy seed M F radius observation w
  have controlled:=(paid radius above outerRadius M observation observed).2 w
  have basic:0≤pairing (modes M) z z := by
    change (0 : ℝ) ≤ inner ℝ (coefficients (modes M) z) (coefficients (modes M) z)
    exact real_inner_self_nonneg
  have gradient:curlPair (modes M) z.1 z.1≤2*E/nu.coeff :=
    (le_div_iff₀ nu.coeff_pos).mpr (by nlinarith only [controlled.2.1,basic])
  have original:=input_pairing_bound M (input seed M time) z
  rw [pairing_symmetric (modes M) z,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  calc
    _ ≤ 2*(‖input seed M time‖*Real.sqrt (curlPair (modes M) z.1 z.1)) := mul_le_mul_of_nonneg_left original (by norm_num)
    _ ≤ 2*(cap nu*(1+NativeUnheatedSourceGradient.mass seed time)*Real.sqrt (2*E/nu.coeff)) := by
      gcongr
      · exact (norm_nonneg _).trans (normed time0 M)
      · exact normed time0 M
    _ = _ := by ring

theorem source_net_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ outerRadius M,∀ observation∈Icc 0 horizon,
      ∀ start finish (ordered : start≤finish),0 ≤ start →∀ᵐ time : ℝ,time∈Ioo start finish →
      let F:=integerWaveFrequencyCube outerRadius
      |deriv (energy seed observation M F radius start finish ordered) time+
        lyapunov seed observation M F radius time (q seed observation M F radius start finish ordered time)|≤
          2*cap nu*(1+NativeUnheatedSourceGradient.mass seed time)*
            Real.sqrt (2*energy seed observation M F radius start finish ordered time/nu.coeff) := by
  obtain ⟨first,derivative⟩ := source_energy_derivative seed horizon nonnegative
  obtain ⟨last,paid⟩ := source_input_bound seed horizon nonnegative
  refine ⟨max first last,fun radius above outerRadius M observation observed start finish ordered start0 => ?_⟩
  filter_upwards [derivative radius ((le_max_left _ _).trans above) M (integerWaveFrequencyCube outerRadius)
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) observation observed start finish ordered start0,
    paid radius ((le_max_right _ _).trans above) outerRadius M observation observed] with time actual bound inside
  dsimp only
  rw [(actual inside).deriv,neg_add_cancel_comm]
  exact bound (start0.trans inside.1.le) _

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
