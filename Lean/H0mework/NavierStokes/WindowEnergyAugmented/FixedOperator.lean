import H0mework.NavierStokes.WindowEnergyAugmented.SourceForm

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedFixedOperator
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open NativeFiniteActionResolvent NativeResolventAdjoint NativeWindowOperatorGreen NativeWindowStressOseenTest
open NativeResolventCompactness NativeUnheatedGlobalNegativeOne NativeWindowAugmentedSourceForm
noncomputable section
variable {nu : Viscosity}

def rowRead (M : Finset IntegerWavevector) (wave : IntegerWavevector) (coordinate : Coordinate) :
    physicalSpace M →ₗ[ℝ] ℂ :=
  (ContinuousLinearMap.proj coordinate).toLinearMap.comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).toLinearMap.comp (physicalSpace M).subtype)

def spectral (nu : Viscosity) (M L : Finset IntegerWavevector) :
    physicalSpace M →ₗ[ℝ] physicalSpace M →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ wave ∈ L,∑ coordinate : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier wave)*
    inner ℝ (rowRead M wave coordinate x) (rowRead M wave coordinate y))
    (fun _ _ _ => by simp only [map_add,inner_add_left,mul_add,Finset.sum_add_distrib])
    (fun _ _ _ => by
      simp only [map_smul,real_inner_smul_left,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave _
      apply Finset.sum_congr rfl
      intro coordinate _
      ring)
    (fun _ _ _ => by simp only [map_add,inner_add_right,mul_add,Finset.sum_add_distrib])
    (fun _ _ _ => by
      simp only [map_smul,real_inner_smul_right,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave _
      apply Finset.sum_congr rfl
      intro coordinate _
      ring)

def matrixPhysicalForm (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) : physicalSpace M →ₗ[ℝ] physicalSpace M →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ output : Coordinate,∑ input : Coordinate,
    matrixRead seed observation F radius output input (evaluate M F output x*evaluate M F input y))
    (fun _ _ _ => by simp only [map_add,add_mul,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,smul_mul_assoc,Finset.smul_sum])
    (fun _ _ _ => by simp only [map_add,mul_add,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,mul_smul_comm,Finset.smul_sum])

def physicalForm (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M L F : Finset IntegerWavevector) (radius : ℕ) :
    physicalSpace M →ₗ[ℝ] physicalSpace M →ₗ[ℝ] ℝ :=
  spectral nu M L+matrixPhysicalForm seed observation M F radius

def test (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M L F : Finset IntegerWavevector) (radius : ℕ) : Module.End ℝ (physicalSpace M) :=
  (duality M).symm.toLinearMap.comp (physicalForm seed observation M L F radius).flip

theorem test_pairing (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M L F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace M) :
    pairing M x (test seed observation M L F radius y)=physicalForm seed observation M L F radius x y := by
  have generated := congrArg (fun f : Module.Dual ℝ (physicalSpace M) => f x)
    ((duality M).apply_symm_apply ((physicalForm seed observation M L F radius).flip y))
  change pairing M (test seed observation M L F radius y) x=_ at generated
  rw [pairing_symmetric] at generated
  exact generated

theorem read_equal (M F : Finset IntegerWavevector) (value : physicalSpace M) (data : State)
    (same : ∀ wave∈F,∀ coordinate,NativeUnheatedTriadRows.decode wave coordinate data=rowRead M wave coordinate value)
    (coordinate : Coordinate) : NativeWindowStressHeatTime.read F coordinate data=evaluate M F coordinate value := by
  rw [NativeWindowStressHeatBalance.read_apply,evaluate_apply]
  apply Finset.sum_congr rfl
  intro wave inside
  exact congrArg (NativeWindowStressHeatBalance.basis wave) (same wave inside coordinate)

theorem source_pairing (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M L F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace M) (left right : State)
    (first : ∀ wave∈L∪F,∀ coordinate,NativeUnheatedTriadRows.decode wave coordinate left=rowRead M wave coordinate x)
    (last : ∀ wave∈L∪F,∀ coordinate,NativeUnheatedTriadRows.decode wave coordinate right=rowRead M wave coordinate y) :
    NativeWindowAugmentedSourceForm.form seed observation L F radius left right=
      pairing M x (test seed observation M L F radius y) := by
  have leftRead := read_equal M F x left (fun wave inside => first wave (Finset.mem_union_right L inside))
  have rightRead := read_equal M F y right (fun wave inside => last wave (Finset.mem_union_right L inside))
  rw [test_pairing,physicalForm]
  simp only [NativeWindowAugmentedSourceForm.form,NativeWindowAugmentedSourceForm.spectralForm,
    NativeWindowAugmentedSourceForm.matrixForm,add_apply,sum_apply,smul_apply,
    ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,smul_eq_mul,
    leftRead,rightRead]
  change (∑ wave ∈ L,∑ coordinate : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier wave)*
      inner ℝ (NativeUnheatedTriadRows.decode wave coordinate left) (NativeUnheatedTriadRows.decode wave coordinate right))+
      (∑ output : Coordinate,∑ input : Coordinate,inner ℝ
        (NativeWindowAugmentedSourceForm.matrixField seed observation F radius output input)
        (NativeWindowStressHeatSource.physical (evaluate M F output x*evaluate M F input y)))=
      spectral nu M L x y+matrixPhysicalForm seed observation M F radius x y
  have spec : (∑ wave ∈ L,∑ coordinate : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier wave)*
      inner ℝ (NativeUnheatedTriadRows.decode wave coordinate left) (NativeUnheatedTriadRows.decode wave coordinate right))=
      spectral nu M L x y := by
    apply Finset.sum_congr rfl
    intro wave inside
    simp only [first wave (Finset.mem_union_left F inside),last wave (Finset.mem_union_left F inside)]
  rw [spec]
  rfl

theorem whole_green (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M L F : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M) (radius : ℕ)
    (advector : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality advector) (value : physicalSpace M) :
    let A:=physicalOperator M zero closed nu advector reality
    let B:=test seed observation M L F radius
    pairing M (A value) (B value)+pairing M value (B (A value))=
      pairing M value (lyapunov M zero closed nu advector reality B value) :=
  NativeWindowOperatorGreen.whole_green M zero closed nu advector reality _ value

theorem convection_green (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M L F : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M) (radius : ℕ)
    (advector : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality advector) (value : physicalSpace M) :
    let K:=convection M zero closed nu advector reality
    let B:=test seed observation M L F radius
    pairing M (K value) (B value)+pairing M value (B (K value))=
      pairing M value (B (K value)-K (B value)) := by
  dsimp only
  rw [map_sub]
  have skew := convection_skew M zero closed nu advector reality value (test seed observation M L F radius value)
  linarith only [skew]


open NativeWholeH1Mixed NativeWindowStressOseenSource NativeUnheatedSourceQuadraticApprox

theorem load_reads (seed : GeneratedWholeRestartCurrent nu) (sample : ℝ) (nonnegative : 0 ≤ sample)
    (M : ℕ) (waves : Finset IntegerWavevector) (cover : ∀ wave∈waves,wave≠0 →wave∈modes M) :
    ∀ wave∈waves,∀ coordinate,NativeUnheatedTriadRows.decode wave coordinate (state seed sample)=
      rowRead (modes M) wave coordinate (load M seed sample) := by
  intro wave inside coordinate
  change NativeUnheatedTriadRows.velocity seed sample wave coordinate=(load M seed sample).1 wave coordinate
  rw [NativeUnheatedTriadRows.velocity_original]
  by_cases zero : wave=0
  · subst wave
    rw [physical_supported _ 0 (modes_zero M)]
    simp [NativeEndpointVelocityCarrier.wholeVelocity_zero]
  · change _=(restrict M (physicalSource seed sample)).1 wave coordinate
    rw [restrict_row,if_pos (cover wave inside zero),physicalSource,dif_pos nonnegative]
    rfl

theorem action_reads (seed : GeneratedWholeRestartCurrent nu) (sample : ℝ) (M : ℕ)
    (waves : Finset IntegerWavevector) (cover : ∀ wave∈waves,wave≠0 →wave∈modes M) :
    ∀ wave∈waves,∀ coordinate,NativeUnheatedTriadRows.decode wave coordinate (value M seed sample)=
      rowRead (modes M) wave coordinate (K M seed sample (load M seed sample)) := by
  intro wave inside coordinate
  change _=(K M seed sample (load M seed sample)).1 wave coordinate
  by_cases zero : wave=0
  · subst wave
    rw [physical_supported _ 0 (modes_zero M)]
    simp [NativeUnheatedTriadRows.decode_apply,NativeEndpointVelocityCarrier.wholeVelocity_zero]
  · exact (NativeWindowStressOseenSource.action_original M seed sample wave coordinate (cover wave inside zero)).symm

theorem gradient_decode_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ sample : ℝ,0 ≤ sample →∀ wave coordinate,
      NativeUnheatedTriadRows.decode wave coordinate (NativeWindowHistoryGradient.gradientState seed sample)=
        integerWaveViscousMultiplier wave • NativeUnheatedTriadRows.velocity seed sample wave coordinate := by
  filter_upwards [NativeUnheatedTriadRows.derivative_split_ae seed] with sample original nonnegative wave coordinate
  simp only [NativeWindowHistoryGradient.gradientState,map_smul,map_sub]
  change nu.coeff⁻¹ • (NativeUnheatedTriadRows.action seed sample wave coordinate-
    NativeUnheatedTriadRows.derivative seed sample wave coordinate)=_
  rw [original nonnegative,sub_sub_cancel,smul_smul]
  congr 1
  field_simp [nu.coeff_pos.ne']

def approximateRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius M : ℕ) (sample : ℝ) : ℝ :=
  NativeWindowAugmentedSourceForm.form seed observation L F radius (value M seed sample) (state seed sample)+
    NativeWindowAugmentedSourceForm.form seed observation L F radius (state seed sample) (value M seed sample)-
      nu.coeff*viscousRate seed observation L F radius sample

theorem approximate_green_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius M : ℕ)
    (cover : ∀ wave∈L∪F,wave≠0 →wave∈modes M) :
    ∀ᵐ sample : ℝ,0 ≤ sample →approximateRate seed observation L F radius M sample=
      pairing (modes M) (load M seed sample)
        (lyapunov (modes M) (modes_zero M) (modes_closed M) nu (advector M seed sample) (advector_reality M seed sample)
          (test seed observation (modes M) L F radius) (load M seed sample)) := by
  filter_upwards [gradient_decode_ae seed] with sample gradient nonnegative
  let U:=load M seed sample
  let lap:=laplacian (modes M) (modes_zero M) (modes_closed M) nu
  have uread := load_reads seed sample nonnegative M (L∪F) cover
  have nread := action_reads seed sample M (L∪F) cover
  have dread : ∀ wave∈L∪F,∀ coordinate,NativeUnheatedTriadRows.decode wave coordinate
      (NativeWindowHistoryGradient.gradientState seed sample)=rowRead (modes M) wave coordinate (lap U) := by
    intro wave inside coordinate
    rw [gradient nonnegative,NativeUnheatedTriadRows.velocity,uread wave inside]
    change _=(lap U).1 wave coordinate
    rw [laplacian_row]
    rfl
  rw [← whole_green seed observation (modes M) L F (modes_zero M) (modes_closed M) radius
    (advector M seed sample) (advector_reality M seed sample) (load M seed sample)]
  unfold approximateRate viscousRate
  rw [source_pairing seed observation (modes M) L F radius _ _ _ _ nread uread,
    source_pairing seed observation (modes M) L F radius _ _ _ _ uread nread,
    source_pairing seed observation (modes M) L F radius _ _ _ _ dread uread,
    source_pairing seed observation (modes M) L F radius _ _ _ _ uread dread]
  rw [operator_split]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,smul_eq_mul]
  change _=_
  dsimp only [K,lap,U]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedFixedOperator
