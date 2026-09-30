import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerSource
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassChangedRead

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherPhysicalBudget
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (Fiber Space row field polynomial)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowAbsoluteTimePhysicalMatter (support coefficientRow matter spatial background baseWeight)
open NativeRecoveryTimeCanonicalWrite (matterMatrix)
open NativeWindowAbsoluteTimeCanonicalEnergy (program program_mass)
open NativeWindowAbsoluteMassChangedRead (rowMass rowGradient canonicalSecondCost)
open NativeWholeH1Mixed (modes modes_zero)
open NativeWindowGreenTestForm (SpinFiber)
open NativeWindowMotherJetProduct (energy)
open NativeUnheatedSexticLatticePower (radical radical_fourth mass)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance fiberSeminormed : SeminormedAddCommGroup Fiber := (inferInstance : NormedAddCommGroup Fiber).toSeminormedAddCommGroup
local instance historySeminormed : SeminormedAddCommGroup H := (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

private def material (b : Fiber) (u : Coordinate → Fiber) : SpinFiber Fiber :=
  WithLp.toLp 2 fun entry => baseWeight entry.1 entry.2 • b+∑i : Coordinate,matterMatrix entry.1 entry.2 i • u i

private theorem material_program (b : Fiber) (u : Coordinate → Fiber) :
    material b u=WithLp.toLp 2 fun entry : Fin 4 × Fin 2 => program b u entry.1 entry.2 := by
  apply PiLp.ext
  intro entry
  rcases entry with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [material,program,NativeRecoveryTimeCanonical.matterProgram,baseWeight,matterMatrix,Fin.sum_univ_three] <;> module

private theorem material_square (b : Fiber) (u : Coordinate → Fiber) :
    ‖material b u‖^2=2*‖b‖^2+(1/8:ℝ)*∑i : Coordinate,‖u i‖^2 := by
  rw [material_program,PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type]
  exact program_mass b u

private def coefficients (M : ℕ) (b : Fiber) (v : H) (k : IntegerWavevector) : SpinFiber Fiber :=
  material (if k=0 then b else 0) (fun i => if k∈modes M then row k i v else 0)

private theorem coefficients_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    coefficients M (background time) (history seed time)=coefficientRow seed M time := by
  funext k
  apply PiLp.ext
  intro entry
  simp only [coefficients,material,coefficientRow,PiLp.toLp_apply]
  split_ifs <;> simp

private theorem coefficients_square (M : ℕ) (b : Fiber) (v : H) (k : IntegerWavevector) :
    ‖coefficients M b v k‖^2=(if k=0 then 2*‖b‖^2 else 0)+
      if k∈modes M then (1/8:ℝ)*∑i : Coordinate,‖row k i v‖^2 else 0 := by
  rw [coefficients,material_square]
  split_ifs <;> simp

private theorem coefficients_polynomial (M : ℕ) (b : Fiber) (v : H) (x : Torus) :
    polynomial (support M) (coefficients M b v) x=WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 =>
      baseWeight entry.1 entry.2 • b+∑i : Coordinate,matterMatrix entry.1 entry.2 i • field (modes M) i v x) := by
  apply PiLp.ext
  intro entry
  simp only [polynomial,ContinuousMap.coe_mk,support,Finset.sum_insert (modes_zero M),coefficients,material,
    WithLp.ofLp_sum,WithLp.ofLp_add,WithLp.ofLp_smul,Finset.sum_apply,Pi.add_apply,Pi.smul_apply,
    ite_true,if_neg (modes_zero M),smul_zero,Finset.sum_const_zero,add_zero,UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply,one_smul]
  congr 1
  have each (k : IntegerWavevector) (inside : k∈modes M) :
      UnitAddTorus.mFourier k x • (baseWeight entry.1 entry.2 • (if k=0 then b else 0)+
        ∑i : Coordinate,matterMatrix entry.1 entry.2 i • (if k∈modes M then row k i v else 0))=
          ∑i : Coordinate,matterMatrix entry.1 entry.2 i • (UnitAddTorus.mFourier k x • row k i v) := by
    have nonzero:k≠0:=fun eq => modes_zero M (eq ▸ inside)
    simp only [if_neg nonzero,if_pos inside,smul_zero,zero_add,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [Finset.sum_congr rfl each,Finset.sum_comm]
  simp only [NativeWindowAbsoluteTimeFourier.field,polynomial,ContinuousMap.coe_mk,Finset.smul_sum]

theorem polynomial_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    polynomial (support M) (coefficientRow seed M time) x=
      WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter seed M time entry.1 entry.2 x) := by
  rw [← coefficients_original,coefficients_polynomial]
  rfl

def spatialRow (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) (k : IntegerWavevector) : SpinFiber Fiber :=
  NativePhysicalGradient.multiplier k j • coefficientRow seed M time k

private theorem material_smul (a : ℂ) (b : Fiber) (u : Coordinate → Fiber) :
    a • material b u=material (a • b) (fun i => a • u i) := by
  apply PiLp.ext
  intro entry
  simp only [material,PiLp.toLp_apply,PiLp.smul_apply,smul_add,Finset.smul_sum]
  congr 1
  · exact smul_comm _ _ _
  · exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem coefficients_scalar (M : ℕ) (b : Fiber) (v w : H) (a : IntegerWavevector → ℂ)
    (zero : a 0=0) (read : ∀ k∈modes M,∀ i,row k i w=a k • row k i v) :
    (fun k => a k • coefficients M b v k)=coefficients M 0 w := by
  funext k
  have base : a k • (if k=0 then b else 0)=0 := by
    by_cases equal:k=0
    · simp only [equal,ite_true,zero,zero_smul]
    · simp only [if_neg equal,smul_zero]
  have values : (fun i => a k • (if k∈modes M then row k i v else 0))=
      (fun i => if k∈modes M then row k i w else 0) := by
    funext i
    by_cases inside:k∈modes M
    · simp only [if_pos inside]
      exact (read k inside i).symm
    · simp only [if_neg inside,smul_zero]
  change a k • material (if k=0 then b else 0) (fun i => if k∈modes M then row k i v else 0)=_
  rw [material_smul,base,values]
  simp only [coefficients,ite_self]

private theorem coefficients_spatial (M : ℕ) (b : Fiber) (v : H) (j : Coordinate) :
    (fun k => NativePhysicalGradient.multiplier k j • coefficients M b v k)=
      coefficients M 0 (NativeWindowAbsoluteTimeGradient.spatial M j v) := by
  apply coefficients_scalar
  · simp [NativePhysicalGradient.multiplier,complexWavevector]
  · intro k inside i
    exact NativeWindowAbsoluteTimeFourier.row_spatial M j k inside i v

private theorem spatial_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    spatialRow seed M time j=coefficients M 0 (NativeWindowAbsoluteTimeGradient.spatial M j (history seed time)) := by
  have original : spatialRow seed M time j=(fun k => NativePhysicalGradient.multiplier k j •
      coefficients M (background time) (history seed time) k) := by
    rw [coefficients_original]
    rfl
  exact original.trans (coefficients_spatial M _ _ j)

theorem spatial_polynomial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) (x : Torus) :
    polynomial (support M) (spatialRow seed M time j) x=
      WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => spatial seed M time j entry.1 entry.2 x) := by
  rw [spatial_row,coefficients_polynomial]
  apply PiLp.ext
  intro entry
  simp only [smul_zero,zero_add,spatial,ContinuousMap.sum_apply,ContinuousMap.smul_apply]

private theorem supported_sum (M : ℕ) (B : ℝ) (a w : IntegerWavevector → ℝ) :
    (∑k∈support M,w k*((if k=0 then B else 0)+(if k∈modes M then a k else 0)))=
      w 0*B+∑k∈modes M,w k*a k := by
  rw [support,Finset.sum_insert (modes_zero M)]
  simp only [ite_true,if_neg (modes_zero M),add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k inside
  have nonzero:k≠0:=fun h => modes_zero M (h ▸ inside)
  rw [if_neg nonzero,if_pos inside,zero_add]

private theorem coefficient_mass (M : ℕ) (b : Fiber) (v : H) :
    (∑k∈support M,‖coefficients M b v k‖^2)=2*‖b‖^2+(1/8:ℝ)*rowMass M v := by
  have source:=supported_sum M (2*‖b‖^2) (fun k => (1/8:ℝ)*∑i : Coordinate,‖row k i v‖^2) (fun _ => 1)
  simp only [one_mul,← coefficients_square] at source
  rw [source]
  simp only [rowMass,← Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem coefficient_gradient (M : ℕ) (b : Fiber) (v : H) :
    (∑k∈support M,integerWaveNormSq k*‖coefficients M b v k‖^2)=(1/8:ℝ)*rowGradient M v := by
  have source:=supported_sum M (2*‖b‖^2) (fun k => (1/8:ℝ)*∑i : Coordinate,‖row k i v‖^2) integerWaveNormSq
  have atZero : integerWaveNormSq (0 : IntegerWavevector)=0 := by simp [integerWaveNormSq]
  simp only [← coefficients_square,atZero,zero_mul,zero_add] at source
  rw [source]
  simp only [rowGradient,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem energy_split (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber Fiber) :
    energy F u=(∑k∈F,‖u k‖^2)+∑k∈F,integerWaveNormSq k*‖u k‖^2 := by
  simp only [energy,radical_fourth,mass,add_mul,one_mul,Finset.sum_add_distrib]

private theorem coefficients_energy (M : ℕ) (b : Fiber) (v : H) :
    energy (support M) (coefficients M b v)=2*‖b‖^2+(1/8:ℝ)*(rowMass M v+rowGradient M v) := by
  rw [energy_split,coefficient_mass,coefficient_gradient]
  ring

theorem coefficient_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    energy (support M) (coefficientRow seed M time)=2+(1/8:ℝ)*(rowMass M (history seed time)+rowGradient M (history seed time)) := by
  rw [← coefficients_original,coefficients_energy,NativeWindowAbsoluteTimeCanonicalEnergy.background_mass]
  ring

theorem spatial_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    (∑k∈support M,‖spatialRow seed M time j k‖^2)=
      (1/8:ℝ)*rowMass M (NativeWindowAbsoluteTimeGradient.spatial M j (history seed time)) := by
  have read:=congrArg (fun c : IntegerWavevector → SpinFiber Fiber => ∑k∈support M,‖c k‖^2) (spatial_row seed M time j)
  exact read.trans (by simpa using coefficient_mass M 0 (NativeWindowAbsoluteTimeGradient.spatial M j (history seed time)))

theorem spatial_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    energy (support M) (spatialRow seed M time j)=
      (∑k∈support M,‖spatialRow seed M time j k‖^2)+canonicalSecondCost seed M time j/(2*Real.pi)^2 := by
  let v:=NativeWindowAbsoluteTimeGradient.spatial M j (history seed time)
  have read:=congrArg (energy (support M)) (spatial_row seed M time j)
  have value : energy (support M) (spatialRow seed M time j)=(1/8:ℝ)*(rowMass M v+rowGradient M v) :=
    read.trans (by simpa using coefficients_energy M 0 v)
  have massRead : (∑k∈support M,‖spatialRow seed M time j k‖^2)=(1/8:ℝ)*rowMass M v := spatial_mass seed M time j
  have cost : canonicalSecondCost seed M time j=(1/8:ℝ)*((2*Real.pi)^2*rowGradient M v) := by
    rw [NativeWindowAbsoluteMassChangedRead.canonical_second_cost,NativeWindowAbsoluteMassChangedRead.secondCost,
      NativeWindowAbsoluteMassChangedRead.dirichlet_original]
  rw [value,massRead,cost]
  field_simp [Real.pi_ne_zero]


private theorem differentiated_mass (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber Fiber) :
    (∑d : Coordinate,∑k∈F,‖NativePhysicalGradient.multiplier k d • u k‖^2)=
      (2*Real.pi)^2*(∑k∈F,integerWaveNormSq k*‖u k‖^2) := by
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [norm_smul,mul_pow,NativePhysicalGradient.multiplier_norm_sq,← Finset.sum_mul,
    ← Finset.mul_sum,integerWaveNormSq]
  ring

theorem second_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    (∑d : Coordinate,∑k∈support M,‖NativePhysicalGradient.multiplier k d • spatialRow seed M time j k‖^2)=
      canonicalSecondCost seed M time j := by
  let v:=NativeWindowAbsoluteTimeGradient.spatial M j (history seed time)
  have read:=congrArg (fun c : IntegerWavevector → SpinFiber Fiber =>
    ∑k∈support M,integerWaveNormSq k*‖c k‖^2) (spatial_row seed M time j)
  have gradient : (∑k∈support M,integerWaveNormSq k*‖spatialRow seed M time j k‖^2)=(1/8:ℝ)*rowGradient M v :=
    read.trans (coefficient_gradient M 0 v)
  rw [differentiated_mass,gradient,NativeWindowAbsoluteMassChangedRead.canonical_second_cost,
    NativeWindowAbsoluteMassChangedRead.secondCost,NativeWindowAbsoluteMassChangedRead.dirichlet_original]
  ring

private theorem row_mass_projected (M : ℕ) (v : H) : rowMass M v=
    ‖(NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v‖^2 := by
  have source:=NativeWindowAbsoluteTimeFourier.physical_mass_exact M v
  change (∑i : Coordinate,‖NativeWindowAbsoluteTimeFourier.physical (modes M) i v‖^2)=_ at source
  simpa only [rowMass,NativeWindowAbsoluteTimeFourier.physical_square] using source

theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time∈Icc 0 horizon,
      energy (support M) (coefficientRow seed M time)≤C ∧∀ j,
        (∑k∈support M,‖spatialRow seed M time j k‖^2)≤C ∧
          energy (support M) (spatialRow seed M time j)≤C+canonicalSecondCost seed M time j/(2*Real.pi)^2 := by
  obtain ⟨L,L0,paid⟩:=NativeWindowAbsoluteTimeEnergy.source_first_jet_bound seed horizon
  refine ⟨2+L,by positivity,fun M time inside => ?_⟩
  have state (d : Fin 4) : ‖NativeWindowAbsoluteTimeEnergy.value seed M time d‖^2≤L := by
    have original:=paid M d time inside
    linarith only [original,sq_nonneg ‖NativeWindowAbsoluteTimeEnergy.tangent seed M time d‖]
  have first : rowMass M (history seed time)≤L := by
    rw [row_mass_projected]
    exact state 0
  have each (j : Coordinate) : ‖NativeWindowAbsoluteTimeGradient.spatial M j (history seed time)‖^2≤L := state j.succ
  have gradient : rowGradient M (history seed time)≤3*L := by
    have total:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun j _ => each j)
    have bounded:NativeWindowAbsoluteMassChangedRead.dirichlet M (history seed time)≤3*L :=
      (NativeWindowAbsoluteMassChangedRead.dirichlet_le M (history seed time)).trans (by simpa using total)
    rw [NativeWindowAbsoluteMassChangedRead.dirichlet_original] at bounded
    have factor : 1≤(2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
    nlinarith only [bounded,mul_nonneg (sub_nonneg.mpr factor) (NativeWindowAbsoluteMassChangedRead.gradient_nonnegative M (history seed time))]
  constructor
  · rw [coefficient_energy]
    linarith
  · intro j
    have massBound : (∑k∈support M,‖spatialRow seed M time j k‖^2)≤2+L := by
      have bound:rowMass M (NativeWindowAbsoluteTimeGradient.spatial M j (history seed time))≤L :=
        (NativeWindowAbsoluteMassChangedRead.row_mass_le M _).trans (each j)
      rw [spatial_mass]
      linarith
    refine ⟨massBound,?_⟩
    rw [spatial_energy]
    exact add_le_add massBound le_rfl


theorem source_lower_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ (time : ℝ) (inside : time∈Icc 0 horizon),
      let valid : -1<time := by linarith [inside.1]
      MemLp (fun x : Torus => NativeWindowAbsoluteLowerBound.lift (NativeWindowMotherLowerProduct.point seed time valid x)
        (polynomial (support M) (coefficientRow seed M time) x)) 2 volume ∧
      (∫x : Torus,‖NativeWindowAbsoluteLowerBound.lift (NativeWindowMotherLowerProduct.point seed time valid x)
        (polynomial (support M) (coefficientRow seed M time) x)‖^2)≤C ∧∀ j,
      MemLp (fun x : Torus => NativeWindowAbsoluteLowerBound.lift (NativeWindowMotherLowerProduct.point seed time valid x)
        (polynomial (support M) (spatialRow seed M time j) x)) 2 volume ∧
      (∫x : Torus,‖NativeWindowAbsoluteLowerBound.lift (NativeWindowMotherLowerProduct.point seed time valid x)
        (polynomial (support M) (spatialRow seed M time j) x)‖^2)≤C*canonicalSecondCost seed M time j+C := by
  obtain ⟨L,L0,paid⟩:=source_energy seed horizon
  let B:=NativeWindowMotherLowerProduct.budget seed horizon
  have B0:0≤B:=NativeWindowMotherLowerProduct.budget_nonnegative seed horizon
  refine ⟨B*(L+1),by positivity,fun M time inside => ?_⟩
  let valid : -1<time:=by linarith [inside.1]
  have state:=paid M time inside
  have first:=NativeWindowMotherLowerProduct.source_product seed time horizon valid inside.2 (support M) (coefficientRow seed M time)
  refine ⟨first.1,?_,fun j => ?_⟩
  · exact first.2.trans ((mul_le_mul_of_nonneg_left state.1 B0).trans (by dsimp only [B]; nlinarith only [B0]))
  · have last:=NativeWindowMotherLowerProduct.source_product seed time horizon valid inside.2 (support M) (spatialRow seed M time j)
    refine ⟨last.1,?_⟩
    have cost0:0≤canonicalSecondCost seed M time j :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have factor : 1≤(2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
    have fraction:canonicalSecondCost seed M time j/(2*Real.pi)^2≤canonicalSecondCost seed M time j :=
      div_le_self cost0 factor
    have bound:=mul_le_mul_of_nonneg_left ((state.2 j).2.trans (add_le_add le_rfl fraction)) B0
    apply last.2.trans (bound.trans ?_)
    nlinarith only [B0,mul_nonneg B0 L0,mul_nonneg (mul_nonneg B0 L0) cost0]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

private theorem mass_clock (M : ℕ) (advance : ℝ) (v : H) :
    rowMass M (NativeWindowAbsoluteTimeIsometry.clock NativeWholeResolvent.wholePhysical advance v)=rowMass M v := by
  simp only [rowMass,NativeWindowAbsoluteMassChangedRead.row_clock,LinearIsometry.norm_map]

theorem energy_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    energy (support M) (coefficientRow seed M (step.2.clockAdvance+time))=
      energy (support M) (coefficientRow step.1 M time) := by
  simp only [coefficient_energy,NativeWindowAbsoluteTimeBridge.source_next seed step generated time nonnegative,
    mass_clock,NativeWindowAbsoluteMassChangedRead.gradient_clock]

theorem spatial_mass_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) (j : Coordinate) :
    (∑k∈support M,‖spatialRow seed M (step.2.clockAdvance+time) j k‖^2)=
      ∑k∈support M,‖spatialRow step.1 M time j k‖^2 := by
  have source:=congrArg (rowMass M) (NativeWindowAbsoluteTimeEnergy.value_next seed M step generated time nonnegative j.succ)
  rw [mass_clock] at source
  rw [spatial_mass,spatial_mass]
  exact congrArg (fun r : ℝ => (1/8:ℝ)*r) source

theorem spatial_energy_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) (j : Coordinate) :
    energy (support M) (spatialRow seed M (step.2.clockAdvance+time) j)=
      energy (support M) (spatialRow step.1 M time j) := by
  rw [spatial_energy,spatial_energy,spatial_mass_next seed M step generated time nonnegative j,
    NativeWindowAbsoluteMassChangedRead.second_cost_next seed M step generated time nonnegative j]

end
end SaturationMonoid.NavierStokes.NativeWindowMotherPhysicalBudget
