import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.CanonicalEnergy
import H0mework.Versions.X.NavierStokes.MaterialReadback.Material

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeCanonicalAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (Fiber Space field realize)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWholeH1Mixed (modes)
open NativeWindowAbsoluteTimePhysicalMatter (Spinor WholeMatter extension coefficient temporal timeCoefficient spaceCoefficient)
open PhysicsCore.StageNineHolonomicField PhysicsCore.DiracExteriorMatterAction PhysicsCore.Stage9C.Material.SpinPair
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance physicalHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance materialFinite : Fintype MatterCoordinateIndex := Fintype.ofFinite MatterCoordinateIndex
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance fiberSeminormed : SeminormedAddCommGroup Fiber := (inferInstance : NormedAddCommGroup Fiber).toSeminormedAddCommGroup
local instance spaceSeminormed : SeminormedAddCommGroup Space := (inferInstance : NormedAddCommGroup Space).toSeminormedAddCommGroup
local instance historySeminormed : SeminormedAddCommGroup H := (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

def coordinateBasis (index : MatterCoordinateIndex) : MatterCoordinateCarrier := WithLp.toLp 2 (Pi.single index 1)

private theorem coordinate_expansion (v : MatterCoordinateCarrier) :
    (∑ index : MatterCoordinateIndex,v index • coordinateBasis index)=v := by
  apply PiLp.ext
  intro index
  simp [coordinateBasis,WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

private theorem functional_expansion (spin : Fin 4) (color : Fin 2) (v : MatterCoordinateCarrier) :
    (∑ index : MatterCoordinateIndex,NativeMaterialReadback.coefficient spin color (coordinateBasis index)*v index)=
      NativeMaterialReadback.coefficient spin color v := by
  have original:=congrArg (NativeMaterialReadback.coefficient spin color) (coordinate_expansion v)
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using original

def read (spin : Fin 4) (color : Fin 2) (value : WholeMatter) : Fiber :=
  ∑ index : MatterCoordinateIndex,NativeMaterialReadback.coefficient spin color (coordinateBasis index) • value index

theorem read_extension (spin : Fin 4) (color : Fin 2) (A : Module.End ℂ DiracExteriorMatterCarrier) (v : Spinor) :
    read spin color (extension A v)=∑ p : Fin 4,∑ q : Fin 2,
      NativeMaterialReadback.coefficient spin color (matterCoordinateEquiv
        (A (NativeWindowStageTenWholeFirstJet.materialBasis p q))) • v p q := by
  simp only [read,extension,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.sum_smul,functional_expansion]

private theorem read_basis (spin p : Fin 4) (color q : Fin 2) :
    NativeMaterialReadback.coefficient spin color
      (matterCoordinateEquiv (NativeWindowStageTenWholeFirstJet.materialBasis p q))=
      (Pi.single p (Pi.single q (1 : ℂ)) : Fin 4 → Fin 2 → ℂ) spin color := by
  change sourceColorDoubletDual color (matterCoordinateEquiv.symm
    (matterCoordinateEquiv (NativeWindowStageTenWholeFirstJet.materialBasis p q)) spin)=_
  rw [matterCoordinateEquiv.symm_apply_apply]
  exact sourceColorDoubletDual_diracMatter _ spin color

theorem read_identity (spin : Fin 4) (color : Fin 2) (v : Spinor) : read spin color (extension LinearMap.id v)=v spin color := by
  rw [read_extension]
  fin_cases spin <;> fin_cases color <;>
    simp [LinearMap.id_apply,read_basis,Pi.single_apply,Fin.sum_univ_four,Fin.sum_univ_two]

def net (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus)
    (spin : Fin 4) (color : Fin 2) : Fiber :=
  read spin color ((NativeCanonicalFluidCoframe.density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) : ℂ) •
    (NativeWindowAbsoluteTimePhysicalMatter.sourceForcing seed M time valid x-
      NativeWindowAbsoluteTimePhysicalMatter.retainedSpatial seed M time valid x))

theorem net_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus)
    (spin : Fin 4) (color : Fin 2) : net seed M time valid x spin color=temporal seed M time spin color x := by
  have original:=congrArg (fun value : WholeMatter => value-NativeWindowAbsoluteTimePhysicalMatter.retainedSpatial seed M time valid x)
    (NativeWindowAbsoluteTimePhysicalMatter.full_forcing_slot seed M time valid x)
  rw [add_sub_cancel_right] at original
  have scaled:=congrArg (fun value : WholeMatter =>
    (NativeCanonicalFluidCoframe.density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) : ℂ) • value) original
  have positive:=NativeCanonicalFluidCoframe.density_pos (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)
  simp only [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_smul] at scaled
  exact (congrArg (read spin color) scaled).trans (read_identity spin color _)

def netField (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (spin : Fin 4) (color : Fin 2) : C(Torus,Fiber) where
  toFun x := net seed M time valid x spin color
  continuous_toFun := by simpa only [net_original] using (temporal seed M time spin color).continuous

theorem netField_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (spin : Fin 4) (color : Fin 2) : netField seed M time valid spin color=temporal seed M time spin color :=
  ContinuousMap.ext fun x => net_original seed M time valid x spin color

def netSpace (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (spin : Fin 4) (color : Fin 2) : Space := (ContinuousMap.toLp 2 volume ℂ) (netField seed M time valid spin color)

theorem netSpace_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (spin : Fin 4) (color : Fin 2) : netSpace seed M time valid spin color=timeCoefficient seed M time spin color :=
  congrArg (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (netField_original seed M time valid spin color)

theorem source_coefficient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun t => coefficient seed M t spin color) (netSpace seed M time valid spin color) time := by
  rw [netSpace_original]
  exact NativeWindowAbsoluteTimePhysicalMatter.coefficient_hasDerivAt seed M time spin color


def shift (j : Coordinate) (displacement : ℝ) : Space →ₗᵢ[ℂ] Space :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Torus => x+NativePhysicalTranslation.displacement j displacement)
    (measurePreserving_add_right (volume : Measure Torus) (NativePhysicalTranslation.displacement j displacement))

theorem shift_field (j : Coordinate) (z : ℝ) (f : C(Torus,Fiber)) :
    shift j z ((ContinuousMap.toLp 2 volume ℂ) f)=
      (ContinuousMap.toLp 2 volume ℂ) (f.comp
        ⟨fun x => x+NativePhysicalTranslation.displacement j z,continuous_id.add continuous_const⟩) := by
  apply Lp.ext
  have preserves:=measurePreserving_add_right (volume : Measure Torus) (NativePhysicalTranslation.displacement j z)
  have shifted:=preserves.quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) f)
  filter_upwards [Lp.coeFn_compMeasurePreserving ((ContinuousMap.toLp 2 volume ℂ) f) preserves,shifted,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) (f.comp
      ⟨fun x => x+NativePhysicalTranslation.displacement j z,continuous_id.add continuous_const⟩)] with x first actual last
  exact (first.trans actual).trans last.symm

private theorem shift_real_inner (j : Coordinate) (z : ℝ) (u v : Space) :
    inner ℝ (shift j z u) (shift j z v)=inner ℝ u v := by
  have actual:=norm_add_sq_real (shift j z u) (shift j z v)
  rw [← map_add,LinearIsometry.norm_map,LinearIsometry.norm_map,LinearIsometry.norm_map] at actual
  linarith only [actual,norm_add_sq_real u v]

theorem shift_zero (j : Coordinate) (v : Space) : shift j 0 v=v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving v
    (measurePreserving_add_right (volume : Measure Torus) (NativePhysicalTranslation.displacement j 0))] with x actual
  simpa [shift,NativePhysicalTranslation.displacement] using actual

def mixedField (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (spin : Fin 4) (color : Fin 2) : C(Torus,Fiber) :=
  ∑ i : Coordinate,NativeRecoveryTimeCanonicalWrite.matterMatrix spin color i •
    field (modes M) i (NativeWindowAbsoluteTimeGradient.spatial M j (rate seed time))

def mixedSpace (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (spin : Fin 4) (color : Fin 2) : Space := (ContinuousMap.toLp 2 volume ℂ) (mixedField seed M time j spin color)

theorem mixed_time_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun t => spaceCoefficient seed M t j spin color) (mixedSpace seed M time j spin color) time := by
  have each (i : Coordinate) := ((realize (modes M) i).hasFDerivAt.comp_hasDerivAt (E := Space) (F := H) time
    (NativeWindowAbsoluteTimeGradient.source_spatial_hasDerivAt seed M j time)).const_smul
      (NativeRecoveryTimeCanonicalWrite.matterMatrix spin color i)
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ => each i) using 1
  · funext t
    simp only [spaceCoefficient,NativeWindowAbsoluteTimePhysicalMatter.spatial,map_sum,map_smul,
      Finset.sum_apply,Pi.smul_apply,Function.comp_apply]
    rfl
  · simp only [mixedSpace,mixedField,map_sum,map_smul]
    rfl

theorem net_spatial_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (j : Coordinate) (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun z => shift j z (netSpace seed M time valid spin color))
      (mixedSpace seed M time j spin color) 0 := by
  have each (i : Coordinate) := (NativeWindowAbsoluteTimeFourier.polynomial_spatial_strong (modes M)
    (fun k => NativeWindowAbsoluteTimeFourier.row k i (rate seed time)) j).const_smul
      (NativeRecoveryTimeCanonicalWrite.matterMatrix spin color i)
  have combined := (HasDerivAt.sum (u := Finset.univ) (fun i _ => each i)).const_add
    (NativeWindowAbsoluteTimePhysicalMatter.baseWeight spin color • ContinuousMap.const Torus
      (NativeWindowAbsoluteTimePhysicalMatter.backgroundRate time))
  have actual : HasDerivAt (fun z => (temporal seed M time spin color).comp
      ⟨fun x => x+NativePhysicalTranslation.displacement j z,continuous_id.add continuous_const⟩)
      (mixedField seed M time j spin color) 0 := by
    convert combined using 1
    · funext z
      apply ContinuousMap.ext
      intro x
      simp only [temporal,ContinuousMap.comp_apply,ContinuousMap.coe_mk,ContinuousMap.add_apply,
        ContinuousMap.sum_apply,ContinuousMap.smul_apply,ContinuousMap.const_apply,Finset.sum_apply,Pi.smul_apply,
        NativeWindowAbsoluteTimeFourier.translatedPolynomial,NativeWindowAbsoluteTimeFourier.field]
    · apply ContinuousMap.ext
      intro x
      simp only [mixedField,ContinuousMap.sum_apply,ContinuousMap.smul_apply]
      exact Finset.sum_congr rfl fun i _ => congrArg
        (fun v : Fiber => NativeRecoveryTimeCanonicalWrite.matterMatrix spin color i • v)
        (NativeWindowAbsoluteTimeFourier.field_spatial M i j (rate seed time) x)
  have lifted:=((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (E := Space) (F := C(Torus,Fiber)) 0 actual
  simpa only [netSpace,netField_original,shift_field,Function.comp_def,mixedSpace] using! lifted

-- The ordinary derivative is taken on the actual complete forcing/coefficient combination.
def netWord (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (word : Fin 4) (spin : Fin 4) (color : Fin 2) : Space :=
  Fin.cases (netSpace seed M time valid spin color)
    (fun j => deriv (fun z => shift j z (netSpace seed M time valid spin color)) 0) word

theorem netWord_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (word : Fin 4) (spin : Fin 4) (color : Fin 2) :
    netWord seed M time valid word spin color=NativeWindowAbsoluteTimeCanonicalEnergy.tangent seed M time word spin color := by
  have actual:=hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (NativeWindowAbsoluteTimeCanonicalEnergy.value_hasDerivAt seed M time word) spin) color
  cases word using Fin.cases with
  | zero => exact (source_coefficient seed M time valid spin color).unique actual
  | succ j =>
    change deriv (fun z => shift j z (netSpace seed M time valid spin color)) 0=_
    exact (net_spatial_derivative seed M time valid j spin color).deriv.trans
      ((mixed_time_derivative seed M time j spin color).unique actual)

def netPower (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) : ℝ :=
  ∑ word : Fin 4,∑ spin : Fin 4,∑ color : Fin 2,
    2*inner ℝ (NativeWindowAbsoluteTimeCanonicalEnergy.value seed M time word spin color)
      (netWord seed M time valid word spin color)

theorem netPower_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    netPower seed M time valid=NativeWindowAbsoluteTimeCanonicalEnergy.power seed M time := by
  simp only [netPower,netWord_original,NativeWindowAbsoluteTimeCanonicalEnergy.power]

theorem source_energy_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    HasDerivAt (NativeWindowAbsoluteTimeCanonicalEnergy.energy seed M) (netPower seed M time valid) time := by
  rw [netPower_original]
  exact NativeWindowAbsoluteTimeCanonicalEnergy.energy_hasDerivAt seed M time

theorem source_net_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time : Icc (0 : ℝ) horizon,
      NativeWindowAbsoluteTimeCanonicalEnergy.energy seed M time≤C ∧
      |netPower seed M time (by linarith [time.property.1])|≤C := by
  obtain ⟨C,C0,paid⟩:=NativeWindowAbsoluteTimeCanonicalEnergy.source_energy_power_bound seed horizon
  exact ⟨C,C0,fun M time => by simpa only [netPower_original] using paid M time time.property⟩

theorem native_net (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    netPower seed M time valid=(1/8:ℝ)*NativeWindowAbsoluteTimeActionWork.originalPower seed M time := by
  rw [netPower_original,NativeWindowAbsoluteTimeCanonicalEnergy.native_power]


def testSpace (F : Finset IntegerWavevector) (c : IntegerWavevector → Fiber) : Space :=
  (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (NativeWindowAbsoluteTimeFourier.polynomial F c)

theorem test_derivative (F : Finset IntegerWavevector) (c : IntegerWavevector → Fiber) (j : Coordinate) :
    HasDerivAt (fun z => shift j z (testSpace F c))
      (testSpace F (fun k => NativePhysicalGradient.multiplier k j • c k)) 0 := by
  have actual:=((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (E := Space) (F := C(Torus,Fiber)) 0 (NativeWindowAbsoluteTimeFourier.polynomial_spatial_strong F c j)
  simpa only [testSpace,shift_field,NativeWindowAbsoluteTimeFourier.translatedPolynomial,Function.comp_def] using! actual

/-- Ordinary weak differentiation of the complete actual force/coefficient combination. -/
theorem weak_first_word (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (j : Coordinate) (spin : Fin 4) (color : Fin 2) (F : Finset IntegerWavevector) (c : IntegerWavevector → Fiber) :
    inner ℝ (testSpace F c) (netWord seed M time valid j.succ spin color)=
      -inner ℝ (testSpace F (fun k => NativePhysicalGradient.multiplier k j • c k)) (netSpace seed M time valid spin color) := by
  have source:=net_spatial_derivative seed M time valid j spin color
  have test:=test_derivative F c j
  have paired:=test.inner ℝ source
  have constant : (fun z => inner ℝ (shift j z (testSpace F c)) (shift j z (netSpace seed M time valid spin color)))=
      fun _ => inner ℝ (testSpace F c) (netSpace seed M time valid spin color) := by
    funext z
    exact shift_real_inner j z _ _
  rw [constant] at paired
  have zero:=paired.unique (hasDerivAt_const 0 (inner ℝ (testSpace F c) (netSpace seed M time valid spin color)))
  simp only [shift_zero] at zero
  change inner ℝ (testSpace F c) (deriv (fun z => shift j z (netSpace seed M time valid spin color)) 0)=_
  rw [source.deriv]
  linarith only [zero]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem netPower_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    netPower seed M (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos])=
      netPower step.1 M time (by linarith) := by
  simp only [netPower_original]
  exact (NativeWindowAbsoluteTimeCanonicalEnergy.energy_power_next seed M step generated time nonnegative).2

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeCanonicalAction
