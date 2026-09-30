import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerReadback
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerSource
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerPhysicalBudget
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerForcing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowWeakLowerSource
open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open NativeWindowAbsoluteTimeFourier (polynomial)
open NativeWindowGreenTestForm (SpinFiber)
open NativeWindowWeakLowerReadback (read readCap operator lift_original read_norm)
open NativeWindowWeakLowerTranslation (pairing orbit derivative)
open NativeWindowMotherJetProduct (energy)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (x : Torus) : SpinFiber E →L[ℂ] SpinFiber E :=
  operator (NativeWindowMotherLowerProduct.point seed time valid x)

def input (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    Lp (SpinFiber E) 2 (volume : Measure Torus) := (ContinuousMap.toLp 2 volume ℂ) (polynomial F u)

theorem input_ae (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    input F u=ᵐ[volume] polynomial F u :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (polynomial F u)

theorem input_mass (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    ‖input F u‖^2=∑ k∈F,‖u k‖^2 := by
  rw [NativeWindowHilbertHalfProduct.lp_square]
  exact (integral_congr_ae ((input_ae F u).fun_comp (fun v => ‖v‖^2))).trans
    (NativeWindowAbsoluteTimeFourier.polynomial_square F u)

theorem source_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    MemLp (fun x : Torus => field (E := E) seed time valid x (polynomial F u x)) 2 volume := by
  have paid:=(NativeWindowMotherLowerProduct.source_product seed time time valid le_rfl F u).1
  simpa only [Function.comp_apply,field,operator,ContinuousLinearMap.comp_apply,lift_original] using!
    (read (E := E)).comp_memLp' paid

def output (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    Lp (SpinFiber E) 2 (volume : Measure Torus) :=
  (source_memLp seed time valid F u).toLp (fun x => field (E := E) seed time valid x (polynomial F u x))

theorem output_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    output seed time valid F u=ᵐ[volume] fun x => field (E := E) seed time valid x (polynomial F u x) :=
  (source_memLp seed time valid F u).coeFn_toLp

theorem output_square (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    ‖output seed time valid F u‖^2=∫ x : Torus,‖field (E := E) seed time valid x (polynomial F u x)‖^2 := by
  rw [NativeWindowHilbertHalfProduct.lp_square]
  exact integral_congr_ae ((output_ae seed time valid F u).fun_comp (fun v => ‖v‖^2))

theorem output_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    ‖output seed time valid F u‖^2 ≤ readCap^2*NativeWindowMotherLowerProduct.budget seed horizon*energy F u := by
  have full:=NativeWindowMotherLowerProduct.source_product seed time horizon valid before F u
  have regular:=(source_memLp seed time valid F u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have integrable:=full.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [output_square]
  have paid:=integral_mono_ae regular (integrable.const_mul (readCap^2)) (Eventually.of_forall fun x => by
    have norm:=read_norm (NativeWindowAbsoluteLowerBound.lift (NativeWindowMotherLowerProduct.point seed time valid x) (polynomial F u x))
    have squared:=sq_le_sq₀ (norm_nonneg _) (mul_nonneg NativeWindowWeakLowerReadback.readCap_nonnegative (norm_nonneg _)) |>.mpr norm
    simpa only [field,operator,ContinuousLinearMap.comp_apply,lift_original,mul_pow] using squared)
  rw [integral_const_mul] at paid
  exact paid.trans ((mul_le_mul_of_nonneg_left full.2 (sq_nonneg readCap)).trans_eq (by ring))

theorem source_regular (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) :
    ∀ u v : SpinFiber E,Integrable (fun x : Torus => inner ℂ u (field (E := E) seed time valid x v)) := by
  intro u v
  have paid:=source_memLp seed time valid {0} (fun _ => v)
  have same:polynomial {0} (fun _ : IntegerWavevector => v)=(ContinuousMap.const Torus v) := by
    ext x
    simp [polynomial,mFourier_zero]
  rw [same] at paid
  exact (paid.integrable (by norm_num)).const_inner u

theorem pairing_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u v : IntegerWavevector → SpinFiber E) :
    pairing (field (E := E) seed time valid) F u v=inner ℂ (input F u) (output seed time valid F v) := by
  rw [L2.inner_def]
  symm
  exact integral_congr_ae (by
    filter_upwards [input_ae F u,output_ae seed time valid F v] with x hp hq
    rw [hp,hq])

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (F : Finset IntegerWavevector) (u v : IntegerWavevector → SpinFiber E) (j : Coordinate) :
    HasDerivAt (fun z => pairing (orbit (field (E := E) seed time valid) j z) F u v)
      (-inner ℂ (input F (derivative j u)) (output seed time valid F v)
        -inner ℂ (input F u) (output seed time valid F (derivative j v))) 0 := by
  simpa only [pairing_original seed time valid] using!
    NativeWindowWeakLowerTranslation.coefficient_hasDerivAt
      (field (E := E) seed time valid) (source_regular seed time valid) F u v j

theorem read_lp_bound (v : Lp (NativeWindowAbsoluteLowerBound.Full E) 2 (volume : Measure Torus)) :
    ‖(read (E := E)).compLpL 2 (volume : Measure Torus) v‖^2 ≤ readCap^2*‖v‖^2 := by
  have normRead:‖read (E := E)‖ ≤ readCap:=(read (E := E)).opNorm_le_bound
    NativeWindowWeakLowerReadback.readCap_nonnegative (fun v => read_norm v)
  have bound:=((read (E := E)).compLpL 2 (volume : Measure Torus)).le_opNorm v
  have bound':‖(read (E := E)).compLpL 2 (volume : Measure Torus) v‖ ≤ readCap*‖v‖:=
    bound.trans (mul_le_mul_of_nonneg_right ((read (E := E)).norm_compLpL_le.trans normRead) (norm_nonneg _))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) bound' 2

theorem pairing_integrable (f : Torus → SpinFiber E) (regular : MemLp f 2 volume)
    (F : Finset IntegerWavevector) (u : IntegerWavevector → SpinFiber E) :
    Integrable (fun x : Torus => inner ℂ (polynomial F u x) (f x)) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (input F u) (regular.toLp f)).congr
  filter_upwards [input_ae F u,regular.coeFn_toLp] with x hp hq
  rw [hp,hq]

section Canonical
open NativeWindowAbsoluteTimeFourier (Fiber)
open NativeWindowAbsoluteTimePhysicalMatter (support coefficientRow)

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) : ℂ :=
  deriv (fun z => pairing (orbit (field (E := Fiber) seed time valid) j z) (support M)
    (derivative j (coefficientRow seed M time)) (coefficientRow seed M time)) 0

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    work seed M time valid j=
      -inner ℂ (input (support M) (derivative j (derivative j (coefficientRow seed M time))))
        (output seed time valid (support M) (coefficientRow seed M time))-
      inner ℂ (input (support M) (derivative j (coefficientRow seed M time)))
        (output seed time valid (support M) (derivative j (coefficientRow seed M time))) :=
  (source_hasDerivAt seed time valid (support M)
    (derivative j (coefficientRow seed M time)) (coefficientRow seed M time) j).deriv

theorem work_integral (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    work seed M time valid j=
      -pairing (field (E := Fiber) seed time valid) (support M)
        (derivative j (derivative j (coefficientRow seed M time))) (coefficientRow seed M time)-
      pairing (field (E := Fiber) seed time valid) (support M)
        (derivative j (coefficientRow seed M time)) (derivative j (coefficientRow seed M time)) := by
  rw [work_original,pairing_original,pairing_original]

def forcingDerivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) : ℂ :=
  -∫ x : Torus,inner ℂ
    (polynomial (support M) (derivative j (derivative j (coefficientRow seed M time))) x)
    (read (E := Fiber) (NativeWindowMotherForcingSource.forcing seed M time valid x))

def principalDerivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) : ℂ :=
  -∫ x : Torus,inner ℂ
    (polynomial (support M) (derivative j (derivative j (coefficientRow seed M time))) x)
    (read (E := Fiber) (∑ d : Fin 4,NativeWindowMotherForcingSource.principal seed M time d x))

def forceValue (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) :
    Lp (SpinFiber Fiber) 2 (volume : Measure Torus) :=
  (read (E := Fiber)).compLpL 2 volume ((NativeWindowMotherForcingSource.forcing_memLp seed M time valid).toLp
    (NativeWindowMotherForcingSource.forcing seed M time valid))

theorem forceValue_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) :
    forceValue seed M time valid=ᵐ[volume] fun x => read (E := Fiber)
      (NativeWindowMotherForcingSource.forcing seed M time valid x) := by
  filter_upwards [(read (E := Fiber)).coeFn_compLpL
    ((NativeWindowMotherForcingSource.forcing_memLp seed M time valid).toLp _),
    (NativeWindowMotherForcingSource.forcing_memLp seed M time valid).coeFn_toLp] with x hr hf
  exact hr.trans (congrArg (read (E := Fiber)) hf)

theorem forceValue_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) :
    ‖forceValue seed M time valid‖^2 ≤ readCap^2*(∫ x : Torus,‖NativeWindowMotherForcingSource.forcing seed M time valid x‖^2) := by
  have paid:=read_lp_bound ((NativeWindowMotherForcingSource.forcing_memLp seed M time valid).toLp _)
  have actual:‖(NativeWindowMotherForcingSource.forcing_memLp seed M time valid).toLp _‖^2=
      ∫ x : Torus,‖NativeWindowMotherForcingSource.forcing seed M time valid x‖^2 := by
    rw [NativeWindowHilbertHalfProduct.lp_square]
    exact integral_congr_ae ((NativeWindowMotherForcingSource.forcing_memLp seed M time valid).coeFn_toLp.fun_comp (fun v => ‖v‖^2))
  exact paid.trans_eq (congrArg (fun v : ℝ => readCap^2*v) actual)

theorem forcingDerivative_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    forcingDerivative seed M time valid j=
      -inner ℂ (input (support M) (derivative j (derivative j (coefficientRow seed M time)))) (forceValue seed M time valid) := by
  rw [L2.inner_def]
  apply congrArg Neg.neg
  symm
  exact integral_congr_ae (by
    filter_upwards [input_ae (support M) (derivative j (derivative j (coefficientRow seed M time))),
      forceValue_ae seed M time valid] with x hp hf
    rw [hp,hf])

theorem read_forcing_slot (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (x : Torus) :
    read (E := Fiber) (NativeWindowMotherForcingSource.forcing seed M time valid x)=
      read (E := Fiber) (∑ d : Fin 4,NativeWindowMotherForcingSource.principal seed M time d x)+
        field (E := Fiber) seed time valid x (polynomial (support M) (coefficientRow seed M time) x) := by
  rw [NativeWindowMotherForcingSource.forcing_original,map_add]
  rw [field,operator,ContinuousLinearMap.comp_apply,lift_original,NativeWindowMotherPhysicalBudget.polynomial_original]

theorem distribution_identity (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    forcingDerivative seed M time valid j=principalDerivative seed M time j+work seed M time valid j+
      pairing (field (E := Fiber) seed time valid) (support M)
        (derivative j (coefficientRow seed M time)) (derivative j (coefficientRow seed M time)) := by
  have principalLp:MemLp (fun x : Torus =>
      read (E := Fiber) (∑ d : Fin 4,NativeWindowMotherForcingSource.principal seed M time d x)) 2 volume := by
    apply (read (E := Fiber)).comp_memLp'
    exact memLp_finsetSum _ (fun d _ => NativeWindowMotherForcingSource.principal_memLp seed M time d)
  have first:=pairing_integrable _ principalLp (support M) (derivative j (derivative j (coefficientRow seed M time)))
  have last:=pairing_integrable _ (source_memLp seed time valid (support M) (coefficientRow seed M time))
    (support M) (derivative j (derivative j (coefficientRow seed M time)))
  have split:(∫ x : Torus,inner ℂ
      (polynomial (support M) (derivative j (derivative j (coefficientRow seed M time))) x)
      (read (E := Fiber) (NativeWindowMotherForcingSource.forcing seed M time valid x)))=
      (∫ x : Torus,inner ℂ
        (polynomial (support M) (derivative j (derivative j (coefficientRow seed M time))) x)
        (read (E := Fiber) (∑ d : Fin 4,NativeWindowMotherForcingSource.principal seed M time d x)))+
      pairing (field (E := Fiber) seed time valid) (support M)
        (derivative j (derivative j (coefficientRow seed M time))) (coefficientRow seed M time) := by
    dsimp only [pairing]
    rw [← integral_add first last]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [read_forcing_slot,inner_add_right]
  unfold forcingDerivative principalDerivative
  rw [split,work_integral]
  ring

theorem input_second_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    ‖input (support M) (derivative j (derivative j (coefficientRow seed M time)))‖^2 ≤
      NativeWindowAbsoluteMassChangedRead.canonicalSecondCost seed M time j := by
  rw [input_mass]
  change (∑k∈support M,‖NativePhysicalGradient.multiplier k j • NativeWindowMotherPhysicalBudget.spatialRow seed M time j k‖^2) ≤ _
  have nonnegative (d : Coordinate) (_ : d∈(Finset.univ : Finset Coordinate)) :
      0 ≤ ∑k∈support M,‖NativePhysicalGradient.multiplier k d • NativeWindowMotherPhysicalBudget.spatialRow seed M time j k‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact (Finset.single_le_sum nonnegative (Finset.mem_univ j)).trans_eq
    (NativeWindowMotherPhysicalBudget.second_mass seed M time j)

theorem source_absorption (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ (time : ℝ) (inside : time∈Icc 0 horizon),∀ j,
      ‖work seed M time (by linarith [inside.1]) j‖ ≤
        epsilon*NativeWindowAbsoluteMassChangedRead.canonicalSecondCost seed M time j+C := by
  obtain ⟨A,A0,paid⟩:=NativeWindowMotherPhysicalBudget.source_energy seed horizon
  let B:=readCap^2*NativeWindowMotherLowerProduct.budget seed horizon
  let K:=B*(A+1)
  have B0:0 ≤ B:=mul_nonneg (sq_nonneg _) (NativeWindowMotherLowerProduct.budget_nonnegative seed horizon)
  have K0:0 ≤ K:=mul_nonneg B0 (by positivity)
  have BK:B ≤ K:=by dsimp only [K]; nlinarith only [mul_nonneg B0 A0]
  refine ⟨(2*epsilon)⁻¹*K+(epsilon/(2*(K+1))*K+(4*(epsilon/(2*(K+1))))⁻¹)*A,by positivity,?_⟩
  intro M time inside j
  let D:=NativeWindowAbsoluteMassChangedRead.canonicalSecondCost seed M time j
  have D0:0 ≤ D:=Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have source:=paid M time inside
  have fraction:D/(2*Real.pi)^2 ≤ D:=div_le_self D0 (by nlinarith [Real.pi_gt_three])
  have pMass:‖input (support M) (derivative j (coefficientRow seed M time))‖^2 ≤ A := by
    rw [input_mass]
    exact (source.2 j).1
  have dpMass:‖input (support M) (derivative j (derivative j (coefficientRow seed M time)))‖^2 ≤ D :=
    input_second_bound seed M time j
  have bqMass:‖output seed time (by linarith [inside.1]) (support M) (coefficientRow seed M time)‖^2 ≤ K := by
    apply (output_bound seed time horizon (by linarith [inside.1]) inside.2 (support M) (coefficientRow seed M time)).trans
    exact (mul_le_mul_of_nonneg_left source.1 B0).trans (by dsimp only [K]; nlinarith only [B0])
  have bpMass:‖output seed time (by linarith [inside.1]) (support M) (derivative j (coefficientRow seed M time))‖^2 ≤ K*(A+D) := by
    apply (output_bound seed time horizon (by linarith [inside.1]) inside.2 (support M) (derivative j (coefficientRow seed M time))).trans
    apply (mul_le_mul_of_nonneg_left ((source.2 j).2.trans (add_le_add_right fraction A)) B0).trans
    exact mul_le_mul_of_nonneg_right BK (add_nonneg A0 D0)
  rw [work_original]
  simpa only [add_assoc] using! NativeWindowWeakLowerReadback.two_test_absorption _ _ _ _ K A D epsilon K0 D0 positive pMass dpMass bqMass bpMass

theorem source_forcing_absorption (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ (time : ℝ) (inside : time∈Icc 0 horizon),∀ j,
      ‖forcingDerivative seed M time (by linarith [inside.1]) j‖ ≤
        epsilon*NativeWindowAbsoluteMassChangedRead.canonicalSecondCost seed M time j+C := by
  obtain ⟨A,A0,paid⟩:=NativeWindowMotherForcingSource.source_bound seed horizon
  refine ⟨(4*epsilon)⁻¹*(readCap^2*A),by positivity,?_⟩
  intro M time inside j
  have bound:=NativeWindowWeakLowerReadback.inner_young
    (input (support M) (derivative j (derivative j (coefficientRow seed M time))))
    (forceValue seed M time (by linarith [inside.1])) epsilon positive
  have first:=input_second_bound seed M time j
  have last:‖forceValue seed M time (by linarith [inside.1])‖^2 ≤ readCap^2*A :=
    (forceValue_bound seed M time (by linarith [inside.1])).trans
      (mul_le_mul_of_nonneg_left (paid M ⟨time,inside⟩).2 (sq_nonneg readCap))
  rw [forcingDerivative_original,norm_neg]
  exact bound.trans (add_le_add (mul_le_mul_of_nonneg_left first positive.le)
    (mul_le_mul_of_nonneg_left last (by positivity)))

theorem source_changed_read (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ (time : ℝ) (inside : time∈Icc 0 horizon),∀ j,
      ‖principalDerivative seed M time j+
        pairing (field (E := Fiber) seed time (by linarith [inside.1])) (support M)
          (derivative j (coefficientRow seed M time)) (derivative j (coefficientRow seed M time))‖ ≤
        epsilon*NativeWindowAbsoluteMassChangedRead.canonicalSecondCost seed M time j+C := by
  obtain ⟨F,F0,force⟩:=source_forcing_absorption seed horizon (epsilon/2) (by positivity)
  obtain ⟨B,B0,lower⟩:=source_absorption seed horizon (epsilon/2) (by positivity)
  refine ⟨F+B,add_nonneg F0 B0,?_⟩
  intro M time inside j
  have identity:=distribution_identity seed M time (by linarith [inside.1]) j
  have actual:principalDerivative seed M time j+
      pairing (field (E := Fiber) seed time (by linarith [inside.1])) (support M)
        (derivative j (coefficientRow seed M time)) (derivative j (coefficientRow seed M time))=
      forcingDerivative seed M time (by linarith [inside.1]) j-work seed M time (by linarith [inside.1]) j := by
    rw [identity]
    ring
  rw [actual]
  have bound:=norm_sub_le (forcingDerivative seed M time (by linarith [inside.1]) j) (work seed M time (by linarith [inside.1]) j)
  have first:=force M time inside j
  have last:=lower M time inside j
  linarith

end Canonical

section Clock
open NativeWindowAbsoluteTimeFourier (Fiber)
open NativeWindowAbsoluteTimePhysicalMatter (matter spatial background)
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

def clock (advance : ℝ) : Fiber →ₗᵢ[ℂ] Fiber :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun s : ℝ => s-advance)
    (by simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance))

theorem clock_original (advance : ℝ) (v : Fiber) :
    clock advance v=NativeWindowAbsoluteTimeIsometry.clock ℂ advance v := rfl

def spinClock (advance : ℝ) (v : SpinFiber Fiber) : SpinFiber Fiber :=
  WithLp.toLp 2 (fun entry => clock advance (v entry))

theorem operator_clock (L : Module.End ℂ DiracExteriorMatterCarrier)
    (advance : ℝ) (v : SpinFiber Fiber) :
    operator (E := Fiber) L (spinClock advance v)=spinClock advance (operator (E := Fiber) L v) := by
  apply PiLp.ext
  intro entry
  simp only [operator,ContinuousLinearMap.comp_apply,NativeWindowWeakLowerReadback.read_apply,
    lift_original,NativeWindowAbsoluteLowerBound.lift,spinClock,PiLp.toLp_apply,map_sum,map_smul]

theorem spinClock_inner (advance : ℝ) (u v : SpinFiber Fiber) :
    inner ℂ (spinClock advance u) (spinClock advance v)=inner ℂ u v := by
  simp only [PiLp.inner_apply,spinClock,(clock advance).inner_map_map]

theorem background_clock (time advance : ℝ) : background (advance+time)=clock advance (background time) := by
  apply Lp.ext
  have preserves : MeasurePreserving (fun s : ℝ => s-advance) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance)
  have shifted:=preserves.quasiMeasurePreserving.ae (NativeWindowAbsoluteTimePhysicalMatter.background_ae time)
  filter_upwards [NativeWindowAbsoluteTimePhysicalMatter.background_ae (advance+time),
    NativeWindowAbsoluteTimeIsometry.clock_ae ℂ advance (background time),shifted] with s hq hc hb
  change clock advance (background time) s=_ at hc
  rw [hq,hc,hb]
  congr 2
  ring

theorem matter_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (x : Torus) :
    WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter seed M (step.2.clockAdvance+time) entry.1 entry.2 x)=
      spinClock step.2.clockAdvance (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter step.1 M time entry.1 entry.2 x)) := by
  apply PiLp.ext
  intro entry
  simp only [spinClock,PiLp.toLp_apply,matter,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    ContinuousMap.const_apply,ContinuousMap.sum_apply,background_clock,
    NativeWindowAbsoluteTimeFourier.source_next seed step generated time nonnegative,
    ← clock_original,map_add,map_sum,map_smul]

theorem spatial_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (j : Coordinate) (x : Torus) :
    WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => spatial seed M (step.2.clockAdvance+time) j entry.1 entry.2 x)=
      spinClock step.2.clockAdvance (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => spatial step.1 M time j entry.1 entry.2 x)) := by
  have original:=NativeWindowAbsoluteTimeEnergy.value_next seed M step generated time nonnegative j.succ
  change NativeWindowAbsoluteTimeGradient.spatial M j (NativeWindowAbsoluteTimeSource.history seed (step.2.clockAdvance+time))=_ at original
  apply PiLp.ext
  intro entry
  simp only [spinClock,PiLp.toLp_apply,spatial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    original,NativeWindowAbsoluteTimeFourier.field_clock,← clock_original,map_sum,map_smul]
  rfl

theorem orbit_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (j : Coordinate) (z : ℝ) :
    pairing (orbit (field (E := Fiber) seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos])) j z)
        (NativeWindowAbsoluteTimePhysicalMatter.support M)
        (derivative j (NativeWindowAbsoluteTimePhysicalMatter.coefficientRow seed M (step.2.clockAdvance+time)))
        (NativeWindowAbsoluteTimePhysicalMatter.coefficientRow seed M (step.2.clockAdvance+time))=
      pairing (orbit (field (E := Fiber) step.1 time (by linarith)) j z)
        (NativeWindowAbsoluteTimePhysicalMatter.support M)
        (derivative j (NativeWindowAbsoluteTimePhysicalMatter.coefficientRow step.1 M time))
        (NativeWindowAbsoluteTimePhysicalMatter.coefficientRow step.1 M time) := by
  unfold pairing
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change inner ℂ (polynomial _ (NativeWindowMotherPhysicalBudget.spatialRow seed M (step.2.clockAdvance+time) j) x) _=_
  simp only [NativeWindowMotherPhysicalBudget.spatial_polynomial,NativeWindowMotherPhysicalBudget.polynomial_original]
  change _=inner ℂ (polynomial _ (NativeWindowMotherPhysicalBudget.spatialRow step.1 M time j) x) _
  rw [NativeWindowMotherPhysicalBudget.spatial_polynomial,
    matter_next seed M step generated time nonnegative x,spatial_next seed M step generated time nonnegative j x]
  simp only [orbit,field,NativeWindowMotherLowerProduct.point_next seed step generated time nonnegative,
    operator_clock,spinClock_inner]

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (j : Coordinate) :
    work seed M (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) j=
      work step.1 M time (by linarith) j := by
  unfold work
  exact congrArg (fun f : ℝ → ℂ => deriv f 0) (funext (orbit_next seed M step generated time nonnegative j))

end Clock
end
end SaturationMonoid.NavierStokes.NativeWindowWeakLowerSource
