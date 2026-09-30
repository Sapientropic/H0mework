import H0mework.NavierStokes.WindowSchurAbsolute.Bridge
import H0mework.NavierStokes.WindowSchurAbsolute.Gradient
import H0mework.NavierStokes.WindowSourceGreen.SpatialForm
import H0mework.NavierStokes.WindowHistoryCreation.Geometry

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeFourier
open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWholeResolvent (wholePhysical)
open NativeWindowAbsoluteTimeSource (H history rate)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}

abbrev Fiber := Lp ℂ 2 (volume : Measure ℝ)
abbrev Space := Lp Fiber 2 (volume : Measure Torus)
local instance fiberSeminormed : SeminormedAddCommGroup Fiber := (inferInstance : NormedAddCommGroup Fiber).toSeminormedAddCommGroup
local instance spaceSeminormed : SeminormedAddCommGroup Space := (inferInstance : NormedAddCommGroup Space).toSeminormedAddCommGroup
local instance historySeminormed : SeminormedAddCommGroup H := (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup

section Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def polynomial (F : Finset IntegerWavevector) (c : IntegerWavevector → E) : C(Torus,E) where
  toFun x := ∑ k ∈ F,mFourier k x • c k
  continuous_toFun := continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const

theorem phase_inner (p q : IntegerWavevector) :
    (∫ x : Torus,star (mFourier p x)*mFourier q x) = if p=q then 1 else 0 := by
  have source:=orthonormal_iff_ite.mp (orthonormal_mFourier (d := Coordinate)) p q
  simpa only [ContinuousMap.inner_toLp,RCLike.inner_apply,starRingEnd_apply,mul_comm] using source

theorem polynomial_pairing (F : Finset IntegerWavevector) (u v : IntegerWavevector → E) :
    (∫ x : Torus,inner ℂ (polynomial F u x) (polynomial F v x))=∑ k∈F,inner ℂ (u k) (v k) := by
  have regular (p q : IntegerWavevector) : Integrable (fun x : Torus =>
      (star (mFourier p x)*mFourier q x)*inner ℂ (u p) (v q)) :=
    (((mFourier p).continuous.star.mul (mFourier q).continuous).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have point (x : Torus) : inner ℂ (polynomial F u x) (polynomial F v x)=
      ∑ p∈F,∑ q∈F,(star (mFourier p x)*mFourier q x)*inner ℂ (u p) (v q) := by
    simp only [polynomial,ContinuousMap.coe_mk,sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum,starRingEnd_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [point]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => regular p q))]
  apply Finset.sum_congr rfl
  intro p inside
  rw [integral_finsetSum _ (fun q _ => regular p q)]
  simp only [integral_mul_const,phase_inner,ite_mul,one_mul,zero_mul]
  simp [inside]

theorem polynomial_square (F : Finset IntegerWavevector) (v : IntegerWavevector → E) :
    (∫ x : Torus,‖polynomial F v x‖^2)=∑ k∈F,‖v k‖^2 := by
  have source:=congrArg Complex.re (polynomial_pairing F v v)
  have paid : Integrable (fun x : Torus => inner ℂ (polynomial F v x) (polynomial F v x)) :=
    ((polynomial F v).continuous.inner (polynomial F v).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have commuted:=Complex.reCLM.integral_comp_comm paid
  change (∫ x : Torus,(inner ℂ (polynomial F v x) (polynomial F v x)).re)=_ at commuted
  change (∫ x : Torus,(inner ℂ (polynomial F v x) (polynomial F v x)).re)=
    (∫ x : Torus,inner ℂ (polynomial F v x) (polynomial F v x)).re at commuted
  rw [← commuted] at source
  simpa [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow] using source


theorem polynomial_hasDerivAt (F : Finset IntegerWavevector) (v : IntegerWavevector → E)
    (j : Coordinate) (x : Torus) :
    HasDerivAt (fun z : ℝ => polynomial F v (x+NativePhysicalTranslation.displacement j z))
      (polynomial F (fun k => NativePhysicalGradient.multiplier k j • v k) x) 0 := by
  have each (k : IntegerWavevector) :
      HasDerivAt (fun z : ℝ => mFourier k (x+NativePhysicalTranslation.displacement j z) • v k)
        (mFourier k x • (NativePhysicalGradient.multiplier k j • v k)) 0 := by
    simp only [NativePhysicalTranslation.character_add,NativePhysicalTranslation.character_displacement]
    simpa only [NativeSpatialTranslation.phase_zero,mul_one,smul_smul] using
      ((NativeSpatialTranslation.phase_hasDerivAt j k 0).const_mul (mFourier k x)).smul_const (v k)
  convert HasDerivAt.sum (u := F) (fun k _ => each k) using 1
  · funext z
    simp only [polynomial,ContinuousMap.coe_mk,Finset.sum_apply]
  · rfl


def translatedPolynomial (F : Finset IntegerWavevector) (v : IntegerWavevector → E)
    (j : Coordinate) (z : ℝ) : C(Torus,E) :=
  (polynomial F v).comp ⟨fun x => x+NativePhysicalTranslation.displacement j z,continuous_id.add continuous_const⟩

theorem polynomial_spatial_strong (F : Finset IntegerWavevector) (v : IntegerWavevector → E) (j : Coordinate) :
    HasDerivAt (translatedPolynomial F v j)
      (polynomial F (fun k => NativePhysicalGradient.multiplier k j • v k)) 0 := by
  have each (k : IntegerWavevector) := (NativeSpatialTranslation.phase_hasDerivAt j k 0).smul_const (polynomial {k} v)
  simp only [NativeSpatialTranslation.phase_zero,mul_one] at each
  convert HasDerivAt.sum (u := F) (fun k _ => each k) using 1
  · funext z
    apply ContinuousMap.ext
    intro x
    simp only [translatedPolynomial,ContinuousMap.comp_apply,polynomial,ContinuousMap.coe_mk,
      NativePhysicalTranslation.character_add,NativePhysicalTranslation.character_displacement,
      Finset.sum_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,Finset.sum_singleton,smul_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  · apply ContinuousMap.ext
    intro x
    simp only [polynomial,ContinuousMap.coe_mk,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
      Finset.sum_singleton,smul_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

end Polynomial

def rowMap (k : IntegerWavevector) (i : Coordinate) : wholePhysical →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj i).comp ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 k).comp
    (NativeEndpointVelocityCarrier.wholeVelocityCLM.comp wholePhysical.subtypeL))

def row (k : IntegerWavevector) (i : Coordinate) : H →L[ℝ] Fiber := (rowMap k i).compLpL 2 volume

theorem row_apply (k : IntegerWavevector) (i : Coordinate) (v : wholePhysical) :
    rowMap k i v=NativeEndpointVelocityCarrier.wholeVelocity v.1 k i := rfl

def field (F : Finset IntegerWavevector) (i : Coordinate) (v : H) : C(Torus,Fiber) :=
  polynomial F (fun k => row k i v)

def physical (F : Finset IntegerWavevector) (i : Coordinate) (v : H) : Space :=
  (ContinuousMap.toLp 2 volume ℂ) (field F i v)

theorem physical_square (F : Finset IntegerWavevector) (i : Coordinate) (v : H) :
    ‖physical F i v‖^2=∑ k∈F,‖row k i v‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  have original:=ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) (field F i v)
  exact (integral_congr_ae (original.fun_comp (fun z => ‖z‖^2))).trans (polynomial_square F (fun k => row k i v))

theorem rows_bound (F : Finset IntegerWavevector) (v : wholePhysical) :
    (∑ k∈F,∑ i : Coordinate,‖rowMap k i v‖^2)≤‖v‖^2 := by
  have paid:=ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
    F (NativeEndpointVelocityCarrier.wholeVelocity v.1)
  rw [NativeEndpointVelocityCarrier.wholeVelocity_mass] at paid
  change (∑ k∈F,∑ i : Coordinate,‖rowMap k i v‖^2)≤‖v.1‖^2
  simpa only [ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy,
    row_apply,complexCoordinateAmplitudeSq,Complex.normSq_eq_norm_sq] using paid

theorem physical_mass (F : Finset IntegerWavevector) (v : H) :
    (∑ i : Coordinate,‖physical F i v‖^2)≤‖v‖^2 := by
  simp only [physical_square]
  rw [Finset.sum_comm]
  have each (k : IntegerWavevector) (i : Coordinate) :
      ‖row k i v‖^2=∫ s : ℝ,‖rowMap k i (v s)‖^2 := by
    rw [NativeWindowAbsoluteTimeIsometry.norm_square]
    exact integral_congr_ae ((rowMap k i).coeFn_compLpL v |>.fun_comp (fun z => ‖z‖^2))
  simp_rw [each]
  have paid (k : IntegerWavevector) (i : Coordinate) : Integrable (fun s : ℝ => ‖rowMap k i (v s)‖^2) :=
    ((rowMap k i).comp_memLp v).norm.integrable_sq
  simp_rw [← integral_finsetSum _ (fun i _ => paid _ i)]
  rw [← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => paid k i)),NativeWindowAbsoluteTimeIsometry.norm_square]
  exact integral_mono (integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => paid k i)))
    ((Lp.memLp v).norm.integrable_sq) (fun s => rows_bound F (v s))


theorem physical_add (F : Finset IntegerWavevector) (i : Coordinate) (u v : H) :
    physical F i (u+v)=physical F i u+physical F i v := by
  have equal : field F i (u+v)=field F i u+field F i v := by
    apply ContinuousMap.ext
    intro x
    simp only [field,polynomial,ContinuousMap.coe_mk,map_add,smul_add,Finset.sum_add_distrib,ContinuousMap.add_apply]
  exact (congrArg (ContinuousMap.toLp 2 volume ℂ) equal).trans ((ContinuousMap.toLp 2 volume ℂ).map_add _ _)

theorem physical_smul (F : Finset IntegerWavevector) (i : Coordinate) (a : ℝ) (v : H) :
    physical F i (a • v)=a • physical F i v := by
  have equal : field F i (a • v)=a • field F i v := by
    apply ContinuousMap.ext
    intro x
    simp only [field,polynomial,ContinuousMap.coe_mk,map_smul,ContinuousMap.smul_apply,Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  exact (congrArg (ContinuousMap.toLp 2 volume ℂ) equal).trans
    (((ContinuousMap.toLp 2 volume ℂ).restrictScalars ℝ).map_smul a _)

def realize (F : Finset IntegerWavevector) (i : Coordinate) : H →L[ℝ] Space :=
  LinearMap.mkContinuous {toFun := physical F i, map_add' := physical_add F i, map_smul' := physical_smul F i}
    1 (fun v => by
      change ‖physical F i v‖ ≤ 1*‖v‖
      have one:=(Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg ‖physical F j v‖) (Finset.mem_univ i)).trans (physical_mass F v)
      simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp one)

def evaluation (F : Finset IntegerWavevector) (i : Coordinate) (x : Torus) : wholePhysical →L[ℝ] ℂ :=
  ∑ k∈F,mFourier k x • rowMap k i

theorem field_evaluation (F : Finset IntegerWavevector) (i : Coordinate) (v : H) (x : Torus) :
    field F i v x=(evaluation F i x).compLpL 2 volume v := by
  let lift : (wholePhysical →L[ℝ] ℂ) →L[ℝ] H →L[ℝ] Fiber :=
    ContinuousLinearMap.compLpL₂ (𝕜 := ℝ) (E := wholePhysical) (F := ℂ)
      (G := wholePhysical →L[ℝ] ℂ) 2 (volume : Measure ℝ) (ContinuousLinearMap.id ℝ _)
  have expanded:=congrArg (fun L : H →L[ℝ] Fiber => L v)
    (map_sum lift (fun k => mFourier k x • rowMap k i) F)
  change (evaluation F i x).compLpL 2 volume v=(∑ k∈F,lift (mFourier k x • rowMap k i)) v at expanded
  have each (k : IntegerWavevector) : lift (mFourier k x • rowMap k i)=mFourier k x • row k i :=
    ContinuousLinearMap.smul_compLpL (mFourier k x) (rowMap k i)
  simp only [each,sum_apply,smul_apply] at expanded
  exact expanded.symm

theorem field_ae (F : Finset IntegerWavevector) (i : Coordinate) (v : H) (x : Torus) :
    field F i v x=ᵐ[volume] fun s => ∑ k∈F,mFourier k x*rowMap k i (v s) := by
  rw [field_evaluation]
  simpa only [evaluation,sum_apply,smul_apply,smul_eq_mul] using
    (evaluation F i x).coeFn_compLpL v

theorem source_field_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (i : Coordinate) (time : ℝ) (x : Torus) :
    field F i (history seed time) x=ᵐ[volume] fun s =>
      NativeWindowKernelHalfDensity.rootKernel (time-s) •
        (∑ k∈F,mFourier k x*NativeEndpointVelocityCarrier.wholeVelocity (NativeWindowTraceWholeHistory.original seed s).1 k i) := by
  filter_upwards [field_ae F i (history seed time) x,NativeWindowAbsoluteTimeSource.history_ae seed time] with s read original
  rw [read,original]
  simp only [map_smul,row_apply,Finset.smul_sum,mul_smul_comm]

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (i : Coordinate) (time : ℝ) :
    HasDerivAt (fun t => realize F i (history seed t)) (realize F i (rate seed time)) time :=
  (realize F i).hasFDerivAt.comp_hasDerivAt (E := Space) (F := H) time
    (NativeWindowAbsoluteTimeSource.source_hasDerivAt seed time)


open NativeWholeH1Mixed (modes modes_zero modes_closed)

theorem row_include (M : ℕ) (k : IntegerWavevector) (i : Coordinate)
    (v : NativeFiniteActionResolvent.physicalSpace (modes M)) :
    rowMap k i (NativePhysicalPairing.includeCLM (modes M) (modes_closed M) v)=v.1 k i := by
  change NativeEndpointVelocityCarrier.wholeVelocity
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize v.1) k i=_
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize v.1
    (NativeFiniteActionResolvent.physical_supported v 0 (modes_zero M))]

theorem row_spatial (M : ℕ) (j : Coordinate) (k : IntegerWavevector) (inside : k∈modes M)
    (i : Coordinate) (v : H) :
    row k i (NativeWindowAbsoluteTimeGradient.spatial M j v)=NativePhysicalGradient.multiplier k j • row k i v := by
  apply Lp.ext
  filter_upwards [(rowMap k i).coeFn_compLpL (NativeWindowAbsoluteTimeGradient.spatial M j v),
    (NativeWindowHistorySpatialWords.fiber M [j]).coeFn_compLpL v,(rowMap k i).coeFn_compLpL v,
    Lp.coeFn_smul (NativePhysicalGradient.multiplier k j) (row k i v)] with s outer original point scalar
  change row k i (NativeWindowAbsoluteTimeGradient.spatial M j v) s=_ at outer
  change NativeWindowAbsoluteTimeGradient.spatial M j v s=_ at original
  change row k i v s=_ at point
  rw [outer,original,scalar,Pi.smul_apply,point,NativeWindowHistoryJacobianSpatial.fiber_original,row_include,
    NativeWindowAugmentedGradient.derivative_apply]
  change NativePhysicalGradient.multiplier k j *
    (complexSharpSupportProjection
      (modes M) (NativeEndpointVelocityCarrier.wholeVelocity (v s).1) k i)=_
  simp only [complexSharpSupportProjection_apply,
    if_pos inside,row_apply,smul_eq_mul]

theorem field_spatial (M : ℕ) (i j : Coordinate) (v : H) (x : Torus) :
    field (modes M) i (NativeWindowAbsoluteTimeGradient.spatial M j v) x=
      polynomial (modes M) (fun k => NativePhysicalGradient.multiplier k j • row k i v) x := by
  change (∑ k∈modes M,mFourier k x • row k i (NativeWindowAbsoluteTimeGradient.spatial M j v))=_
  exact Finset.sum_congr rfl fun k inside => congrArg (fun z : Fiber => mFourier k x • z) (row_spatial M j k inside i v)

theorem field_hasDerivAt (M : ℕ) (i j : Coordinate) (v : H) (x : Torus) :
    HasDerivAt (fun z : ℝ => field (modes M) i v (x+NativePhysicalTranslation.displacement j z))
      (field (modes M) i (NativeWindowAbsoluteTimeGradient.spatial M j v) x) 0 := by
  rw [field_spatial]
  exact polynomial_hasDerivAt (modes M) (fun k => row k i v) j x

theorem source_mixed_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M j,∀ time∈Icc 0 horizon,
      (∑ i : Coordinate,‖realize (modes M) i (NativeWindowAbsoluteTimeGradient.spatial M j (rate seed time))‖^2)≤C := by
  obtain ⟨C,C0,paid⟩:=NativeWindowAbsoluteTimeGradient.source_rate_spatial_bound seed horizon
  exact ⟨C,C0,fun M j time inside => (physical_mass (modes M) _).trans (paid M j time inside)⟩


theorem row_project (M : ℕ) (k : IntegerWavevector) (inside : k∈modes M) (i : Coordinate) (v : H) :
    row k i ((NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v)=row k i v := by
  apply Lp.ext
  filter_upwards [(rowMap k i).coeFn_compLpL ((NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v),
    (NativeWindowTraceWholeHistory.projection M).coeFn_compLpL v,(rowMap k i).coeFn_compLpL v] with s outer project point
  change row k i ((NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v) s=_ at outer
  change row k i v s=_ at point
  rw [outer,project,point]
  change rowMap k i (NativePhysicalPairing.includeCLM (modes M) (NativeWholeH1Mixed.modes_closed M)
    (NativeWholeResolvent.restrictCLM (modes M) (NativeWholeH1Mixed.modes_zero M) (NativeWholeH1Mixed.modes_closed M) (v s)))=_
  rw [row_include]
  change complexSharpSupportProjection (modes M) (NativeEndpointVelocityCarrier.wholeVelocity (v s).1) k i=_
  rw [complexSharpSupportProjection_apply,if_pos inside]
  rfl

theorem field_project (M : ℕ) (i : Coordinate) (v : H) :
    field (modes M) i ((NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v)=field (modes M) i v := by
  apply ContinuousMap.ext
  intro x
  change (∑ k∈modes M,UnitAddTorus.mFourier k x • row k i ((NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v))=_
  exact Finset.sum_congr rfl fun k inside => congrArg (fun z : Fiber => UnitAddTorus.mFourier k x • z) (row_project M k inside i v)

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (i : Coordinate) (time : ℝ) (x : Torus) :
    field (modes M) i (rate seed time) x=
      field (modes M) i (NativeWindowAbsoluteTimeBridge.absoluteAction seed M time (NativeWindowAbsoluteTimeBridge.finiteHistory seed M time)) x+
      field (modes M) i (NativeWindowAbsoluteTimeIsometry.map NativeWholeResolvent.wholePhysical time (NativeWindowHistoryOseen.forcingHistory seed M time)) x-
      field (modes M) i (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time) x := by
  have projection:=congrArg (fun f : C(Torus,Fiber) => f x) (field_project M i (rate seed time))
  have actual:=congrArg ((evaluation (modes M) i x).compLpL 2 (volume : Measure ℝ))
    (NativeWindowAbsoluteTimeBridge.source_equation seed M time)
  simp only [map_add,map_sub] at actual
  have first : field (modes M) i (rate seed time) x=
      (evaluation (modes M) i x).compLpL 2 volume (NativeWindowAbsoluteTimeBridge.finiteRate seed M time) :=
    projection.symm.trans (field_evaluation (modes M) i _ x)
  exact first.trans (actual.trans (by simp only [field_evaluation]))


theorem projected_square (M : ℕ) (v : wholePhysical) :
    ‖NativeWindowTraceWholeHistory.projection M v‖^2=∑ k∈modes M,∑ i : Coordinate,‖rowMap k i v‖^2 := by
  rw [NativeWindowTraceWholeHistory.projection,ContinuousLinearMap.comp_apply,
    NativePhysicalPairing.include_norm (modes M) (modes_zero M) (modes_closed M),← real_inner_self_eq_norm_sq]
  change NativeFiniteActionResolvent.pairing (modes M)
    (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
    (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) v)=_
  rw [NativeWindowHistoryCreationGeometry.pairing_mass]
  apply Finset.sum_congr rfl
  intro k inside
  apply Finset.sum_congr rfl
  intro i _
  change ‖complexSharpSupportProjection (modes M) (NativeEndpointVelocityCarrier.wholeVelocity v.1) k i‖^2=_
  rw [complexSharpSupportProjection_apply,if_pos inside,row_apply]

theorem physical_mass_exact (M : ℕ) (v : H) :
    (∑ i : Coordinate,‖realize (modes M) i v‖^2)=
      ‖(NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v‖^2 := by
  change (∑ i : Coordinate,‖physical (modes M) i v‖^2)=_
  simp only [physical_square]
  rw [Finset.sum_comm]
  have each (k : IntegerWavevector) (i : Coordinate) :
      ‖row k i v‖^2=∫ s : ℝ,‖rowMap k i (v s)‖^2 := by
    rw [NativeWindowAbsoluteTimeIsometry.norm_square]
    exact integral_congr_ae ((rowMap k i).coeFn_compLpL v |>.fun_comp (fun z => ‖z‖^2))
  simp_rw [each]
  have paid (k : IntegerWavevector) (i : Coordinate) : Integrable (fun s : ℝ => ‖rowMap k i (v s)‖^2) :=
    ((rowMap k i).comp_memLp v).norm.integrable_sq
  simp_rw [← integral_finsetSum _ (fun i _ => paid _ i)]
  rw [← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => paid k i)),NativeWindowAbsoluteTimeIsometry.norm_square]
  apply integral_congr_ae
  filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL v] with s actual
  rw [actual,projected_square]

theorem physical_pairing (M : ℕ) (u v : H) :
    (∑ i : Coordinate,inner ℝ (realize (modes M) i u) (realize (modes M) i v))=
      inner ℝ ((NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) u)
        ((NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ) v) := by
  have plus:=physical_mass_exact M (u+v)
  simp only [map_add,norm_add_sq_real,Finset.sum_add_distrib,← Finset.mul_sum] at plus
  linarith only [plus,physical_mass_exact M u,physical_mass_exact M v]

theorem source_power (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (∑ i : Coordinate,2*inner ℝ (realize (modes M) i (history seed time)) (realize (modes M) i (rate seed time)))=
      2*inner ℝ (NativeWindowAbsoluteTimeBridge.finiteHistory seed M time) (NativeWindowAbsoluteTimeBridge.finiteRate seed M time) := by
  rw [← Finset.mul_sum,physical_pairing]
  rfl


theorem field_clock (F : Finset IntegerWavevector) (i : Coordinate) (advance : ℝ) (v : H) (x : Torus) :
    field F i (NativeWindowAbsoluteTimeIsometry.clock wholePhysical advance v) x=
      NativeWindowAbsoluteTimeIsometry.clock ℂ advance (field F i v x) := by
  simp only [field_evaluation]
  apply Lp.ext
  have preserves : MeasurePreserving (fun s : ℝ => s-advance) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance)
  have shifted:=preserves.quasiMeasurePreserving.ae ((evaluation F i x).coeFn_compLpL v)
  filter_upwards [(evaluation F i x).coeFn_compLpL (NativeWindowAbsoluteTimeIsometry.clock wholePhysical advance v),
    NativeWindowAbsoluteTimeIsometry.clock_ae wholePhysical advance v,
    NativeWindowAbsoluteTimeIsometry.clock_ae ℂ advance ((evaluation F i x).compLpL 2 (volume : Measure ℝ) v),shifted]
    with s first original last actual
  rw [first,original,last,actual]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (F : Finset IntegerWavevector) (i : Coordinate) (x : Torus) :
    field F i (history seed (step.2.clockAdvance+time)) x=
      NativeWindowAbsoluteTimeIsometry.clock ℂ step.2.clockAdvance (field F i (history step.1 time) x) :=
  (congrArg (fun v : H => field F i v x) (NativeWindowAbsoluteTimeBridge.source_next seed step generated time nonnegative)).trans
    (field_clock F i step.2.clockAdvance _ x)

theorem rate_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (F : Finset IntegerWavevector) (i : Coordinate) (x : Torus) :
    field F i (rate seed (step.2.clockAdvance+time)) x=
      NativeWindowAbsoluteTimeIsometry.clock ℂ step.2.clockAdvance (field F i (rate step.1 time) x) :=
  (congrArg (fun v : H => field F i v x) (NativeWindowAbsoluteTimeBridge.rate_next seed step generated time nonnegative)).trans
    (field_clock F i step.2.clockAdvance _ x)

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeFourier
