import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeCurrentLaplaceCarrier

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentConstrainedInverse
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open Filter MeasureTheory Set
open scoped BigOperators Topology Matrix Interval
attribute [local irreducible] sourceCurrentOperator originalJacobi sourceGreen sourceCompatibility
  sourceCausalHalfOperator sourceLaplaceCurrent sourceLaplaceInitial sourceCommonUpdateOperator

private theorem complex_decomposition (z : ℂ) (v : SignalAmplitude) :
    z • v=z.re • v+z.im • (Complex.I • v) :=by
  ext i
  simp only [Pi.smul_apply,Pi.add_apply,Complex.real_smul,smul_eq_mul]
  calc
    z*v i=((z.re : ℂ)+(z.im : ℂ)*Complex.I)*v i:=congrArg (fun w : ℂ=>w*v i) (Complex.re_add_im z).symm
    _=_:=by ring

private theorem realMap_complex_linear (A : SignalAmplitude→L[ℝ] SignalAmplitude)
    (rotation : ∀v,A (Complex.I • v)=Complex.I • A v) (z : ℂ) (v : SignalAmplitude) :
    A (z • v)=z • A v :=by
  rw [complex_decomposition z v,map_add,A.map_smul,A.map_smul,rotation,←complex_decomposition]

private theorem quadrature_rotation (A : SignalAmplitude→L[ℝ] SignalAmplitude) (v : SignalAmplitude) :
    (A+Complex.I • A.comp sourceQuadratureOperator) (Complex.I • v)=
      Complex.I • (A+Complex.I • A.comp sourceQuadratureOperator) v :=by
  have square : sourceQuadratureOperator (Complex.I • v)=v :=by
    ext i
    change (-Complex.I)*(Complex.I*v i)=v i
    calc
      _=-(Complex.I*Complex.I)*v i:=by ring
      _=v i:=by simp
  have reversed : sourceQuadratureOperator v=-(Complex.I • v) :=by
    simp only [sourceQuadratureOperator,smul_apply,ContinuousLinearMap.id_apply,neg_smul]
  rw [add_apply,smul_apply,ContinuousLinearMap.comp_apply,square,add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,reversed,map_neg]
  ext i
  simp only [Pi.smul_apply,Pi.add_apply,Pi.neg_apply,smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem sourceQuadratureCurrent_complex_smul (q : PhysicalResponsePoint) (p : Fin 4→ℂ)
    (t : ℝ) (z : ℂ) (a : SignalAmplitude) :
    sourceQuadratureCurrent q p t (z • a)=z • sourceQuadratureCurrent q p t a :=
  realMap_complex_linear _ (quadrature_rotation _) z a

def sourceComplexHistoryCurrent (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) :
    SignalAmplitude→L[ℂ] SignalAmplitude where
  toLinearMap:=
    {toFun:=sourceQuadratureCurrent q p t
     map_add':=(sourceQuadratureCurrent q p t).map_add
     map_smul':=sourceQuadratureCurrent_complex_smul q p t}
  cont:=(sourceQuadratureCurrent q p t).continuous

theorem sourceComplexHistoryCurrent_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ)
    (t : ℝ) (a : SignalAmplitude) :
    sourceComplexHistoryCurrent q p t a=PreparationVacuumCurrentSignalRealization.sourceSignalCurrent q p a t :=
  sourceQuadratureCurrent_actual q p t a

theorem sourceCausalWindow_complex_smul (q : PhysicalResponsePoint) (p : Fin 4→ℂ)
    (lambda : ℂ) (T : ℝ) (z : ℂ) (a : SignalAmplitude) :
    sourceCausalWindow q p lambda T (z • a)=z • sourceCausalWindow q p lambda T a :=by
  simp only [sourceCausalWindow,ContinuousLinearMap.intervalIntegral_apply
    ((sourceWeightedQuadrature_continuous q p lambda).intervalIntegrable 0 T)]
  have same (t : ℝ) : sourceWeightedQuadrature q p lambda t (z • a)=z • sourceWeightedQuadrature q p lambda t a :=by
    simp only [sourceWeightedQuadrature,smul_apply,sourceQuadratureCurrent_complex_smul]
    exact smul_comm (laplaceWeight lambda t) z _
  simp_rw [same]
  rw [intervalIntegral.integral_smul]

theorem sourceCausalHalf_complex_smul (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth p<lambda.re) (z : ℂ) (a : SignalAmplitude) :
    sourceCausalHalfOperator q p lambda (z • a)=z • sourceCausalHalfOperator q p lambda a :=by
  have windows:=sourceCausalWindow_operatorNorm q p lambda off
  have left : Tendsto (fun T=>sourceCausalWindow q p lambda T (z • a)) atTop
      (𝓝 (sourceCausalHalfOperator q p lambda (z • a))) :=
    ((ContinuousLinearMap.apply ℝ SignalAmplitude (z • a)).continuous.tendsto _).comp windows
  have right : Tendsto (fun T=>z • sourceCausalWindow q p lambda T a) atTop
      (𝓝 (z • sourceCausalHalfOperator q p lambda a)) :=
    ((((ContinuousLinearMap.apply ℝ SignalAmplitude a).continuous.tendsto _).comp windows).const_smul z)
  exact tendsto_nhds_unique left (right.congr' (Filter.Eventually.of_forall (fun T=>(sourceCausalWindow_complex_smul q p lambda T z a).symm)))


def sourceComplexHalfCurrent (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth p<lambda.re) : SignalAmplitude→L[ℂ] SignalAmplitude where
  toLinearMap:=
    {toFun:=sourceCausalHalfOperator q p lambda
     map_add':=(sourceCausalHalfOperator q p lambda).map_add
     map_smul':=sourceCausalHalf_complex_smul q p lambda off}
  cont:=(sourceCausalHalfOperator q p lambda).continuous

theorem sourceComplexHalfCurrent_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (lambda : ℂ)
    (off : sourceClockGrowth p<lambda.re) (a : SignalAmplitude) :
    sourceComplexHalfCurrent q p lambda off a=sourceCausalHalfOperator q p lambda a :=rfl

theorem sourceLaplaceCurrent_complex_smul (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.re) (z : ℂ) (a : SignalAmplitude) :
    sourceLaplaceCurrent q clock lambda (z • a)=z • sourceLaplaceCurrent q clock lambda a :=by
  simp only [sourceLaplaceCurrent,ContinuousLinearMap.comp_apply,sourceLaplaceAmplitudeMap,
    smul_apply,ContinuousLinearMap.id_apply]
  rw [smul_comm (lambda-clock) z,sourceCausalHalf_complex_smul q _ lambda off]

private theorem ordinary_clock_bound (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.re) : clock.re<lambda.re :=by
  have growth : clock.re ≤ sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock):=by
    change clock.re ≤ max 0 clock.re
    exact le_max_right _ _
  exact growth.trans_lt off

theorem sourceLaplaceInitial_actual (q : PhysicalResponsePoint) (clock lambda : ℂ) (off : clock.re<lambda.re)
    (a : SignalAmplitude) :
    sourceLaplaceInitial q clock lambda a=
      (sourceTemporalFirst (physicalSpatial q.k)+(clock+lambda) • sourceTemporalSecond)*ᵥ((lambda-clock) • a) :=by
  have paid:=sourceLaplaceInitial_history q clock lambda off (sourceLaplaceAmplitudeMap clock lambda a)
  have inverse:=congrArg (fun A : SignalAmplitude→L[ℝ] SignalAmplitude=>A a)
    (sourceLaplaceAmplitudeMap_inverse clock lambda off).2
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at inverse
  rw [inverse,sourceNativeBoundary_initial] at paid
  exact paid

theorem sourceLaplaceInitial_complex_smul (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : clock.re<lambda.re) (z : ℂ) (a : SignalAmplitude) :
    sourceLaplaceInitial q clock lambda (z • a)=z • sourceLaplaceInitial q clock lambda a :=by
  rw [sourceLaplaceInitial_actual q clock lambda off,sourceLaplaceInitial_actual q clock lambda off,
    smul_comm (lambda-clock) z,Matrix.mulVec_smul]

def sourceComplexLaplaceCurrent (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.re) : SignalAmplitude→L[ℂ] SignalAmplitude where
  toLinearMap:=
    {toFun:=sourceLaplaceCurrent q clock lambda
     map_add':=(sourceLaplaceCurrent q clock lambda).map_add
     map_smul':=sourceLaplaceCurrent_complex_smul q clock lambda off}
  cont:=(sourceLaplaceCurrent q clock lambda).continuous

theorem sourceCommonUpdate_complex_smul (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.val.re) (z : ℂ) (a : SignalAmplitude) :
    sourceCommonUpdateOperator q clock lambda (z • a)=z • sourceCommonUpdateOperator q clock lambda a :=by
  rw [sourceCommonUpdateOperator_actual,sourceCommonUpdateOperator_actual,
    sourceLaplaceCurrent_complex_smul q clock lambda.val off,
    sourceLaplaceInitial_complex_smul q clock lambda.val (ordinary_clock_bound q clock lambda.val off),
    ←smul_add,Matrix.mulVec_smul]

def sourceComplexCommonUpdate (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.val.re) : SignalAmplitude→L[ℂ] SignalAmplitude where
  toLinearMap:=
    {toFun:=sourceCommonUpdateOperator q clock lambda
     map_add':=(sourceCommonUpdateOperator q clock lambda).map_add
     map_smul':=sourceCommonUpdate_complex_smul q clock lambda off}
  cont:=(sourceCommonUpdateOperator q clock lambda).continuous

def sourceCurrentMatrix (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.re) : Matrix (Fin 289) (Fin 289) ℂ:=
  LinearMap.toMatrix' (sourceComplexLaplaceCurrent q clock lambda off).toLinearMap

def sourceCurrentUpdateMatrix (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.val.re) : Matrix (Fin 289) (Fin 289) ℂ:=
  LinearMap.toMatrix' (sourceComplexCommonUpdate q clock lambda off).toLinearMap

theorem sourceCurrentMatrix_actual (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.re) (a : SignalAmplitude) :
    sourceCurrentMatrix q clock lambda off*ᵥa=sourceLaplaceCurrent q clock lambda a :=
  LinearMap.toMatrix'_mulVec _ a

theorem sourceCurrentUpdateMatrix_actual (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.val.re) (a : SignalAmplitude) :
    sourceCurrentUpdateMatrix q clock lambda off*ᵥa=sourceCommonUpdateOperator q clock lambda a :=
  LinearMap.toMatrix'_mulVec _ a

theorem sourceCurrentMatrix_column (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.re) (row column : Fin 289) :
    sourceCurrentMatrix q clock lambda off row column=
      sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda
        ((lambda-clock) • Pi.single column 1) row :=by
  rw [sourceCurrentMatrix,LinearMap.toMatrix'_apply]
  change sourceLaplaceCurrent q clock lambda (Pi.single column 1) row=_
  rw [sourceLaplaceCurrent,ContinuousLinearMap.comp_apply,sourceLaplaceAmplitudeMap,smul_apply,ContinuousLinearMap.id_apply]

theorem sourceCurrentUpdateMatrix_column (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.val.re) (row column : Fin 289) :
    sourceCurrentUpdateMatrix q clock lambda off row column=
      (sourceGreen ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩*ᵥ
        (sourceLaplaceCurrent q clock lambda.val (Pi.single column 1)+
          sourceLaplaceInitial q clock lambda.val (Pi.single column 1))) row :=by
  rw [sourceCurrentUpdateMatrix,LinearMap.toMatrix'_apply]
  exact congrFun (sourceCommonUpdateOperator_actual q clock lambda (Pi.single column 1)) row

end LowEnergy.PreparationVacuumCurrentConstrainedInverse
