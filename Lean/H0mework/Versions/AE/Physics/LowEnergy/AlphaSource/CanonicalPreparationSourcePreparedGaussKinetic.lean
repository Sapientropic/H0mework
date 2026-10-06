import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussMomentumReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGaussMeasureReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussFockPair
open PreparationVacuumCoframeLegendreSource PreparationVacuumSpinGaussContraction
open scoped Topology ContDiff BigOperators Matrix

private theorem sourceNumberScalarAction_apply (j : Fin 6) (f : QuantumTest)
    (z : SourceCoordinateSlice) (word : Occupation) :
    sourceNumberScalarAction j f z word=
      (sourceNumberConnection z.1 j:ℂ)*(word.card:ℂ)*f z word:=by
  change (sourceNumberConnection z.1 j:ℂ)*fiberNumber (f z) word=_
  rw [fiberNumber_apply]
  ring

theorem sourceNumberScalar_pair (j : Fin 6) (f g : QuantumTest) :
    sourcePair f (sourceNumberScalarAction j g)=sourcePair (sourceNumberScalarAction j f) g:=by
  rw [sourcePair_integral,sourcePair_integral]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  rw [densityPair_sum,densityPair_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [sourceNumberScalarAction_apply,sourceNumberScalarAction_apply]
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal,map_natCast]
  ring

theorem sourceNoetherMomentum_pair (j : Fin 6) (f g : QuantumTest) :
    sourcePair f (sourceNoetherMomentumRight j g)=sourcePair (sourceNoetherMomentumLeft j f) g:=by
  have momentum := GaussCoframeCore.momentum_pair j f g
  have number := sourceNumberScalar_pair j f g
  have connection := SourceCoframeCovariantAction.original_connection_pair j f g
  unfold sourcePair at momentum number connection ⊢
  simp only [sourceNoetherMomentumRight,sourceNoetherMomentumLeft,LinearMap.add_apply,
    LinearMap.sub_apply,LinearMap.smul_apply,map_add,map_sub,map_smul,inner_add_right,
    inner_add_left,inner_sub_right,inner_smul_right,inner_smul_left,Complex.conj_I]
  rw [momentum,number,connection]
  ring

theorem sourceNoetherMomentum_pair_reversed (j : Fin 6) (f g : QuantumTest) :
    sourcePair f (sourceNoetherMomentumLeft j g)=sourcePair (sourceNoetherMomentumRight j f) g:=by
  have actual := congrArg (starRingEnd ℂ) (sourceNoetherMomentum_pair j g f)
  rw [GaussNativeForm.pair_conjugate,GaussNativeForm.pair_conjugate] at actual
  exact actual.symm

def sourceKineticCoefficient (i j : Fin 6) (z : SourceCoordinateSlice) : ℝ:=
  (1/2:ℝ)*sourceGaussVelocityInverse z i j

theorem sourceKineticCoefficient_original (i j : Fin 6) (z : SourceCoordinateSlice) :
    sourceKineticCoefficient i j z=GaussCoframeKinetic.coefficient i j z:=by
  simp only [sourceKineticCoefficient,sourceGaussVelocityInverse,Pi.smul_apply,smul_eq_mul]
  ring

theorem sourceKineticCoefficient_smooth (i j : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceKineticCoefficient i j) z.val:=by
  have same : sourceKineticCoefficient i j=GaussCoframeKinetic.coefficient i j:=
    funext (fun w=>sourceKineticCoefficient_original i j w)
  rw [same]
  exact GaussCoframeKinetic.coefficient_smooth i j z

def sourceKineticMetric (i j : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussNativeForm.multiply (sourceKineticCoefficient i j) (sourceKineticCoefficient_smooth i j)

def sourcePreparedKinetic : QuantumTest→ₗ[ℂ] QuantumTest:=
  ∑i : Fin 6,∑j : Fin 6,sourceNoetherMomentumLeft i*sourceKineticMetric i j*sourceNoetherMomentumRight j

theorem sourceKineticMetric_original (i j : Fin 6) :
    sourceKineticMetric i j=SourceCoframeCovariantAction.metricAction i j:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (sourceKineticCoefficient i j z:ℂ) • f z=(GaussCoframeKinetic.coefficient i j z:ℂ) • f z
  rw [sourceKineticCoefficient_original]

theorem sourcePreparedKinetic_pair (f g : QuantumTest) :
    sourcePair f (sourcePreparedKinetic g)=sourcePair (sourcePreparedKinetic f) g:=by
  simp only [sourcePreparedKinetic,LinearMap.sum_apply,Module.End.mul_apply,
    sourcePair,map_sum,inner_sum,sum_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (sourceNoetherMomentumLeft i
      (sourceKineticMetric i j (sourceNoetherMomentumRight j g)))=
    sourcePair (sourceNoetherMomentumLeft j
      (sourceKineticMetric j i (sourceNoetherMomentumRight i f))) g
  rw [sourceNoetherMomentum_pair_reversed]
  have metricPair (u v : QuantumTest) : sourcePair u (sourceKineticMetric i j v)=
      sourcePair (sourceKineticMetric i j u) v:=by
    simpa only [sourceKineticMetric] using GaussNativeForm.multiply_pair
      (sourceKineticCoefficient i j) (sourceKineticCoefficient_smooth i j) u v
  rw [metricPair,sourceNoetherMomentum_pair]
  have symmetric : sourceKineticMetric i j=sourceKineticMetric j i:=by
    rw [sourceKineticMetric_original,sourceKineticMetric_original]
    apply LinearMap.ext
    intro h
    apply DFunLike.ext
    intro z
    change (GaussCoframeKinetic.coefficient i j z:ℂ) • h z=
      (GaussCoframeKinetic.coefficient j i z:ℂ) • h z
    rw [GaussCoframeKinetic.coefficient_symmetric]
  rw [symmetric]

def sourcePreparedNumberCorrection : QuantumTest→ₗ[ℂ] QuantumTest:=
  ∑i : Fin 6,∑j : Fin 6,
    (Complex.I • (sourceNumberScalarAction i*sourceKineticMetric i j*
      SourceCoframeCovariantAction.covariantMomentum j)-
      Complex.I • (SourceCoframeCovariantAction.covariantAdjoint i*sourceKineticMetric i j*
        sourceNumberScalarAction j)+
      sourceNumberScalarAction i*sourceKineticMetric i j*sourceNumberScalarAction j)

theorem sourcePreparedKinetic_generated :
    sourcePreparedKinetic=SourceCoframeCovariantAction.covariantKinetic+sourcePreparedNumberCorrection:=by
  have right (j : Fin 6) : sourceNoetherMomentumRight j=
      SourceCoframeCovariantAction.covariantMomentum j-Complex.I • sourceNumberScalarAction j:=by
    simp only [sourceNoetherMomentumRight,SourceCoframeCovariantAction.covariantMomentum]
    abel
  have left (i : Fin 6) : sourceNoetherMomentumLeft i=
      SourceCoframeCovariantAction.covariantAdjoint i+Complex.I • sourceNumberScalarAction i:=by
    simp only [sourceNoetherMomentumLeft,SourceCoframeCovariantAction.covariantAdjoint]
    abel
  have term (i j : Fin 6) :
      sourceNoetherMomentumLeft i*sourceKineticMetric i j*sourceNoetherMomentumRight j=
        SourceCoframeCovariantAction.covariantAdjoint i*sourceKineticMetric i j*
          SourceCoframeCovariantAction.covariantMomentum j+
          Complex.I • (sourceNumberScalarAction i*sourceKineticMetric i j*
            SourceCoframeCovariantAction.covariantMomentum j)-
          Complex.I • (SourceCoframeCovariantAction.covariantAdjoint i*sourceKineticMetric i j*
            sourceNumberScalarAction j)+
          sourceNumberScalarAction i*sourceKineticMetric i j*sourceNumberScalarAction j:=by
    rw [right,left]
    simp only [add_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_add,smul_smul,Complex.I_mul_I]
    module
  simp only [sourcePreparedKinetic,term,sourcePreparedNumberCorrection,
    SourceCoframeCovariantAction.covariantKinetic,←sourceKineticMetric_original,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

end LowEnergy.PreparationVacuumGaussMeasureReturn
