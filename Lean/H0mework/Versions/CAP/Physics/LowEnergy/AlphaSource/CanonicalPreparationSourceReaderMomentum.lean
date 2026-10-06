import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullPoleContinuation
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy FullQuantum.StateGreen
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussQuantumMultiplier
open CanonicalGradedSpatialSource PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActualFieldQuantization PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumSourceActionJets PreparationVacuumMixedFieldReturn
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert PreparationVacuumFullFieldRiesz
open MeasureTheory
open scoped BigOperators Topology Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] rawForm rawReader rawSample

private theorem fourier_momentum_add (A : Fin 4→SourceMatrix) (p k : PhysicalMomentum) :
    realFourierMatrix A (p+k)=realFourierMatrix A p+realFourierMatrix A k-realFourierMatrix A 0:=by
  simp only [realFourier_affine,Pi.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib,
    Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,add_zero]
  abel

private theorem fourier_momentum_smul (A : Fin 4→SourceMatrix) (p : PhysicalMomentum) (r : ℝ) :
    realFourierMatrix A (r • p)=(r:ℂ) • realFourierMatrix A p+(1-r:ℂ) • realFourierMatrix A 0:=by
  simp only [realFourier_affine,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,mul_smul,
    Finset.smul_sum,smul_add,Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,add_zero]
  simp only [sub_smul,one_smul]
  abel

private theorem rawPair_neg (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) (a b : FockFiber) :
    pairSample z a (-b)= -pairSample z a b:=by
  rw [←neg_one_smul ℂ b,pairSample_smul_right,neg_one_mul]

private theorem rawSample_momentum_add (reader : Field289) (p k : PhysicalMomentum)
    (a b : QuantumTest) (u : JointParameter) :
    rawSample reader (p+k) a b u=rawSample reader p a b u+rawSample reader k a b u-rawSample reader 0 a b u:=by
  simp only [rawSample,rawFiber,rawActionSymbol,rawFourier,LinearMap.coe_mk,AddHom.coe_mk,
    fourierLinear,fourier_momentum_add,mul_sub,mul_add,map_sub,map_add,sub_apply,
    add_apply]
  simp only [sub_eq_add_neg,pairSample_add_right,rawPair_neg]

private theorem rawSample_momentum_smul (reader : Field289) (p : PhysicalMomentum) (r : ℝ)
    (a b : QuantumTest) (u : JointParameter) :
    rawSample reader (r • p) a b u=(r:ℂ)*rawSample reader p a b u+(1-r:ℂ)*rawSample reader 0 a b u:=by
  simp only [rawSample,rawFiber,rawActionSymbol,rawFourier,LinearMap.coe_mk,AddHom.coe_mk,
    fourierLinear,fourier_momentum_smul,mul_add,mul_smul_comm,map_add,map_smul,
    add_apply,smul_apply,pairSample_add_right,pairSample_smul_right]

private theorem rawSample_integrable (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (fun z=>rawSample reader p a b (0,z)) configurationMeasure:=
  parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
    (fun z=>rawSample_near_smooth reader p a b 0 z (by simpa only [norm_zero] using ambientRadius_positive a))
    (rawSample_zero reader p a b)

def sourceReaderMomentumForm (reader : Field289) (a b : QuantumTest) : PhysicalMomentum→ₗ[ℝ] ℂ where
  toFun p:=rawForm reader p a b 0-rawForm reader 0 a b 0
  map_add' p k:=by
    have identity : rawForm reader (p+k) a b 0=rawForm reader p a b 0+rawForm reader k a b 0-rawForm reader 0 a b 0:=by
      unfold rawForm
      simp only [rawSample_momentum_add]
      calc
        _=(∫z,(rawSample reader p a b (0,z)+rawSample reader k a b (0,z)) ∂GaussHistoryHilbert.configurationMeasure)-
            ∫z,rawSample reader 0 a b (0,z) ∂GaussHistoryHilbert.configurationMeasure:=
          integral_sub ((rawSample_integrable reader p a b).add (rawSample_integrable reader k a b))
            (rawSample_integrable reader 0 a b)
        _= _:=by rw [integral_add (rawSample_integrable reader p a b) (rawSample_integrable reader k a b)]
    rw [identity]
    abel
  map_smul' r p:=by
    have identity : rawForm reader (r • p) a b 0=(r:ℂ)*rawForm reader p a b 0+(1-r:ℂ)*rawForm reader 0 a b 0:=by
      unfold rawForm
      simp only [rawSample_momentum_smul]
      rw [integral_add ((rawSample_integrable reader p a b).const_mul _) ((rawSample_integrable reader 0 a b).const_mul _),
        integral_const_mul,integral_const_mul]
    rw [identity]
    simp only [RingHom.id_apply,Complex.real_smul]
    ring

theorem rawForm_momentum_continuous (reader : Field289) (a b : QuantumTest) :
    Continuous (fun p : PhysicalMomentum=>rawForm reader p a b 0):=by
  have same : (fun p : PhysicalMomentum=>rawForm reader p a b 0)=
      fun p=>sourceReaderMomentumForm reader a b p+rawForm reader 0 a b 0:=by
    funext p
    exact (sub_add_cancel _ _).symm
  rw [same]
  exact (sourceReaderMomentumForm reader a b).continuous_of_finiteDimensional.add continuous_const

theorem rawReader_momentum_continuous (reader : Field289) (F : GaussUnitaryHistory.Index) :
    Continuous (fun p : PhysicalMomentum=>rawReader reader p F 0):=by
  unfold rawReader finiteRiesz
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (rawForm_momentum_continuous reader (frameTest F i) (frameTest F j)).smul continuous_const

end LowEnergy.PreparationVacuumFullPoleContinuation
