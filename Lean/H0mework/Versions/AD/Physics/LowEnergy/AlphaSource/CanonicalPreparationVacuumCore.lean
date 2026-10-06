import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSpin

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFactor
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart GaussFockPair
open GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum GaussDensityCore GaussHistoryHilbert
open GaussQuantumMultiplier CanonicalPreparationCreation CanonicalPreparationMomentum
open scoped BigOperators ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

theorem quantized_vacuum (A : Matrix Mode Mode ℂ) : quantized A vacuumFiber=0 := by
  apply fiberCoordinates.injective
  change fiberCoordinates (fiberCoordinates.symm
    (LowEnergy.Fermion.quantize A (fiberCoordinates vacuumFiber)))=fiberCoordinates 0
  rw [LinearEquiv.apply_symm_apply,map_zero]
  change LowEnergy.Fermion.quantize A QuantizationCheck.Fermion.vacuum=0
  rw [LowEnergy.Fermion.quantize_apply]
  funext word
  simp [QuantizationCheck.Fermion.secondQuantize,QuantizationCheck.Fermion.create]

theorem nativeFock_vacuum (a : NativeLie) : GaussNativeMatter.nativeFock a vacuumFiber=0 :=
  quantized_vacuum (GaussNativeMatter.nativeFull a)

theorem quantized_adjoint (A : Matrix Mode Mode ℂ) : (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro psi
  apply ext_inner_left ℂ
  intro phi
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact quantizedFiber_adjoint A phi psi

theorem adjoint_vacuum (A : Matrix Mode Mode ℂ) : (quantized A).adjoint vacuumFiber=0 := by
  rw [quantized_adjoint,quantized_vacuum]

theorem vacuumSection_apply (f : ScalarTest) (z : SourceCoordinateSlice) :
    vacuumSection f z=f z • vacuumFiber := rfl

theorem vacuum_component (f : ScalarTest) (word : Occupation) :
    component word (vacuumSection f)=vacuumFiber word • f := by
  apply DFunLike.ext
  intro z
  change f z*vacuumFiber word=vacuumFiber word*f z
  ring

theorem multiplier_vacuum (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => quantized (A w)) z.val)
    (f : ScalarTest) : action A smooth (vacuumSection f)=0 := by
  apply DFunLike.ext
  intro z
  change quantized (A z) (f z • vacuumFiber)=0
  rw [map_smul,quantized_vacuum,smul_zero]

theorem connection_vacuum (v : Ambient) (f : ScalarTest) :
    connectionAction v (vacuumSection f)=0 := by
  apply DFunLike.ext
  intro z
  change GaussNativeMatter.nativeFock (inverseL z v).1 (f z • vacuumFiber)=0
  rw [map_smul,nativeFock_vacuum,smul_zero]

theorem directional_vacuum (v : Ambient) (f : ScalarTest) :
    directional v (vacuumSection f)=vacuumSection (GaussScalarTransport.fieldDerivative v f) := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have identity := GaussMomentumAdjoint.component_directional v (vacuumSection f) word
  rw [vacuum_component,map_smul] at identity
  have value := congrArg (fun g : ScalarTest => g z) identity
  change directional v (vacuumSection f) z word=
    GaussScalarTransport.fieldDerivative v f z*vacuumFiber word
  exact value.trans (mul_comm _ _)

theorem transpose_vacuum (v : Ambient) (f : ScalarTest) :
    GaussMomentumAdjoint.derivativeTranspose v (vacuumSection f)=
      vacuumSection (GaussScalarTransport.fieldTranspose 0 v f) := by
  apply embed_injective
  rw [GaussMomentumAdjoint.transpose_embed]
  apply PiLp.ext
  intro word
  change scalarLp word.card
      (GaussScalarTransport.fieldTranspose word.card v (component word (vacuumSection f)))=
    scalarLp word.card (component word
      (vacuumSection (GaussScalarTransport.fieldTranspose 0 v f)))
  rw [vacuum_component,vacuum_component,map_smul,GaussComposite.SourceGraph.scalarLp_smul,
    GaussComposite.SourceGraph.scalarLp_smul]
  by_cases empty : word=∅
  · subst word
    rfl
  · have zero : vacuumFiber word=0 := by
      rw [vacuumFiber_single]
      simp [EuclideanSpace.single,empty]
    rw [zero]
    simp

theorem momentum_vacuum (v : Ambient) (f : ScalarTest) :
    covariantMomentum v (vacuumSection f)=
      (-Complex.I) • vacuumSection (GaussScalarTransport.fieldDerivative v f) := by
  change (-Complex.I) • (directional v (vacuumSection f)+connectionAction v (vacuumSection f))=_
  rw [directional_vacuum,connection_vacuum,add_zero]

theorem momentum_adjoint_vacuum (v : Ambient) (f : ScalarTest) :
    GaussMomentumAdjoint.adjoint v (vacuumSection f)=
      Complex.I • vacuumSection (GaussScalarTransport.fieldTranspose 0 v f) := by
  rw [GaussMomentumAdjoint.adjoint,LinearMap.smul_apply,LinearMap.sub_apply,
    transpose_vacuum,connection_vacuum,sub_zero]

def realCoefficient (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : ScalarTest →ₗ[ℂ] ScalarTest :=
  GaussDensityCore.multiply (fun z => (c z : ℂ))
    (fun z => Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (smooth z))

theorem multiply_vacuum (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f : ScalarTest) :
    GaussNativeForm.multiply c smooth (vacuumSection f)=
      vacuumSection (realCoefficient c smooth f) := by
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • (f z • vacuumFiber)=((c z : ℂ)*f z) • vacuumFiber
  exact (mul_smul _ _ _).symm

def scalarSandwich (v w : Ambient) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : ScalarTest →ₗ[ℂ] ScalarTest :=
  (GaussScalarTransport.fieldTranspose 0 v).comp
    ((realCoefficient c smooth).comp (GaussScalarTransport.fieldDerivative w))

theorem sandwich_vacuum (v w : Ambient) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f : ScalarTest) :
    GaussNativeForm.sandwich v w c smooth (vacuumSection f)=
      vacuumSection (scalarSandwich v w c smooth f) := by
  simp only [GaussNativeForm.sandwich,LinearMap.comp_apply]
  rw [momentum_vacuum,map_smul,multiply_vacuum,map_smul,momentum_adjoint_vacuum]
  simp only [smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  rfl

end LowEnergy.PreparationVacuumFactor
