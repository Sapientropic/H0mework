import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoreDescent
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylL2

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeClosure
open PreparationVacuumWeyl PreparationVacuumWeylDomain PreparationVacuumWeylOperator
open PreparationVacuumWeylDecay PreparationChartGuard
open CanonicalPreparationCore.Completed CanonicalPreparationSquareCutoff
open GaussDensityCore GaussHistoryHilbert MeasureTheory Filter
open scoped SchwartzMap FourierTransform ComplexConjugate LinearPMap

theorem fourierActionLp_weak_pair (g f : 𝓢(PhysicalMomentum,ℂ)) :
    weakWeylForm g f=inner ℂ (g.toLp 2) (fourierActionLp f) := by
  rw [weakWeylForm_actual_action,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 volume,fourierActionLp_readback f] with xi hg hf
  rw [hg,hf]
  simp only [RCLike.inner_apply,mul_comm]

theorem fourierActionLp_hermitian (g f : 𝓢(PhysicalMomentum,ℂ)) :
    inner ℂ (fourierActionLp f) (g.toLp 2)=inner ℂ (f.toLp 2) (fourierActionLp g) := by
  calc
    _ = conj (inner ℂ (g.toLp 2) (fourierActionLp f)) := (inner_conj_symm _ _).symm
    _ = conj (weakWeylForm g f) := congrArg conj (fourierActionLp_weak_pair g f).symm
    _ = weakWeylForm f g := weakWeylForm_hermitian f g
    _ = _ := fourierActionLp_weak_pair f g

def nativeInput : SectorHilbert 0 →L[ℂ] FourierHilbert :=
  (sourceFrequencyHalfDensity 0).toContinuousLinearMap.comp (zeroCutoff actualNativeLocalizer)

theorem nativeInput_core (x : originalCoreDomain) :
    nativeInput x.val=(coreFrequencyInput x).toLp 2 :=
  (coreFrequencyInput_native_readback x).symm

def coreFactor : SectorHilbert 0 →ₗ.[ℂ] FourierHilbert where
  domain := originalCoreDomain
  toFun := fourierActionLpLinear.comp coreFrequencyInput

theorem coreFactor_dense : Dense (coreFactor.domain : Set (SectorHilbert 0)) :=
  originalCoreDomain_dense

theorem coreFactor_original (f : GaussDensityCore.ScalarTest) :
    coreFactor (zeroCore.rangeRestrict f)=fourierActionLp (sourceVacuumInputFrequency f) := by
  change fourierActionLp (coreFrequencyInput (zeroCore.rangeRestrict f))=_
  rw [coreFrequencyInput_original]

def nativeAdjointRead (g : 𝓢(PhysicalMomentum,ℂ)) : SectorHilbert 0 :=
  nativeInput.adjoint (fourierActionLp g)

theorem nativeAdjointRead_pair (x : coreFactor.domain) (g : 𝓢(PhysicalMomentum,ℂ)) :
    inner ℂ (coreFactor x) (g.toLp 2)=inner ℂ x.val (nativeAdjointRead g) := by
  rw [nativeAdjointRead,ContinuousLinearMap.adjoint_inner_right,nativeInput_core]
  exact fourierActionLp_hermitian g (coreFrequencyInput x)

theorem original_Schwartz_adjoint_domain (g : 𝓢(PhysicalMomentum,ℂ)) :
    g.toLp 2 (volume : Measure PhysicalMomentum)∈coreFactor.adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists (T := coreFactor) (g.toLp 2 volume)
  refine ⟨nativeAdjointRead g,?_⟩
  intro x
  rw [←inner_conj_symm (nativeAdjointRead g) x.val,
    ←inner_conj_symm (g.toLp 2 volume) (coreFactor x)]
  exact congrArg conj (nativeAdjointRead_pair x g).symm

theorem coreFactor_adjoint_dense : Dense (coreFactor.adjoint.domain : Set FourierHilbert) := by
  apply (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
    ENNReal.ofNat_ne_top).mono
  rintro _ ⟨g,rfl⟩
  exact original_Schwartz_adjoint_domain g

theorem coreFactor_closable : coreFactor.IsClosable := by
  have formal := LinearPMap.adjoint_isFormalAdjoint (T := coreFactor) coreFactor_dense
  have extension : coreFactor≤coreFactor.adjoint.adjoint :=
    formal.le_adjoint coreFactor_adjoint_dense
  exact (LinearPMap.adjoint_isClosed coreFactor_adjoint_dense).isClosable.leIsClosable extension

def closedFactor : SectorHilbert 0 →ₗ.[ℂ] FourierHilbert := coreFactor.closure

theorem closedFactor_closed : closedFactor.IsClosed := coreFactor_closable.closure_isClosed

theorem closedFactor_dense : Dense (closedFactor.domain : Set (SectorHilbert 0)) :=
  coreFactor_dense.mono coreFactor.le_closure.1

theorem closedFactor_original (f : GaussDensityCore.ScalarTest) :
    closedFactor ⟨zeroCore f,coreFactor.le_closure.1 (LinearMap.mem_range_self zeroCore f)⟩=
      fourierActionLp (sourceVacuumInputFrequency f) := by
  have same := coreFactor.le_closure.2 (x := zeroCore.rangeRestrict f)
    (y := ⟨zeroCore f,coreFactor.le_closure.1 (LinearMap.mem_range_self zeroCore f)⟩) rfl
  exact same.symm.trans (coreFactor_original f)

end LowEnergy.PreparationVacuumNativeClosure
