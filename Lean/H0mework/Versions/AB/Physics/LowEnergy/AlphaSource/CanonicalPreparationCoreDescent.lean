import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylOperator
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeClosure
open PreparationVacuumWeylDomain PreparationVacuumWeylOperator
open CanonicalPreparationSquareCutoff
open CanonicalPreparationCore.Completed PreparationChartGuard
open GaussDensityCore GaussHistoryHilbert MeasureTheory
open scoped SchwartzMap FourierTransform

theorem original_frequency_core_kernel :
    LinearMap.ker zeroCore ≤ LinearMap.ker sourceVacuumFrequencyLinear := by
  intro f coreZero
  have original : (sourceVacuumInputFrequency f).toLp 2=0 := by
    rw [←actual_N0_input_profile f]
    change sourceFrequencyHalfDensity 0 (zeroCutoff actualNativeLocalizer (zeroCore f))=0
    rw [LinearMap.mem_ker.mp coreZero,map_zero,map_zero]
  apply LinearMap.mem_ker.mpr
  apply SchwartzMap.injective_toLp 2 (volume : Measure PhysicalMomentum)
  change (sourceVacuumInputFrequency f).toLp 2=(0 : 𝓢(PhysicalMomentum,ℂ)).toLp 2
  rw [original]
  change 0=SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure PhysicalMomentum) 0
  exact (map_zero _).symm

abbrev originalCoreDomain : Submodule ℂ (SectorHilbert 0) := LinearMap.range zeroCore

def coreFrequencyInput : originalCoreDomain →ₗ[ℂ] 𝓢(PhysicalMomentum,ℂ) :=
  ((LinearMap.ker zeroCore).liftQ sourceVacuumFrequencyLinear
    original_frequency_core_kernel).comp zeroCore.quotKerEquivRange.symm.toLinearMap

theorem coreFrequencyInput_original (f : GaussDensityCore.ScalarTest) :
    coreFrequencyInput (zeroCore.rangeRestrict f)=sourceVacuumInputFrequency f := by
  rw [coreFrequencyInput,LinearMap.comp_apply,LinearEquiv.coe_coe]
  change (zeroCore.ker.liftQ sourceVacuumFrequencyLinear original_frequency_core_kernel)
    (zeroCore.quotKerEquivRange.symm ⟨zeroCore f,LinearMap.mem_range_self zeroCore f⟩)=_
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem coreFrequencyInput_native_readback (x : originalCoreDomain) :
    (coreFrequencyInput x).toLp 2=
      sourceFrequencyHalfDensity 0 (zeroCutoff actualNativeLocalizer x.val) := by
  obtain ⟨f,rfl⟩:=zeroCore.surjective_rangeRestrict x
  rw [coreFrequencyInput_original]
  exact (actual_N0_input_profile f).symm

theorem originalCoreDomain_dense : Dense (originalCoreDomain : Set (SectorHilbert 0)) :=
  zeroCore_dense

def nativeCoreFrequency : SectorHilbert 0 →ₗ.[ℂ] 𝓢(PhysicalMomentum,ℂ) where
  domain := originalCoreDomain
  toFun := coreFrequencyInput

theorem nativeCoreFrequency_dense :
    Dense (nativeCoreFrequency.domain : Set (SectorHilbert 0)) := originalCoreDomain_dense

end LowEnergy.PreparationVacuumNativeClosure
