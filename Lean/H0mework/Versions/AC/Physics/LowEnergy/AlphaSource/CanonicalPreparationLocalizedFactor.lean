import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativeOperator
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalFormPreparation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeClosure
open PreparationVacuumWeylDomain PreparationVacuumWeylOperator PreparationVacuumWeylDecay PreparationChartGuard
open CanonicalPreparationSquareCutoff
open CanonicalPreparationCore.Completed CanonicalScalarPreparation
open GaussDensityCore GaussHistoryHilbert MeasureTheory Set Topology
open scoped SchwartzMap FourierTransform LinearPMap

abbrev sourceLocalSpace := zeroLocalizedSpace actualNativeLocalizer

theorem original_local_core_mem (f : ScalarTest) :
    zeroCore (sourceVacuumInputCore f)∈sourceLocalSpace := by
  change zeroCore (cutCore actualNativeLocalizer f)∈sourceLocalSpace
  rw [←zeroCutoff_core actualNativeLocalizer f]
  exact (LinearMap.range (zeroCutoff actualNativeLocalizer).toLinearMap).le_topologicalClosure
    ⟨zeroCore f,rfl⟩

def localCore : ScalarTest →ₗ[ℂ] sourceLocalSpace :=
  (zeroCore.comp sourceVacuumInputCore).codRestrict sourceLocalSpace original_local_core_mem

theorem localCore_ambient (f : ScalarTest) :
    (localCore f).val=zeroCutoff actualNativeLocalizer (zeroCore f) :=
  (zeroCutoff_core actualNativeLocalizer f).symm

theorem original_local_core_closure :
    closure (Set.range (fun f : ScalarTest => (localCore f).val))=
      (sourceLocalSpace : Set (SectorHilbert 0)) := by
  have whole (u : SectorHilbert 0) : zeroCutoff actualNativeLocalizer u∈
      closure (Set.range (fun f : ScalarTest => (localCore f).val)) := by
    have image := image_closure_subset_closure_image
      (zeroCutoff actualNativeLocalizer).continuous (s := Set.range zeroCore)
    have member := image (Set.mem_image_of_mem (zeroCutoff actualNativeLocalizer) (zeroCore_dense u))
    have same : zeroCutoff actualNativeLocalizer '' Set.range zeroCore=
        Set.range (fun f : ScalarTest => (localCore f).val) := by
      ext v
      constructor
      · rintro ⟨_,⟨f,rfl⟩,rfl⟩
        exact ⟨f,localCore_ambient f⟩
      · rintro ⟨f,rfl⟩
        exact ⟨zeroCore f,⟨f,rfl⟩,(localCore_ambient f).symm⟩
    rw [same] at member
    exact member
  apply le_antisymm
  · apply closure_minimal
    · rintro _ ⟨f,rfl⟩
      exact (localCore f).property
    · exact (LinearMap.range (zeroCutoff actualNativeLocalizer).toLinearMap).isClosed_topologicalClosure
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨u,rfl⟩
    exact whole u

theorem localCore_dense : DenseRange localCore := by
  change Dense (Set.range localCore)
  apply (IsInducing.dense_iff (IsInducing.subtypeVal :
    IsInducing ((↑) : sourceLocalSpace → SectorHilbert 0))).mpr
  intro x
  have ambient : (x : SectorHilbert 0)∈
      closure (Set.range (fun f : ScalarTest => (localCore f).val)) := by
    rw [original_local_core_closure]
    exact x.property
  apply closure_mono _ ambient
  rintro _ ⟨f,rfl⟩
  exact ⟨localCore f,⟨f,rfl⟩,rfl⟩

abbrev localCoreDomain : Submodule ℂ sourceLocalSpace := LinearMap.range localCore

def localCoreInclusion : localCoreDomain →ₗ[ℂ] originalCoreDomain :=
  ((sourceLocalSpace.subtype.comp localCoreDomain.subtype).codRestrict originalCoreDomain
    (fun x => by
      obtain ⟨f,heq⟩:=x.property
      refine ⟨sourceVacuumInputCore f,?_⟩
      exact congrArg (fun u : sourceLocalSpace => u.val) heq))

theorem localCoreInclusion_original (f : ScalarTest) :
    localCoreInclusion (localCore.rangeRestrict f)=zeroCore.rangeRestrict (sourceVacuumInputCore f) :=
  rfl

theorem localCoreDomain_dense : Dense (localCoreDomain : Set sourceLocalSpace) := localCore_dense

def localInput : sourceLocalSpace →L[ℂ] FourierHilbert :=
  nativeInput.comp sourceLocalSpace.subtypeL

theorem localInput_core (x : localCoreDomain) :
    localInput x.val=(coreFrequencyInput (localCoreInclusion x)).toLp 2 :=
  nativeInput_core (localCoreInclusion x)

def localCoreFactor : sourceLocalSpace →ₗ.[ℂ] FourierHilbert where
  domain := localCoreDomain
  toFun := coreFactor.toFun.comp localCoreInclusion

theorem localCoreFactor_dense : Dense (localCoreFactor.domain : Set sourceLocalSpace) :=
  localCoreDomain_dense

theorem localCoreFactor_original (f : ScalarTest) :
    localCoreFactor (localCore.rangeRestrict f)=
      fourierActionLp (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  change coreFactor (localCoreInclusion (localCore.rangeRestrict f))=_
  rw [localCoreInclusion_original]
  exact coreFactor_original (sourceVacuumInputCore f)

def localAdjointRead (g : 𝓢(PhysicalMomentum,ℂ)) : sourceLocalSpace :=
  localInput.adjoint (fourierActionLp g)

theorem localAdjointRead_pair (x : localCoreFactor.domain) (g : 𝓢(PhysicalMomentum,ℂ)) :
    inner ℂ (localCoreFactor x) (g.toLp 2)=inner ℂ x.val (localAdjointRead g) := by
  rw [localAdjointRead,ContinuousLinearMap.adjoint_inner_right,localInput_core]
  exact fourierActionLp_hermitian g (coreFrequencyInput (localCoreInclusion x))

theorem local_Schwartz_adjoint_domain (g : 𝓢(PhysicalMomentum,ℂ)) :
    g.toLp 2 (volume : Measure PhysicalMomentum)∈localCoreFactor.adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists (T := localCoreFactor) (g.toLp 2 volume)
  refine ⟨localAdjointRead g,?_⟩
  intro x
  rw [←inner_conj_symm (localAdjointRead g) x.val,
    ←inner_conj_symm (g.toLp 2 volume) (localCoreFactor x)]
  exact congrArg (starRingEnd ℂ) (localAdjointRead_pair x g).symm

theorem localCoreFactor_adjoint_dense : Dense (localCoreFactor.adjoint.domain : Set FourierHilbert) := by
  apply (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) ENNReal.ofNat_ne_top).mono
  rintro _ ⟨g,rfl⟩
  exact local_Schwartz_adjoint_domain g

theorem localCoreFactor_closable : localCoreFactor.IsClosable := by
  have formal := LinearPMap.adjoint_isFormalAdjoint (T := localCoreFactor) localCoreFactor_dense
  have extension : localCoreFactor≤localCoreFactor.adjoint.adjoint :=
    formal.le_adjoint localCoreFactor_adjoint_dense
  exact (LinearPMap.adjoint_isClosed localCoreFactor_adjoint_dense).isClosable.leIsClosable extension

def sourceClosedFactor : sourceLocalSpace →ₗ.[ℂ] FourierHilbert := localCoreFactor.closure

theorem sourceClosedFactor_closed : sourceClosedFactor.IsClosed := localCoreFactor_closable.closure_isClosed

theorem sourceClosedFactor_dense : Dense (sourceClosedFactor.domain : Set sourceLocalSpace) :=
  localCoreFactor_dense.mono localCoreFactor.le_closure.1

theorem sourceClosedFactor_original (f : ScalarTest) :
    sourceClosedFactor ⟨localCore f,
      localCoreFactor.le_closure.1 (LinearMap.mem_range_self localCore f)⟩=
      fourierActionLp (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  have same := localCoreFactor.le_closure.2 (x := localCore.rangeRestrict f)
    (y := ⟨localCore f,localCoreFactor.le_closure.1 (LinearMap.mem_range_self localCore f)⟩) rfl
  exact same.symm.trans (localCoreFactor_original f)

theorem sourceClosedFactor_weyl_readback (f : ScalarTest) :
    Lp.toTemperedDistribution (𝓕⁻ (sourceClosedFactor ⟨localCore f,
      localCoreFactor.le_closure.1 (LinearMap.mem_range_self localCore f)⟩))=
      actualVacuumWeyl (sourceVacuumInputCore f) := by
  rw [sourceClosedFactor_original,←Lp.fourierInv_toTemperedDistribution_eq,
    fourierActionLp_tempered_readback]
  rfl

end LowEnergy.PreparationVacuumNativeClosure
