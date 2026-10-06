import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldFormConsumer
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaPreparedDomain
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCore

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPreparedCurrent
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore
open GaussComposite GaussComposite.SourceGraph
open PreparationVacuumNativeClosure PreparationVacuumWeylDomain PreparationChartGuard
open CanonicalPreparationCore.Completed CanonicalScalarPreparation
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumLocalizedYukawa
open Set Filter Topology
open scoped ContDiff Topology InnerProductSpace LinearPMap

def sourceCut : QuantumTest →ₗ[ℂ] QuantumTest :=
  scalarMultiplier (fun z => (actualNativeLocalizer z : ℂ))
    (Complex.ofRealCLM.contDiff.comp actualNativeLocalizer.contDiff)

theorem sourceCut_apply (test : QuantumTest) (z : SourceCoordinateSlice) :
    sourceCut test z=(actualNativeLocalizer z : ℂ) • test z := rfl

def sourceCoreMap : QuantumTest →ₗ[ℂ] H := embed.comp sourceCut

def localCarrier : Submodule ℂ H := (LinearMap.range sourceCoreMap).topologicalClosure

def localCoreMap : QuantumTest →ₗ[ℂ] localCarrier :=
  sourceCoreMap.codRestrict localCarrier (fun test =>
    (LinearMap.range sourceCoreMap).le_topologicalClosure ⟨test,rfl⟩)

theorem localCarrier_closed : IsClosed (localCarrier : Set H) :=
  (LinearMap.range sourceCoreMap).isClosed_topologicalClosure

theorem localCoreMap_dense : DenseRange localCoreMap := by
  change Dense (Set.range localCoreMap)
  apply (IsInducing.dense_iff (IsInducing.subtypeVal :
    IsInducing ((↑) : localCarrier → H))).mpr
  intro x
  have hx : (x : H)∈closure (Set.range sourceCoreMap) := x.property
  apply closure_mono _ hx
  rintro _ ⟨test,rfl⟩
  exact ⟨localCoreMap test,⟨test,rfl⟩,rfl⟩

def legTest (addition : Bool) (a s : Fin 2) : QuantumTest →ₗ[ℂ] QuantumTest :=
  if addition then creationTest a s else annihilationTest a s

theorem legTest_embed (addition : Bool) (a s : Fin 2) (test : QuantumTest) :
    embed (legTest addition a s test)=leg addition a s test := by
  cases addition
  · exact embed_annihilation_test a s test
  · exact embed_creation_test a s test

theorem sourceCut_legTest (addition : Bool) (a s : Fin 2) (test : QuantumTest) :
    sourceCut (legTest addition a s test)=legTest addition a s (sourceCut test) := by
  apply DFunLike.ext
  intro z
  cases addition
  · change (actualNativeLocalizer z : ℂ) •
      ((rootVolume z : ℂ) • fiberAnnihilation a s (GaussNativePotential.scalarField z) (test z)) =
      (rootVolume z : ℂ) • fiberAnnihilation a s (GaussNativePotential.scalarField z)
        ((actualNativeLocalizer z : ℂ) • test z)
    rw [map_smul,smul_comm (actualNativeLocalizer z : ℂ)]
  · change (actualNativeLocalizer z : ℂ) •
      ((rootVolume z : ℂ)⁻¹ • fiberCreation a s (GaussNativePotential.scalarField z) (test z)) =
      (rootVolume z : ℂ)⁻¹ • fiberCreation a s (GaussNativePotential.scalarField z)
        ((actualNativeLocalizer z : ℂ) • test z)
    rw [map_smul,smul_comm (actualNativeLocalizer z : ℂ)]

theorem preparedCore_sourceCut (test : ScalarTest) :
    preparedCore test=sourceCut (CanonicalPreparationCore.createdCore test) := by
  apply DFunLike.ext
  intro z
  change (CanonicalPreparationCore.numberRaise z*((actualNativeLocalizer z : ℂ)*test z)) •
      CanonicalCompletedSector.seed=(actualNativeLocalizer z : ℂ) •
        ((CanonicalPreparationCore.numberRaise z*test z) • CanonicalCompletedSector.seed)
  rw [smul_smul]
  congr 1
  ring

theorem local_profile_core (test : ScalarTest) :
    zeroLocalizedProfile actualNativeLocalizer (localCore test)=
      CanonicalPreparationCore.profile (sourceVacuumInputCore test) := by
  change localProfile (outerCutoff actualNativeLocalizer)
    (numberRaise (zeroCore (sourceVacuumInputCore test)))=_
  rw [numberRaise_core,localProfile_core]
  apply congrArg core
  apply DFunLike.ext
  intro z
  change (outerCutoff actualNativeLocalizer z : ℂ)*
      (CanonicalPreparationCore.numberRaise z*((actualNativeLocalizer z : ℂ)*test z))=
    CanonicalPreparationCore.numberRaise z*((actualNativeLocalizer z : ℂ)*test z)
  have actual:=congrArg (fun r : ℝ => (r : ℂ)) (outerCutoff_retains actualNativeLocalizer z)
  push_cast at actual
  calc
    _=CanonicalPreparationCore.numberRaise z*
      (((outerCutoff actualNativeLocalizer z : ℂ)*(actualNativeLocalizer z : ℂ))*test z) := by ring
    _=_ := by rw [actual]

def sourceLeg (addition : Bool) (a s : Fin 2) : sourceLocalSpace →L[ℂ] H :=
  (completedLeg addition a s).comp (zeroLocalizedProfile actualNativeLocalizer)

theorem sourceLeg_core (addition : Bool) (a s : Fin 2) (test : ScalarTest) :
    sourceLeg addition a s (localCore test)=embed (legTest addition a s (preparedCore test)) := by
  change completedLeg addition a s (zeroLocalizedProfile actualNativeLocalizer (localCore test))=_
  rw [local_profile_core,CanonicalPreparationCore.original_eight_legs,legTest_embed]
  rfl

theorem sourcePrepared_mem (x : sourceLocalSpace) : sourcePrepared x∈localCarrier := by
  refine localCore_dense.induction_on x (localCarrier_closed.preimage sourcePrepared.continuous) ?_
  intro test
  rw [sourcePrepared_core,preparedCore_sourceCut]
  exact (LinearMap.range sourceCoreMap).le_topologicalClosure
    ⟨CanonicalPreparationCore.createdCore test,rfl⟩

theorem sourceLeg_mem (addition : Bool) (a s : Fin 2) (x : sourceLocalSpace) :
    sourceLeg addition a s x∈localCarrier := by
  refine localCore_dense.induction_on x
    (localCarrier_closed.preimage (sourceLeg addition a s).continuous) ?_
  intro test
  rw [sourceLeg_core,preparedCore_sourceCut,←sourceCut_legTest]
  exact (LinearMap.range sourceCoreMap).le_topologicalClosure
    ⟨legTest addition a s (CanonicalPreparationCore.createdCore test),rfl⟩

def preparedPoint (x : sourceLocalSpace) : localCarrier := ⟨sourcePrepared x,sourcePrepared_mem x⟩
def legPoint (addition : Bool) (a s : Fin 2) (x : sourceLocalSpace) : localCarrier :=
  ⟨sourceLeg addition a s x,sourceLeg_mem addition a s x⟩

theorem sourceLeg_bound (addition : Bool) (a s : Fin 2) (x : sourceLocalSpace) :
    ‖sourceLeg addition a s x‖ ≤
      legBound*CanonicalScalarPreparation.localBound (outerCutoff actualNativeLocalizer)*‖x‖ :=
  zeroLocalized_eight_legs actualNativeLocalizer x addition a s

end LowEnergy.PreparationVacuumPreparedCurrent
