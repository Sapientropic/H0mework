import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationLocalCurrentCarrier

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
open CanonicalGradedSpatialSource
open Set Filter Topology
open scoped ContDiff Topology InnerProductSpace LinearPMap

def sourceCover := outerCutoff actualNativeLocalizer

theorem covered_core_exact (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (retains : ∀ z,phi z*actualNativeLocalizer z=actualNativeLocalizer z) (test : QuantumTest) :
    localizedCore f p phi (sourceCut test)=familyCore f p (sourceCut test) := by
  apply DFunLike.ext
  intro z
  change (phi z:ℂ) • fiberFamily f p z ((actualNativeLocalizer z:ℂ) • test z)=
    fiberFamily f p z ((actualNativeLocalizer z:ℂ) • test z)
  rw [map_smul,smul_smul,←Complex.ofReal_mul,retains]

theorem sourceCut_family (f : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    familyCore f p (sourceCut test)=sourceCut (familyCore f p test) := by
  apply DFunLike.ext
  intro z
  exact (fiberFamily f p z).map_smul (actualNativeLocalizer z:ℂ) (test z)

def fullCurrent (f : Field289) (p : PhysicalMomentum) : localCarrier →L[ℂ] H :=
  (localizedGauss f p sourceCover).comp localCarrier.subtypeL

def currentPrice (f : Field289) (p : PhysicalMomentum) : ℝ :=
  PreparationVacuumSourceFieldFamily.localBound f p sourceCover

theorem currentPrice_nonnegative (f : Field289) (p : PhysicalMomentum) : 0 ≤ currentPrice f p :=
  PreparationVacuumSourceFieldFamily.localBound_nonnegative f p sourceCover

theorem fullCurrent_core (f : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    fullCurrent f p (localCoreMap test)=embed (familyCore f p (sourceCut test)) := by
  change localizedGauss f p sourceCover (embed (sourceCut test))=_
  rw [localizedGauss_core,covered_core_exact f p sourceCover
    (outerCutoff_retains actualNativeLocalizer)]

theorem fullCurrent_bound (f : Field289) (p : PhysicalMomentum) (x : localCarrier) :
    ‖fullCurrent f p x‖ ≤ currentPrice f p*‖x‖ := by
  exact ((localizedGauss f p sourceCover).le_opNorm x.val).trans
    (mul_le_mul_of_nonneg_right (localizedGauss_norm f p sourceCover) (norm_nonneg x.val))

theorem fullCurrent_cover_independent (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (retains : ∀ z,phi z*actualNativeLocalizer z=actualNativeLocalizer z) (x : localCarrier) :
    localizedGauss f p phi x.val=fullCurrent f p x := by
  refine localCoreMap_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro test
  change localizedGauss f p phi (embed (sourceCut test))=_
  rw [localizedGauss_core,covered_core_exact f p phi retains,fullCurrent_core]

theorem fullCurrent_mem (f : Field289) (p : PhysicalMomentum) (x : localCarrier) :
    fullCurrent f p x∈localCarrier := by
  refine localCoreMap_dense.induction_on x
    (localCarrier_closed.preimage (fullCurrent f p).continuous) ?_
  intro test
  rw [fullCurrent_core,sourceCut_family]
  exact (LinearMap.range sourceCoreMap).le_topologicalClosure ⟨familyCore f p test,rfl⟩

def current (f : Field289) (p : PhysicalMomentum) : localCarrier →L[ℂ] localCarrier :=
  (fullCurrent f p).codRestrict localCarrier (fullCurrent_mem f p)

theorem current_core (f : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    current f p (localCoreMap test)=localCoreMap (familyCore f p test) := by
  apply Subtype.ext
  exact (fullCurrent_core f p test).trans (congrArg embed (sourceCut_family f p test))

theorem current_norm (f : Field289) (p : PhysicalMomentum) : ‖current f p‖ ≤ currentPrice f p :=
  ContinuousLinearMap.opNorm_le_bound _ (currentPrice_nonnegative f p) (fullCurrent_bound f p)

def originalCoreGraph (f : Field289) (p : PhysicalMomentum) : Set (localCarrier × H) :=
  Set.range (fun test : QuantumTest=>
    (localCoreMap test,embed (familyCore f p (sourceCut test))))

theorem original_core_graph_closed (f : Field289) (p : PhysicalMomentum) :
    closure (originalCoreGraph f p)={xy | fullCurrent f p xy.1=xy.2} := by
  apply le_antisymm
  · apply closure_minimal
    · rintro _ ⟨test,rfl⟩
      exact fullCurrent_core f p test
    · exact isClosed_eq ((fullCurrent f p).continuous.comp continuous_fst) continuous_snd
  · rintro ⟨x,y⟩ (same : fullCurrent f p x=y)
    subst y
    have h:=image_closure_subset_closure_image
      (continuous_id.prodMk (fullCurrent f p).continuous) (s:=Set.range localCoreMap)
    apply closure_mono _ (h ⟨x,localCoreMap_dense x,rfl⟩)
    rintro _ ⟨_,⟨test,rfl⟩,rfl⟩
    exact ⟨test,Prod.ext rfl (fullCurrent_core f p test).symm⟩

theorem original_two_current_core (f g : Field289) (p q : PhysicalMomentum) (test : QuantumTest) :
    current f p (current g q (localCoreMap test))=
      localCoreMap (familyCore f p (familyCore g q test)) := by
  rw [current_core,current_core]

end LowEnergy.PreparationVacuumPreparedCurrent
