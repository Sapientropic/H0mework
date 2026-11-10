import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularSectorFourierReturn
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularWholeChart
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedOrderedStatic
open ActualDressedAngularSpherePrice ActualDressedAngularSectorFourier ActualDressedCorrectedElectronRead ActualDressedEMTensorClock ActualCompositeFieldCurrent
open Filter Set
open scoped Topology Matrix

def sourceDirectionSphere : Set PhysicalMomentum := {n | spatialSquare n=1}

private theorem sphere_coordinate (n : PhysicalMomentum) (unit : spatialSquare n=1) (j : Fin 3) : |n j|≤1 := by
  have single : (n j)^2≤∑k : Fin 3,(n k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (n k)) (Finset.mem_univ j)
  have value : (n j)^2≤ spatialSquare n := by simpa only [spatialSquare,Fin.sum_univ_three] using single
  rw [unit] at value
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (n j+1)],by nlinarith [sq_nonneg (n j-1)]⟩

theorem source_direction_sphere_compact : IsCompact sourceDirectionSphere := by
  have closed : IsClosed sourceDirectionSphere := by
    apply isClosed_eq (show Continuous spatialSquare from ?_) continuous_const
    unfold spatialSquare
    fun_prop
  apply (isCompact_closedBall (0 : PhysicalMomentum) 1).of_isClosed_subset closed
  intro n unit
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro j
  simpa only [Real.norm_eq_abs] using sphere_coordinate n unit j

theorem source_direction_sphere_nonempty : sourceDirectionSphere.Nonempty := by
  refine ⟨Pi.single 0 1,?_⟩
  norm_num [sourceDirectionSphere,spatialSquare,Pi.single_apply,Fin.ext_iff]

/-- The bound is generated from the actual leading polynomial on the complete physical direction sphere. -/
structure SourceWholeDirectionChart (event : DressedEvent) where
  eta : ℝ
  positive : 0<eta
  source_lower : ∀n : PhysicalMomentum,spatialSquare n=1→eta≤‖directionLeadingRead event n‖

def sourceWholeDirectionFloor (event : DressedEvent) : ℝ :=
  sInf ((fun n : PhysicalMomentum => ‖directionLeadingRead event n‖) '' sourceDirectionSphere)

theorem source_whole_floor_lower (event : DressedEvent) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    sourceWholeDirectionFloor event≤‖directionLeadingRead event n‖ := by
  have bounded : BddBelow ((fun k : PhysicalMomentum => ‖directionLeadingRead event k‖) '' sourceDirectionSphere) := by
    refine ⟨0,?_⟩
    rintro _ ⟨k,_,rfl⟩
    exact norm_nonneg _
  exact csInf_le bounded ⟨n,unit,rfl⟩

theorem source_whole_floor_positive (event : DressedEvent) (empty : ¬(sourceExceptionalDirections event).Nonempty) :
    0<sourceWholeDirectionFloor event := by
  have continuous := (direction_leading_continuous event).norm
  obtain ⟨n,unit,minimum⟩ := source_direction_sphere_compact.exists_isMinOn source_direction_sphere_nonempty continuous.continuousOn
  have nonzero : directionLeadingRead event n≠0 := fun zero => empty ⟨n,unit,zero⟩
  have least : IsLeast ((fun k : PhysicalMomentum => ‖directionLeadingRead event k‖) '' sourceDirectionSphere)
      ‖directionLeadingRead event n‖ := by
    refine ⟨⟨n,unit,rfl⟩,?_⟩
    rintro _ ⟨k,unitK,rfl⟩
    exact minimum unitK
  rw [sourceWholeDirectionFloor,least.csInf_eq]
  exact norm_pos_iff.mpr nonzero

private def whole_chart_generated (event : DressedEvent) (empty : ¬(sourceExceptionalDirections event).Nonempty) :
    SourceWholeDirectionChart event :=
  ⟨sourceWholeDirectionFloor event,source_whole_floor_positive event empty,source_whole_floor_lower event⟩

inductive WholeDirectionDisposition (event : DressedEvent) : Type
  | exceptional (actual_zero_set_nonempty : (sourceExceptionalDirections event).Nonempty)
  | whole (source_chart : SourceWholeDirectionChart event)

/-- The source zero set chooses the branch; the complete-sphere chart has no caller inverse or normalizer premise. -/
def sourceWholeDirectionDisposition (event : DressedEvent) : WholeDirectionDisposition event := by
  classical
  by_cases exceptional : (sourceExceptionalDirections event).Nonempty
  · exact .exceptional exceptional
  · exact .whole (whole_chart_generated event exceptional)

theorem whole_source_chart_membership (event : DressedEvent) (chart : SourceWholeDirectionChart event)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) : n∈sourceDirectionChart event chart.eta :=
  ⟨unit,chart.source_lower n unit⟩

theorem actual_whole_direction_response_return (event : DressedEvent) (chart : SourceWholeDirectionChart event)
    (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (clock : DirectionClockFinite event pd ps dL dR sL sR) (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    ∀n : PhysicalMomentum,spatialSquare n=1→∀eps : ℝ,eps≠0→|eps|<sourceDirectionRadius event chart.eta→
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n)) ∧
    Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockProbeRead event eps n pd ps dL dR sL sR)) ∧
    (∀mu nu,‖-(eps : ℂ)^4*zeroClockEMRead event eps n mu nu‖≤
      sourceAngularReadPrice event (directionZeroClockEM event mu nu) chart.eta) ∧
    ‖-(eps : ℂ)^4*zeroClockProbeRead event eps n pd ps dL dR sL sR‖≤
      sourceAngularReadPrice event (directionZeroClockProbe event pd ps dL dR sL sR) chart.eta :=
  fun n unit eps away small => actual_direction_finite_chart_return event pd ps dL dR sL sR clock spatial
    chart.eta chart.positive n (whole_source_chart_membership event chart n unit) eps away small

end LowEnergy.GaussComposite.ActualDressedAngularWholeChart
