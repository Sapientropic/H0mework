import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightNoether

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussQuantumMultiplier SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussCoreDifferential SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceActionJets PreparationVacuumHalfDensityFiber
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumNoetherChart CanonicalGradedSpatialSource
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] sourceRestLightMap sourceRestRemainderMap noetherReader noetherReaderContact
  projectedNoetherForm projectedNoetherContactForm frameVector frameTest finiteRiesz

theorem source_rest_noether_fiber_partition (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) :
    projectedNoetherFiber sourceRestLightMap reader p u+projectedNoetherFiber sourceRestRemainderMap reader p u=
      noetherFiber reader p u := by
  unfold projectedNoetherFiber noetherFiber
  rw [←map_add,source_rest_light_remainder]

/-- This decomposition retains the actual source configuration in the current before integrating it. -/
theorem source_rest_noether_form_partition (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (small : ‖h‖<ambientRadius a) :
    projectedNoetherForm sourceRestLightMap reader p a b h+
      projectedNoetherForm sourceRestRemainderMap reader p a b h=noetherForm reader p a b h := by
  have light:=projected_noether_form_integrable sourceRestLightMap reader p a b h small
  have remainder:=projected_noether_form_integrable sourceRestRemainderMap reader p a b h small
  unfold projectedNoetherForm
  change (∫z,pairSample z (a z) (projectedNoetherFiber sourceRestLightMap reader p (h,z) (b z)) ∂GaussHistoryHilbert.configurationMeasure)+
    (∫z,pairSample z (a z) (projectedNoetherFiber sourceRestRemainderMap reader p (h,z) (b z)) ∂GaussHistoryHilbert.configurationMeasure)=_
  rw [←integral_add light remainder]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change pairSample z (a z) _+pairSample z (a z) _=pairSample z (a z) _
  rw [←pairSample_add_right,←add_apply,source_rest_noether_fiber_partition]

/-- The generated split is differentiated through the original compact configuration integral. -/
theorem source_rest_noether_contact_form_partition (reader force : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) :
    projectedNoetherContactForm sourceRestLightMap reader force p a b+
      projectedNoetherContactForm sourceRestRemainderMap reader force p a b=noetherContactForm reader force p a b := by
  have generated:=(projected_noether_form_generated sourceRestLightMap reader force p a b).add
    (projected_noether_form_generated sourceRestRemainderMap reader force p a b)
  have ray : Continuous (fun r : ℝ=>r • force):=continuous_id.smul continuous_const
  have near : ∀ᶠr : ℝ in 𝓝 0,‖r • force‖<ambientRadius a := by
    exact (isOpen_lt (continuous_norm.comp ray) continuous_const).mem_nhds
      (by simpa using ambientRadius_positive a)
  have same : (fun r : ℝ=>noetherForm reader p a b (r • force))=ᶠ[𝓝 0]
      fun r : ℝ=>projectedNoetherForm sourceRestLightMap reader p a b (r • force)+
        projectedNoetherForm sourceRestRemainderMap reader p a b (r • force) := by
    filter_upwards [near] with r small
    exact (source_rest_noether_form_partition reader p a b (r • force) small).symm
  exact (generated.congr_of_eventuallyEq same).unique (noetherForm_generated reader force p a b)

private theorem circuit_riesz_add (F : GaussUnitaryHistory.Index)
    (a b : FrameIndex F→FrameIndex F→ℂ) :
    finiteRiesz F a+finiteRiesz F b=finiteRiesz F (fun i j=>a i j+b i j) := by
  simp only [finiteRiesz,add_smul,Finset.sum_add_distrib]

/-- The original finite frame is unchanged; only its complete material current has been split. -/
theorem source_rest_noether_reader_partition (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceLightNoetherReader reader p F 0+sourceRemainderNoetherReader reader p F 0=noetherReader reader p F 0 := by
  unfold sourceLightNoetherReader sourceRemainderNoetherReader projectedNoetherReader noetherReader
  rw [circuit_riesz_add]
  apply congrArg (finiteRiesz F)
  funext i j
  exact source_rest_noether_form_partition reader p (frameTest F i) (frameTest F j) 0
    (by simpa using ambientRadius_positive (frameTest F i))

/-- The true full Noether contact partitions on the same original event frame. -/
theorem source_rest_noether_reader_contact_partition (reader force : Field289)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceLightNoetherReaderContact reader force p F+sourceRemainderNoetherReaderContact reader force p F=
      noetherReaderContact reader force p F := by
  rw [noetherReaderContact_source]
  unfold sourceLightNoetherReaderContact sourceRemainderNoetherReaderContact projectedNoetherReaderContact
  rw [circuit_riesz_add]
  apply congrArg (finiteRiesz F)
  funext i j
  exact source_rest_noether_contact_form_partition reader force p (frameTest F i) (frameTest F j)

end LowEnergy.GaussComposite.ActualSourceLightCircuit
