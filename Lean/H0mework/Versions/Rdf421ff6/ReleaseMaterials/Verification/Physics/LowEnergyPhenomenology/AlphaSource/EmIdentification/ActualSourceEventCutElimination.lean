import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3CausalResponseWindow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceEMEventFeed
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert PreparationVacuumMixedFieldReturn
open PreparationVacuumSourcePreparedResponse PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumActionFieldLift
open PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard
open ActualCompositeFieldCurrent ActualElectronPhysicalJointInverse
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedIRReturn
open ActualElectronWholeNoetherObserver PhysicalN3CausalWindow
open Filter Set
open scoped Topology InnerProductSpace
attribute [local irreducible] jointResolvent jointCurrent physicalTime timeSlope
  noetherReader noetherReaderContact noetherStaticHalf
  actualElectronPhysicalState actualNoetherBackground actualHistoryReader

/-- The full-Y kinematic mouth has already removed the finite Yukawa cutoff. -/
theorem actual_cut_free_kinematics (event : DressedEvent) (cut : ℕ) (transfer : PhysicalMomentum) :
    dressedKinematicPoint {event with cut:=cut} transfer=dressedKinematicPoint event transfer := rfl

theorem actual_cut_free_observer (event : DressedEvent) (cut : ℕ) :
    dressedEulerObserver {event with cut:=cut}=dressedEulerObserver event := rfl

/-- Every original static entry is unchanged, at every transfer and every complex damping. -/
theorem actual_cut_free_static (event : DressedEvent) (cut : ℕ) (transfer : PhysicalMomentum) (lambda : ℂ) :
    dressedStaticPolarization {event with cut:=cut} transfer lambda=dressedStaticPolarization event transfer lambda := by
  funext i j
  change dressedEulerObserver {event with cut:=cut}
      (noetherStaticHalf (dressedKinematicPoint {event with cut:=cut} transfer) (fieldUnit i) (fieldUnit j) lambda)=
    dressedEulerObserver event (noetherStaticHalf (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j) lambda)
  exact (congrArg (fun observer=>observer
    (noetherStaticHalf (dressedKinematicPoint {event with cut:=cut} transfer) (fieldUnit i) (fieldUnit j) lambda))
      (actual_cut_free_observer event cut)).trans
    (congrArg (fun point=>dressedEulerObserver event (noetherStaticHalf point (fieldUnit i) (fieldUnit j) lambda))
      (actual_cut_free_kinematics event cut transfer))

private theorem actual_cut_free_variation (event : DressedEvent) (cut : ℕ)
    (transfer : PhysicalMomentum) (reader force : Field289) (age : ℝ) :
    actualFullNoetherVariation {event with cut:=cut} transfer reader force age=
      actualFullNoetherVariation event transfer reader force age := rfl

private theorem actual_cut_free_background (event : DressedEvent) (cut : ℕ) :
    actualNoetherBackground {event with cut:=cut}=actualNoetherBackground event := by
  unfold actualNoetherBackground
  rfl

private theorem actual_cut_free_physical_observer (event : DressedEvent) (cut : ℕ) (leg : CompositeLeg) :
    actualPhysicalEulerObserver {event with cut:=cut} leg=actualPhysicalEulerObserver event leg := by
  apply ContinuousLinearMap.ext
  intro A
  have first:=actual_physical_euler_observer_value {event with cut:=cut} leg A
  have second:=actual_physical_euler_observer_value event leg A
  exact first.trans ((congrArg (fun background=>
    -inner ℂ (actualElectronPhysicalState event.momentum event.energy event.nonreal leg)
      (GaussUnitaryHistory.reader A (actualElectronPhysicalState event.momentum event.energy event.nonreal leg))+
      inner ℂ background (GaussUnitaryHistory.reader A background))
    (actual_cut_free_background event cut)).trans second.symm)

/-- The unchanged physical N3 state and source background consume the full five-leg causal window. -/
theorem actual_cut_free_physical_n3_window (event : DressedEvent) (cut : ℕ) (leg : CompositeLeg)
    (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    physicalN3ResponseWindow {event with cut:=cut} leg transfer lambda T reader force=
      physicalN3ResponseWindow event leg transfer lambda T reader force := by
  unfold physicalN3ResponseWindow physicalN3ResponseWindowOperator
  simp only [actual_cut_free_physical_observer,actual_cut_free_variation]

/-- One source-generated IR limit serves all old finite-cut labels of the same actual full response. -/
theorem actual_cut_free_sixth_ir_return (event : DressedEvent) :
    ∃L : Matrix (Fin 289) (Fin 289) ℂ,∀cut : ℕ,
      Tendsto (fun z : ℂ=>z^6 • dressedStaticPolarization {event with cut:=cut} 0 z)
        (nhdsWithin 0 {z : ℂ|0<z.re}) (𝓝 L) := by
  obtain ⟨L,limit⟩:=actual_sixth_ir_return event
  exact ⟨L,fun cut=>by simpa only [actual_cut_free_static] using limit⟩

end LowEnergy.GaussComposite.ActualSourceEMEventFeed
