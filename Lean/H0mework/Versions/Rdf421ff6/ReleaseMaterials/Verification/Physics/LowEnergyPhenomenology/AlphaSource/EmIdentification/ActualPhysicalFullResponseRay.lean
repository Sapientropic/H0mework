import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompleteJMixedTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronFullNoetherMixedSoft
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open ActualElectronWholeChargeSoft ActualElectronPhysicalJointInverse ActualElectronWholeNoetherObserver
open ActualDressedFullCoulomb ActualDressedNoether
open SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] actualPhysicalEulerObserver actualElectronPhysicalState actualNoetherBackground
  actualFullNoetherVariation mixedVertex actualCorrectedContact

private theorem fixed_ray_return {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace W] (f : P→W) (paid : Continuous f) (direction : P) :
    Tendsto (fun r : ℝ=>f (r • direction)) (𝓝 0) (𝓝 (f 0)) := by
  have curve : Continuous (fun r : ℝ=>r • direction):=continuous_id.smul (continuous_const (y:=direction))
  have shifted : Tendsto (fun r : ℝ=>r • direction) (𝓝 0) (𝓝 (0:P)):=by
    simpa only [zero_smul] using curve.tendsto (0:ℝ)
  exact paid.continuousAt.tendsto.comp shifted

private theorem prepared_observer_price {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (psi b : Hilbert E u) (psinorm : ‖psi‖=1) (bnorm : ‖b‖=1) (A : E→L[ℂ]E) :
    ‖-inner ℂ psi (lift u (constant A) psi)+inner ℂ b (lift u (constant A) b)‖≤2*‖A‖ := by
  have psiBound:=SourceBoundaryGram.lift_bound_explicit u (constant A) ‖A‖ (norm_nonneg A) (fun _ x=>A.le_opNorm x) psi
  have bBound:=SourceBoundaryGram.lift_bound_explicit u (constant A) ‖A‖ (norm_nonneg A) (fun _ x=>A.le_opNorm x) b
  calc
    _≤‖inner ℂ psi (lift u (constant A) psi)‖+‖inner ℂ b (lift u (constant A) b)‖ := by
      simpa only [norm_neg] using norm_add_le (-inner ℂ psi (lift u (constant A) psi)) (inner ℂ b (lift u (constant A) b))
    _≤‖psi‖*‖lift u (constant A) psi‖+‖b‖*‖lift u (constant A) b‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _≤‖psi‖*(‖A‖*‖psi‖)+‖b‖*(‖A‖*‖b‖) :=
      add_le_add (mul_le_mul_of_nonneg_left psiBound (norm_nonneg psi)) (mul_le_mul_of_nonneg_left bBound (norm_nonneg b))
    _=_ := by rw [psinorm,bnorm];ring

/-- The price uses the actual physical unit and the unchanged original normalized background. -/
theorem actual_physical_observer_operator_price (event : DressedEvent) (leg : CompositeLeg) (A : H→L[ℂ]H) :
    ‖actualPhysicalEulerObserver event leg A‖≤2*‖A‖ := by
  have observed:=actual_physical_euler_observer_value event leg A
  exact (congrArg norm observed).le.trans (prepared_observer_price GaussUnitaryHistory.sourceFilter
    (actualElectronPhysicalState event.momentum event.energy event.nonreal leg) (actualNoetherBackground event)
    (actual_electron_physical_state_norm event.momentum event.energy event.nonreal leg) (actual_noether_background_norm event) A)

/-- Complete Noether linear response at the actual fixed physical preparation, in all reader/force directions. -/
def actualPhysicalFullResponse (event : DressedEvent) (leg : CompositeLeg) (reader force : Field289) (age : ℝ)
    (k : PhysicalMomentum) : ℂ :=
  actualPhysicalEulerObserver event leg (actualFullNoetherVariation event (-k) reader force age)

def actualPhysicalMixedRead (event : DressedEvent) (leg : CompositeLeg) (reader force : Field289)
    (k : PhysicalMomentum) : ℂ :=
  actualPhysicalEulerObserver event leg (mixedVertex force reader event.momentum k event.frame event.energy event.energy)

def actualPhysicalContactRead (event : DressedEvent) (leg : CompositeLeg) (reader force : Field289) (age : ℝ)
    (k : PhysicalMomentum) : ℂ :=
  actualPhysicalEulerObserver event leg (actualCorrectedContact event (-k) reader force age)

theorem actual_physical_full_response_continuous (event : DressedEvent) (leg : CompositeLeg)
    (reader force : Field289) (age : ℝ) :Continuous (actualPhysicalFullResponse event leg reader force age) :=
  (actualPhysicalEulerObserver event leg).continuous.comp (actual_complete_J_transfer_continuous event reader force age)

theorem actual_physical_mixed_read_continuous (event : DressedEvent) (leg : CompositeLeg)
    (reader force : Field289) :Continuous (actualPhysicalMixedRead event leg reader force) :=
  (actualPhysicalEulerObserver event leg).continuous.comp (actual_original_mixed_transfer_continuous event.momentum event.frame
    event.energy event.energy event.nonreal force reader)

theorem actual_physical_contact_read_continuous (event : DressedEvent) (leg : CompositeLeg)
    (reader force : Field289) (age : ℝ) :Continuous (actualPhysicalContactRead event leg reader force age) :=
  (actualPhysicalEulerObserver event leg).continuous.comp (actual_corrected_contact_transfer_continuous event reader force age)

theorem actual_physical_full_response_difference_price (event : DressedEvent) (leg : CompositeLeg)
    (reader force : Field289) (age : ℝ) (k : PhysicalMomentum) :
    ‖actualPhysicalFullResponse event leg reader force age k-actualPhysicalFullResponse event leg reader force age 0‖≤
      2*‖actualFullNoetherVariation event (-k) reader force age-actualFullNoetherVariation event 0 reader force age‖ := by
  have identity : actualPhysicalEulerObserver event leg
      (actualFullNoetherVariation event (-k) reader force age-actualFullNoetherVariation event 0 reader force age)=
      actualPhysicalFullResponse event leg reader force age k-actualPhysicalFullResponse event leg reader force age 0 := by
    simpa only [actualPhysicalFullResponse,neg_zero] using!
      map_sub (actualPhysicalEulerObserver event leg) (actualFullNoetherVariation event (-k) reader force age)
        (actualFullNoetherVariation event 0 reader force age)
  exact (congrArg norm identity.symm).le.trans (actual_physical_observer_operator_price event leg _)

/-- This ordinary ray uses one transfer for every preparation frame; no adaptive k(F,m) is substituted. -/
theorem actual_physical_full_response_fixed_ray (event : DressedEvent) (leg : CompositeLeg)
    (reader force : Field289) (age : ℝ) (direction : PhysicalMomentum) :
    Tendsto (fun r : ℝ=>actualPhysicalFullResponse event leg reader force age (r • direction)) (𝓝 0)
      (𝓝 (actualPhysicalFullResponse event leg reader force age 0)) := by
  exact fixed_ray_return _ (actual_physical_full_response_continuous event leg reader force age) direction

theorem actual_physical_mixed_fixed_ray (event : DressedEvent) (leg : CompositeLeg)
    (reader force : Field289) (direction : PhysicalMomentum) :
    Tendsto (fun r : ℝ=>actualPhysicalMixedRead event leg reader force (r • direction)) (𝓝 0)
      (𝓝 (actualPhysicalMixedRead event leg reader force 0)) := by
  exact fixed_ray_return _ (actual_physical_mixed_read_continuous event leg reader force) direction

theorem actual_physical_contact_fixed_ray (event : DressedEvent) (leg : CompositeLeg)
    (reader force : Field289) (age : ℝ) (direction : PhysicalMomentum) :
    Tendsto (fun r : ℝ=>actualPhysicalContactRead event leg reader force age (r • direction)) (𝓝 0)
      (𝓝 (actualPhysicalContactRead event leg reader force age 0)) := by
  exact fixed_ray_return _ (actual_physical_contact_read_continuous event leg reader force age) direction

theorem actual_physical_ray_nonzero (direction : PhysicalMomentum) (nonzero : direction≠0) (r : ℝ) (off : r≠0) :
    r • direction≠0 := smul_ne_zero off nonzero

def actualPhysicalFullResponseMatrix (event : DressedEvent) (leg : CompositeLeg) (age : ℝ) (k : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=fun i j=>actualPhysicalFullResponse event leg (fieldUnit i) (fieldUnit j) age k

theorem actual_physical_full_response_matrix_continuous (event : DressedEvent) (leg : CompositeLeg) (age : ℝ) :
    Continuous (actualPhysicalFullResponseMatrix event leg age) :=
  continuous_pi fun i=>continuous_pi fun j=>actual_physical_full_response_continuous event leg (fieldUnit i) (fieldUnit j) age

theorem actual_physical_full_response_matrix_fixed_ray (event : DressedEvent) (leg : CompositeLeg)
    (age : ℝ) (direction : PhysicalMomentum) :
    Tendsto (fun r : ℝ=>actualPhysicalFullResponseMatrix event leg age (r • direction)) (𝓝 0)
      (𝓝 (actualPhysicalFullResponseMatrix event leg age 0)) := by
  exact fixed_ray_return _ (actual_physical_full_response_matrix_continuous event leg age) direction

end LowEnergy.GaussComposite.ActualElectronFullNoetherMixedSoft
