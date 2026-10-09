import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceBackgroundLockedDirection
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.SourceLockedFieldReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginFields

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMSourceDirection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineDynamicBreakingVacuum
open StageNineHolonomicField Stage9C.Material.SpinPair DiracExteriorMatterAction DiracCliffordRepresentation
open SourceQuantumScalarChart SourceQuantumResidualGaugeSlice SourceQuantumScalarOrbitDimensions
open PreparationVacuumPhysicalElectromagneticDirection PreparationPhysicalElectromagneticDirectionReturn
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily PreparationVacuumNativeFieldInjection
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationCoordinates
open PhysicalEMGaugeRealization ActualEMCompleteOrbit
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open scoped Matrix BigOperators

/-- The three original scalar-stabilizer current tests retain their Lorentz connections in all289 slots. -/
def lockedInput (mu : Fin 4) : Matrix (Fin 289) (Fin 3) ℂ :=
  fun j i=>(sourceLockedField mu i j:ℂ)

def lockedAmplitude (mu : Fin 4) (n : Fin 3→ℝ) : Fin 289→ℂ :=
  lockedInput mu*ᵥ(fun i=>(n i:ℂ))

private theorem spinSlot_injective : Function.Injective sourceSpinSlot := by
  intro i j same
  apply Fin.ext
  have value:=congrArg Fin.val same
  simp only [sourceSpinSlot] at value
  omega

/-- Every independent source parameter is read back from its actual Lorentz current slot. -/
theorem locked_amplitude_lorentz_read (mu : Fin 4) (n : Fin 3→ℝ) (i : Fin 3) :
    lockedAmplitude mu n (lorentzSlot mu (sourceSpinSlot i))=(n i:ℂ) := by
  have slot (j : Fin 3) : sourceLockedField mu j (lorentzSlot mu (sourceSpinSlot i))=
      if j=i then 1 else 0 := by
    have original:=sourceLockedField_lorentz mu mu j (sourceSpinSlot i)
    simpa only [fieldLorentz,eq_self, true_and,spinSlot_injective.eq_iff,eq_comm] using original
  simp [lockedAmplitude,lockedInput,Matrix.mulVec,dotProduct,slot,apply_ite]

theorem locked_amplitude_nonzero (mu : Fin 4) (n : Fin 3→ℝ) (nonzero : n≠0) : lockedAmplitude mu n≠0 := by
  intro zero
  apply nonzero
  funext i
  have read:=congrFun zero (lorentzSlot mu (sourceSpinSlot i))
  rw [locked_amplitude_lorentz_read] at read
  exact Complex.ofReal_injective read

/-- The entire scalar kernel is source generated; its actual gauge orbit is retained separately. -/
theorem scalar_stabilizer_complete (a : NativeLie) (fixed : orbit a=0) :
    ∃n : Fin 3→ℝ,sourceBackgroundColor n=a ∧ orbit (sourceBackgroundColor n)=0 := by
  refine ⟨colorStabilizerEquiv.symm ⟨a,fixed⟩,sourceBackgroundColor_complete a fixed,?_⟩
  exact sourceBackgroundColor_scalar _

/-- Scalar stabilization and ordinary background parallelism remain two distinct original source conditions. -/
theorem scalar_background_parallel (a : stabilizer) : residualOrbit a=0 ↔ a=0 :=
  sourceScalar_gauge_fixed_direction a

/-- The same source parameter supplies color, spatial-index and Dirac-spin compensation, preserving both independent background matter endpoints. -/
theorem locked_actual_background (n : Fin 3→ℝ) (point : BasePoint) :
    orbit (sourceBackgroundColor n)=0 ∧
    (∀j : Fin 3,sourceBackgroundBracket (sourceBackgroundColor n) (gaugeCoordinates sourceGauge j)+
      ∑k : Fin 3,sourceBackgroundIndex n j k • gaugeCoordinates sourceGauge k=0) ∧
    sourceBackgroundMatterAction n (actual.matter point)=0 ∧
    (actual.conjugateMatter point).comp (sourceBackgroundMatterAction n)=0 ∧
    sourceBackgroundFrame n*actual.coframe point-actual.coframe point*sourceBackgroundFrame n=0 := by
  exact ⟨sourceBackgroundColor_scalar n,sourceBackgroundGauge_source n,sourceBackgroundMatter_source n point,
    sourceBackgroundDual_source n point,sourceBackgroundCoframe_source n point⟩

/-- The source's constitutive gauge auxiliary obeys that same compensated spatial action. -/
theorem locked_actual_auxiliary (n : Fin 3→ℝ) (point : BasePoint) (j : Fin 3) :
    sourceBackgroundBracket (sourceBackgroundColor n) (sourceBackgroundAuxiliary point ⟨j.val,by omega⟩)+
      ∑k : Fin 3,sourceBackgroundIndex n j k • sourceBackgroundAuxiliary point ⟨k.val,by omega⟩=0 :=
  sourceBackgroundAuxiliary_source n point j

/-- The literal E direction has this actual scalar action, independently of the locked family. -/
theorem literal_em_scalar_action :
    scalarCoordinateSquaredNorm (scalarMotherLieAction (p286LieBlockEmbed emDirection) (actual.scalar 0))=(1/2:ℝ) := by
  rw [←em_orbit_scalar_original]
  exact em_orbit_scalar_norm

/-- Background locking does not erase the actual charged triplet external current. -/
theorem locked_actual_charged_read : sourceRestLockedMixing 0 2 (0,1) (0,1)=(-1:ℂ) := by
  rw [sourceRestLockedCharge_generated]
  norm_num [sourceRestLockedChargeBlock,Matrix.cons_val_two]

end LowEnergy.GaussComposite.ActualEMSourceDirection
