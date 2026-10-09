import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourcePreparation

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSourceResponse
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussComposite.SourceGraph Electromagnetic.Identification
open CanonicalGradedCurrent GaussQuantumMultiplier CanonicalGradedSpatialSource GaussDensityCore
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open GaussUnitaryHistory (Index)
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open PreparationPhysicalDressedSpinChargeReturn
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMDressedCharacter
open scoped BigOperators ContDiff InnerProductSpace Matrix
open PhysicalEMDressedPreparedRead PreparationVacuumSourcePreparedState
open CanonicalScalarPreparation PreparationChartGuard PreparationScalarCoordinates PreparationCoordinates CanonicalPreparationCutoff PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open MeasureTheory Filter Set GaussHistoryHilbert GaussHalfDensity

open ActualDressedSourcePreparation PreparationVacuumMixedFieldReturn
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition sourceProfile finiteFull

/-- The actual unit excitation is propagated by the original fullY finite inverse. -/
def sourceDressedResponse (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) : H :=
  finiteFull p F cut z (sourceDressedUnit epsilon precision)

theorem source_dressed_response_equation (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) :
    (CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff cut-z • 1)
      (sourceDressedResponse epsilon precision p F cut z)=sourceDressedUnit epsilon precision := by
  have h:=congrArg (fun A : H→L[ℂ]H=>A (sourceDressedUnit epsilon precision)) (finiteFull_right p F cut z nonreal)
  exact h

theorem source_dressed_response_nonzero (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) :
    sourceDressedResponse epsilon precision p F cut z≠0 := by
  intro zero
  have h:=source_dressed_response_equation epsilon precision p F cut z nonreal
  rw [zero,map_zero] at h
  have unit:=source_dressed_unit_norm epsilon precision
  rw [←h,norm_zero] at unit
  exact zero_ne_one unit

/-- The genuine current of the actual unit excitation; this is distinct from the two-leg joint variation. -/
def sourceDressedCurrent (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) : Fin 289→ℂ :=
  fun i=>inner ℂ (sourceDressedUnit epsilon precision)
    (currentVertex (fieldBasis i) p k F cut z w (sourceDressedUnit epsilon precision))

theorem source_dressed_current_original (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) :
    sourceDressedCurrent epsilon precision p k F cut z w=
      sourceCovector p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (sourceDressedUnit epsilon precision)))
        (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut w)) := by
  funext i
  exact currentVertex_original_pair (fieldBasis i) p k F cut z w _ _

/-- The complete original action first variation consumes the same propagated actual unit endpoints in every field slot. -/
theorem source_dressed_action_current (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (f : Field289) :
    HasDerivAt
      (fieldForm f p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (sourceDressedUnit epsilon precision)))
        (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut w)))
      (∑i : Fin 289,(f i:ℂ)*sourceDressedCurrent epsilon precision p k F cut z w i) 0 := by
  rw [source_dressed_current_original]
  exact sourceCovector_derivative f p _ _

/-- Scalar, complement and density contact of the same actual event is retained independently. -/
theorem source_dressed_contact_original (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (f : Field289) :
    inner ℂ (sourceDressedUnit epsilon precision)
      (contactVertex f p k F cut z w (sourceDressedUnit epsilon precision))=
      (fieldJets f p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (sourceDressedUnit epsilon precision)))
        (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut w))).second := by
  exact contactVertex_original_pair f p k F cut z w _ _

private theorem completed_creation_native_charge (f : Profile) :
    CanonicalGradedCharge.chargeReader nativeY (completedLeg true 1 0 f)=
      (-2:ℂ) • completedLeg true 1 0 f := by
  refine core_dense.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [completedLeg_core]
  change CanonicalGradedCharge.chargeReader nativeY (creationSource 1 0 (seedSection g))=_
  rw [←embed_creation_test,CanonicalGradedCharge.chargeReader_core,
    created_core_charge 1 0 (seedSection g) g (fun _=>rfl),map_smul,embed_creation_test]
  rfl

private theorem completed_background_native_charge (f : Profile) :
    CanonicalGradedCharge.chargeReader nativeY (prepared f)=-prepared f := by
  refine core_dense.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [prepared_core,CanonicalGradedCharge.chargeReader_core,
    source_section_charge (seedSection g) g (fun _=>rfl),map_neg]

theorem source_dressed_unit_native_charge (epsilon : ℝ) (precision : 0<epsilon) :
    CanonicalGradedCharge.chargeReader nativeY (sourceDressedUnit epsilon precision)=
      (-2:ℂ) • sourceDressedUnit epsilon precision := by
  rw [source_dressed_unit_original,sourceDressedAddition,map_smul,completed_creation_native_charge]
  exact smul_comm _ _ _

/-- The connected nativeY read subtracts the same original prepared background, with no change of source state or normalization. -/
theorem source_dressed_connected_native_charge (epsilon : ℝ) (precision : 0<epsilon) :
    inner ℂ (sourceDressedUnit epsilon precision)
        (CanonicalGradedCharge.chargeReader nativeY (sourceDressedUnit epsilon precision))-
      inner ℂ (prepared (sourceProfile epsilon precision))
        (CanonicalGradedCharge.chargeReader nativeY (prepared (sourceProfile epsilon precision)))=-1 := by
  have background : ‖prepared (sourceProfile epsilon precision)‖=1 := by
    rw [sourceProfile]
    exact (sourceCausalState epsilon precision).unit
  rw [source_dressed_unit_native_charge,completed_background_native_charge,inner_smul_right,
    inner_neg_right,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,
    source_dressed_unit_norm,background]
  norm_num

/-- Full propagation retains its actual compression/cutoff Noether commutator. -/
theorem source_dressed_propagated_native_return (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) :
    CanonicalGradedCharge.chargeReader nativeY (sourceDressedResponse epsilon precision p F cut z)=
      (-2:ℂ) • sourceDressedResponse epsilon precision p F cut z+
        finiteFull p F cut z
          ((CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff cut-z • 1)
              (CanonicalGradedCharge.chargeReader nativeY (sourceDressedResponse epsilon precision p F cut z))-
            CanonicalGradedCharge.chargeReader nativeY
              ((CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff cut-z • 1)
                (sourceDressedResponse epsilon precision p F cut z))) := by
  let B:=CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff cut-z • 1
  let v:=sourceDressedResponse epsilon precision p F cut z
  let Q:=CanonicalGradedCharge.chargeReader nativeY
  have left : finiteFull p F cut z (B (Q v))=Q v :=
    congrArg (fun A : H→L[ℂ]H=>A (Q v)) (finiteFull_left p F cut z nonreal)
  have input : B v=sourceDressedUnit epsilon precision :=
    source_dressed_response_equation epsilon precision p F cut z nonreal
  change Q v=(-2:ℂ) • v+finiteFull p F cut z (B (Q v)-Q (B v))
  rw [map_sub,input,source_dressed_unit_native_charge,map_smul,left]
  change Q v=(-2:ℂ) • v+(Q v-(-2:ℂ) • v)
  abel

/-- The original joint scalar/matter EM variation and the connected nativeY increment use the same exterior normalization. -/
theorem source_dressed_joint_unit_ratio :
    (-Complex.I)*emDressedCharacter true=-(1/2:ℂ)*(-1) := by
  norm_num [emDressedCharacter,emDressedChargeUnit_value]
  ring_nf
  norm_num [Complex.I_sq]

/-- The current background is the same actual SourcePreparation occurrence. -/
def sourceDressedConnectedCurrent (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) : Fin 289→ℂ :=
  fun i=>sourceDressedCurrent epsilon precision p k F cut z w i-
    inner ℂ (prepared (sourceProfile epsilon precision))
      (currentVertex (fieldBasis i) p k F cut z w (prepared (sourceProfile epsilon precision)))

theorem source_dressed_connected_current_original (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) :
    sourceDressedConnectedCurrent epsilon precision p k F cut z w=
      sourceCovector p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (sourceDressedUnit epsilon precision)))
        (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut w))-
      sourceCovector p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (prepared (sourceProfile epsilon precision))))
        (sourceTestApprox F (finiteFull p F cut w (prepared (sourceProfile epsilon precision)))) := by
  funext i
  exact congrArg₂ (fun a b : ℂ=>a-b)
    (congrFun (source_dressed_current_original epsilon precision p k F cut z w) i)
    (currentVertex_original_pair (fieldBasis i) p k F cut z w
      (prepared (sourceProfile epsilon precision)) (prepared (sourceProfile epsilon precision)))

/-- Equal creation/annihilation types cancel only in the joint variation; this does not set the actual excitation current to zero. -/
theorem dressed_joint_variation_diagonal (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (addition : Bool) :
    emDressedPreparedCovector epsilon precision p k F cut z w addition addition 1 0 1 0=0 := by
  rw [em_dressed_prepared_return]
  funext i
  cases addition <;> simp [emDressedCharacter,emDressedChargeUnit_value,star_mul]
  all_goals left; ring

end LowEnergy.GaussComposite.ActualDressedSourceResponse
