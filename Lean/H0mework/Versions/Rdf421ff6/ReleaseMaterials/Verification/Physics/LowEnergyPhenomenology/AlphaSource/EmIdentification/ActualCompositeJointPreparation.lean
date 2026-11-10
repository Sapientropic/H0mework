import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeOriginWard
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeJointPreparation
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussQuantumMultiplier GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore GaussFockPair
open MixedSpectatorCandidate YukawaResolventDetection GaussCoreLabel
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse FullYSourceResolventGraphSplice
open SourceClockYukawaCubicCurrent GeneralThreeParticleResponse SourceScalarPairedTransport
open PreparationVacuumRawJointFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumSourceActionJets
open PreparationVacuumGaugeSourceInjection PreparationVacuumNonlinearFieldCurve PreparationVacuumOriginalGreenFeedback PreparationVacuumActualFieldQuantization
open PreparationVacuumStaticPoleResponse PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic
open ActualEMExternalRepresentation
open MeasureTheory Filter
open scoped Matrix BigOperators Topology InnerProductSpace Matrix.Norms.Operator
open ActualCompositeFieldCurrent ActualCompositeStaticCurrent
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumFullFieldRiesz
open GaussFockLabel NativeHistoryGrade NamedColorQtNext
open Set
open ActualCompositeGaugeBand PreparationPhysicalPhaseGaugeRealization
open GaussNativeMatter SourceQuantumResidualGaugeSlice GaussYukawaGrade GaussYukawaInteraction PreparationVacuumRestModeCoupling
open ActualCompositeChargeGrade CanonicalGradedCharge CanonicalPhysicalWardCore
open ActualEMOriginWard Stage9C.Material.SpinPair
open PreparationVacuumFullElectricWard PreparationVacuumActionDecomposition CanonicalPhysicalSpatial
open PreparationVacuumFieldConstraintResponse
open ActualCompositeOriginWard PreparationVacuumElectricConstraint
open GaussLiveMomentum GaussHalfDensity
attribute [local irreducible] compositeChargeCore compositeResponse compositeResolvent

private theorem profile_nonzero (dual : Bool) : compositeProfile dual≠0 := by
  intro zero
  have point:=congrArg (fun f : ScalarTest=>f sourcePoint.val) zero
  rw [composite_profile_source] at point
  simp only [zero_apply] at point
  exact one_ne_zero point

def preparedInput (dual : Bool) : QuantumTest :=
  ((‖embed (candidateTest dual (compositeProfile dual))‖:ℂ)⁻¹) • candidateTest dual (compositeProfile dual)

theorem prepared_input_norm (dual : Bool) : ‖embed (preparedInput dual)‖=1 := by
  have nz:=actual_candidate_test_nonzero dual (compositeProfile dual) (profile_nonzero dual)
  rw [preparedInput,map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr nz)]

/-- The existing source profile is retained exactly; only its actual norm generates the unit input. -/
theorem prepared_input_profile (dual : Bool) (z : SourceCoordinateSlice) :
    preparedInput dual z=
      (((‖embed (candidateTest dual (compositeProfile dual))‖:ℂ)⁻¹)*compositeProfile dual z) • candidate dual := by
  change ((‖embed (candidateTest dual (compositeProfile dual))‖:ℂ)⁻¹) •
    (compositeProfile dual z • candidate dual)=_
  rw [smul_smul]

/-- The full scalar+gauge source orbit is vertical in the original source slice; no profile neutrality premise is used. -/
theorem prepared_profile_orbit (dual : Bool) (z : physicalChart) :
    fderiv ℝ (compositeProfile dual) z.val (0,(inverseL z.val (orbitMap z.val sourcePhaseGaugeLie)).2)=0 := by
  have orbit : orbitMap z.val sourcePhaseGaugeLie=splitMap z.val (sourcePhaseGaugeLie,0) := by
    simp [splitMap,sliceMap]
  rw [orbit,inverse_left]
  change fderiv ℝ (compositeProfile dual) z.val 0=0
  exact map_zero _

/-- The same complete scalar/gauge orbit has zero horizontal derivative on this actual normalized full504 wave. -/
theorem prepared_wave_orbit (dual : Bool) (z : physicalChart) :
    fderiv ℝ (preparedInput dual) z.val (0,(inverseL z.val (orbitMap z.val sourcePhaseGaugeLie)).2)=0 := by
  have orbit : orbitMap z.val sourcePhaseGaugeLie=splitMap z.val (sourcePhaseGaugeLie,0) := by
    simp [splitMap,sliceMap]
  rw [orbit,inverse_left]
  change fderiv ℝ (preparedInput dual) z.val 0=0
  exact map_zero _

/-- Literal full504 matter Noether acts on the same actual unit preparation. -/
theorem prepared_input_noether (dual : Bool) :
    compositeChargeCore (preparedInput dual)=(if dual then (-1:ℂ) else 1) • preparedInput dual := by
  apply DFunLike.ext
  intro z
  unfold compositeChargeCore preparedInput
  change quantized PhysicalEMNativeChargeFull.emFullCharge
    (((‖embed (candidateTest dual (compositeProfile dual))‖:ℂ)⁻¹) • (compositeProfile dual z • candidate dual))=
      (if dual then (-1:ℂ) else 1) •
        (((‖embed (candidateTest dual (compositeProfile dual))‖:ℂ)⁻¹) • (compositeProfile dual z • candidate dual))
  rw [map_smul,map_smul,composite_em_charge_same,actual_candidate_phase_charge]
  module

/-- The same prepared unit vector is an eigenvector of the original completed source Noether reader. -/
theorem prepared_input_completed_charge (dual : Bool) :
    CanonicalGradedCharge.chargeReader sourcePhaseGaugeLie (embed (preparedInput dual))=
      (if dual then (-1:ℂ) else 1) • embed (preparedInput dual) := by
  rw [CanonicalGradedCharge.chargeReader_core,←composite_charge_original,prepared_input_noether,map_smul]

/-- The actual complete covariant configuration orbit includes the original native compensator; it is not the sum defining the local Gauss constraint. -/
theorem prepared_input_covariant_orbit (dual : Bool) (z : physicalChart) :
    covariantMomentum (orbitMap z.val sourcePhaseGaugeLie) (preparedInput dual) z.val=
      -(if dual then (-1:ℂ) else 1) • preparedInput dual z.val := by
  rw [covariantMomentum_orbit]
  have charge:=congrArg (fun f : QuantumTest=>f z.val) (prepared_input_noether dual)
  rw [composite_charge_original,chargeAction_fock] at charge
  change Complex.I • nativeFock sourcePhaseGaugeLie (preparedInput dual z.val)=
    (if dual then (-1:ℂ) else 1) • preparedInput dual z.val at charge
  calc
    _= -(Complex.I • nativeFock sourcePhaseGaugeLie (preparedInput dual z.val)) := by rw [neg_smul]
    _=_ := by rw [charge,neg_smul]

/-- Both original orbit pieces and the matter term are retained in their exact local Gauss balance. -/
theorem prepared_input_local_gauss (dual : Bool) :
    electricOrbitAction sourcePhaseGaugeLie (preparedInput dual)+
      scalarOrbitAction sourcePhaseGaugeLie (preparedInput dual)+
      (if dual then (-1:ℂ) else 1) • preparedInput dual=0 := by
  rw [←prepared_input_noether,composite_charge_original]
  exact electric_scalar_charge_balance sourcePhaseGaugeLie (preparedInput dual)

/-- The complete original Jacobian/Number-three half-density acts on this same source-generated preparation. -/
theorem prepared_input_half_density (dual : Bool) :
    fockHalfDensityEquiv (embed (preparedInput dual))=
      ((‖embed (candidateTest dual (compositeProfile dual))‖:ℂ)⁻¹) •
        WithLp.toLp 2 (fun word : Occupation=>candidate dual word • halfDensityEquiv 3 (scalarLp 3 (compositeProfile dual))) := by
  rw [preparedInput,map_smul,map_smul,actual_candidate_half_density]

theorem prepared_input_flat_norm (dual : Bool) :
    ‖fockHalfDensityEquiv (embed (preparedInput dual))‖=1 := by
  rw [LinearIsometryEquiv.norm_map,prepared_input_norm]

private theorem response_from_resolvent (leg : CompositeLeg) :
    compositeResolvent leg (compositeInput leg)=compositeResponse leg := by
  cases hs : leg.sharp <;>
    simp only [compositeResolvent,compositeResponse,hs,Bool.false_eq_true,if_false,if_true]

/-- The same prepared input reaches its original fullY/independent-sharp response; no profile or state replacement occurs. -/
theorem prepared_input_propagates (leg : CompositeLeg) :
    compositeResolvent leg (preparedInput leg.dual)=
      ((‖embed (compositeInput leg)‖:ℂ)⁻¹) • compositeResponse leg := by
  have input : candidateTest leg.dual (compositeProfile leg.dual)=compositeInput leg := rfl
  rw [preparedInput,input,map_smul,response_from_resolvent]

/-- The complete dynamic unit endpoint is generated from the same actual unit preparation with its actual source response norm. -/
theorem prepared_response_unit (leg : CompositeLeg) :
    compositeUnitLeg leg=
      ((‖embed (compositeInput leg)‖:ℂ)/(‖embed (compositeResponse leg)‖:ℂ)) •
        compositeResolvent leg (preparedInput leg.dual) := by
  have nz : (‖embed (compositeInput leg)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (actual_candidate_test_nonzero leg.dual (compositeProfile leg.dual) (profile_nonzero leg.dual)))
  rw [prepared_input_propagates,compositeUnitLeg,smul_smul]
  congr 1
  field_simp

/-- The original full289 current consumes those same prepared inputs after their original full response and normalization. -/
theorem prepared_current_generated (p : PhysicalMomentum) (left right : CompositeLeg) (i : Fin 289) :
    ActualCompositeFieldCurrent.compositeCurrent p left right i=
      -rawForm (fieldUnit i) p
        (((‖embed (compositeInput left)‖:ℂ)/(‖embed (compositeResponse left)‖:ℂ)) •
          compositeResolvent left (preparedInput left.dual))
        (((‖embed (compositeInput right)‖:ℂ)/(‖embed (compositeResponse right)‖:ℂ)) •
          compositeResolvent right (preparedInput right.dual)) 0 := by
  rw [ActualCompositeFieldCurrent.compositeCurrent,prepared_response_unit,prepared_response_unit]

end LowEnergy.GaussComposite.ActualCompositeJointPreparation
