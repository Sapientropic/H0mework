import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMDressedPreparedRead
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationLocalCurrentCarrier

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCreationSupport
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
attribute [local instance] SourceRealScalarFock.branchOrder


theorem unused_color_seed_coordinate : CanonicalCompletedSector.seedCoordinates (mode 0 2)=0 := by
  change (su7ExteriorBasis 2).repr
    ((Stage10.ChargedPreparation.CanonicalParticle.normalizedPreparation 0
      (Stage9DEF.Compatibility.embed (Stage9DEF.Source.vector 0))) 0).2.1
    (Composite.matterBasis 2)=0
  rw [Stage10.ChargedPreparation.CanonicalParticle.normalized_source]
  have d0 : Composite.matterBasis 2≠sourceColorDoubletIndex 0 := by decide
  have d1 : Composite.matterBasis 2≠sourceColorDoubletIndex 1 := by decide
  simp [Stage9DEF.Compatibility.embed,sourceColorDiracMatter,sourceColorDoubletMatter,
    Fin.sum_univ_two,d0,d1]

theorem unused_color_seed_annihilator :
    GaussCARHistory.annihilateFiber (mode 0 2) CanonicalCompletedSector.seed=0 := by
  apply fiberCoordinates.injective
  change QuantizationCheck.Fermion.annihilate (mode 0 2)
    (QuantizationCheck.Fermion.oneParticle CanonicalCompletedSector.seedCoordinates)=0
  rw [QuantizationCheck.Fermion.annihilate_oneParticle,unused_color_seed_coordinate]
  funext word
  change 0*QuantizationCheck.Fermion.vacuum word=0
  exact zero_mul _

theorem original_creation_seed_extract (phi : SourceQuantumScalarChart.Scalar) :
    GaussCARHistory.annihilateFiber (mode 0 2)
      (fiberCreation 1 0 phi CanonicalCompletedSector.seed)=
      star (scalarCoefficient 1 2 phi) • CanonicalCompletedSector.seed := by
  simp only [fiberCreation,sum_apply,smul_apply,map_sum,map_smul]
  have each (c : Fin 3) : GaussCARHistory.annihilateFiber (mode 0 2)
      (GaussCARHistory.createFiber (mode 0 c) CanonicalCompletedSector.seed)=
      if c=2 then CanonicalCompletedSector.seed else 0 := by
    have h:=congrArg (fun A : FiberOp=>A CanonicalCompletedSector.seed)
      (GaussCARHistory.fiber_car (mode 0 2) (mode 0 c))
    simp only [add_apply,mul_apply_eq_comp,unused_color_seed_annihilator,map_zero,add_zero] at h
    simp only [mode_equal,true_and] at h
    by_cases same : c=2
    · subst c
      simpa only [ite_true,one_apply_eq_self] using h
    · simpa only [true_and,if_neg (Ne.symm same),zero_apply,if_neg same] using h
  simp only [each,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]

private theorem weighted_seed (f : ScalarTest) (z : physicalChart) :
    weightedValue (seedSection f) z=
      ((halfDensity 1 z:ℂ)*f z.val) • CanonicalCompletedSector.seed := by
  apply PiLp.ext
  intro word
  change (halfDensity word.card z:ℂ)*(f z.val*CanonicalCompletedSector.seed word)=
    ((halfDensity 1 z:ℂ)*f z.val)*CanonicalCompletedSector.seed word
  by_cases card : word.card=1
  · rw [card]
    ring
  · rw [seed_zero_off_one word card]
    simp

theorem original_creation_core_extract (f : ScalarTest) :
    GaussCARHistory.annihilate (mode 0 2) (creationSource 1 0 (preparedCore f))=
      embed (scalarMultiplier (fun z=>star (coefficient 1 2 z))
        ((RCLike.conjCLE : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.contDiff.comp (coefficient_smooth 1 2))
        (preparedCore f)) := by
  apply fockHalfDensityEquiv.injective
  rw [GaussCARHistory.annihilate,GaussFockLift.lift_apply,LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro word
  apply Lp.ext_iff.mpr
  change ∀ᵐ z ∂GaussHistoryHilbert.chartMeasure,
    (flatLift (GaussCARHistory.annihilateFiber (mode 0 2))
      (fockHalfDensityEquiv (creationSource 1 0 (preparedCore f)))) word z=_
  filter_upwards [flat_lift_value (GaussCARHistory.annihilateFiber (mode 0 2))
      (fockHalfDensityEquiv (creationSource 1 0 (preparedCore f))),
    creation_source_value 1 0 (preparedCore f),
    flat_embed_value (scalarMultiplier (fun z=>star (coefficient 1 2 z))
      ((RCLike.conjCLE : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.contDiff.comp (coefficient_smooth 1 2))
      (preparedCore f))] with z ha hc he
  change (flatValue (flatLift (GaussCARHistory.annihilateFiber (mode 0 2))
    (fockHalfDensityEquiv (creationSource 1 0 (preparedCore f)))) z) word=
    (flatValue (fockHalfDensityEquiv (embed (scalarMultiplier (fun z=>star (coefficient 1 2 z))
      ((RCLike.conjCLE : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.contDiff.comp (coefficient_smooth 1 2))
      (preparedCore f)))) z) word
  rw [ha,hc,he,weighted_scalar_value]
  change (GaussCARHistory.annihilateFiber (mode 0 2)
    (fiberCreation 1 0 (GaussNativePotential.scalarField z)
      (weightedValue (seedSection _) z))) word=_
  rw [weighted_seed,map_smul,map_smul,original_creation_seed_extract]
  change _=(star (coefficient 1 2 z.val) •
    weightedValue (seedSection ((CanonicalPreparationCore.numberRaiseCore.comp
      PreparationVacuumWeylDomain.sourceVacuumInputCore) f)) z) word
  rw [weighted_seed,smul_comm]
  rfl

end LowEnergy.GaussComposite.ActualDressedCreationSupport
