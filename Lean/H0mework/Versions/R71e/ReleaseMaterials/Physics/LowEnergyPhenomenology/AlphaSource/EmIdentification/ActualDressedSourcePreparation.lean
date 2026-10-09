import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMDressedPreparedRead
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationLocalCurrentCarrier
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCreationSupport

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSourcePreparation
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

theorem scalar_coefficient_coordinate (phi : SourceQuantumScalarChart.Scalar) :
    GaussComposite.scalarCoefficient 1 2 phi=phi (Composite.scalarBasis 1 2) := by
  simp [GaussComposite.scalarCoefficient,StageNineDynamicBreakingVacuum.scalarCoordinateEquiv]

theorem scalar_coefficient_bound (phi : SourceQuantumScalarChart.Scalar) :
    ‖GaussComposite.scalarCoefficient 1 2 phi‖≤‖phi‖ := by
  rw [scalar_coefficient_coordinate]
  exact PiLp.norm_apply_le phi _

theorem scalar_coefficient_vacuum :
    GaussComposite.scalarCoefficient 1 2 SourceQuantumScalarChart.vacuum=1 := by
  rw [scalar_coefficient_coordinate]
  simp only [SourceQuantumScalarChart.vacuum,
    StageNineDynamicBreakingVacuum.sourceGeneratedVacuumCoordinates,
    StageNineDynamicBreakingVacuum.positive_sourceGeneratedVacuumBase,
    SU7ExteriorYukawaMassSpectrum.finiteGenerationJointBreakingScalar,
    SU7ExteriorYukawaMassSpectrum.finiteGenerationBreakingTensor,map_sum,
    StageNineDynamicBreakingVacuum.scalarCoordinateEquiv,LinearEquiv.trans_apply,
    WithLp.linearEquiv_symm_apply,
    Module.Basis.repr_self]
  norm_num [Fin.sum_univ_two]
  have h00 : Composite.scalarBasis 1 2≠SU7ExteriorYukawaMassSpectrum.finiteGenerationScalarIndex 0 0 := by decide
  have h01 : Composite.scalarBasis 1 2≠SU7ExteriorYukawaMassSpectrum.finiteGenerationScalarIndex 0 1 := by decide
  have h10 : Composite.scalarBasis 1 2=SU7ExteriorYukawaMassSpectrum.finiteGenerationScalarIndex 1 0 := by decide
  have h11 : Composite.scalarBasis 1 2≠SU7ExteriorYukawaMassSpectrum.finiteGenerationScalarIndex 1 1 := by decide
  simp only [if_neg h00,if_neg h01,if_pos h10,if_neg h11,zero_add,add_zero]

theorem scalar_coefficient_lower (z : SourceCoordinateSlice)
    (box : fullCoordinates z∈sourceClosedBox) :
    (1/2:ℝ)≤‖GaussComposite.coefficient 1 2 z‖ := by
  have small:=scalar_box_norm (fullCoordinates z) box
  rw [ContinuousLinearEquiv.symm_apply_apply] at small
  have perturb:=scalar_coefficient_bound z.2.1.val
  have triangle:=norm_sub_le (GaussComposite.scalarCoefficient 1 2 SourceQuantumScalarChart.vacuum+
      GaussComposite.scalarCoefficient 1 2 z.2.1.val)
    (GaussComposite.scalarCoefficient 1 2 z.2.1.val)
  rw [add_sub_cancel_right,scalar_coefficient_vacuum,norm_one] at triangle
  have expanded : GaussComposite.coefficient 1 2 z=
      1+GaussComposite.scalarCoefficient 1 2 z.2.1.val := by
    change GaussComposite.scalarCoefficient 1 2 (SourceQuantumScalarChart.vacuum+z.2.1.val)=_
    rw [map_add,scalar_coefficient_vacuum]
  rw [←expanded] at triangle
  linarith [radius_small.2]


private theorem weighted_inner_integrable (f g : QuantumTest) :
    Integrable (fun z : physicalChart=>inner ℂ (weightedValue f z) (weightedValue g z)) GaussHistoryHilbert.chartMeasure := by
  exact (flat_value_inner_integrable (fockHalfDensityEquiv (embed f)) (fockHalfDensityEquiv (embed g))).congr (by
    filter_upwards [flat_embed_value f,flat_embed_value g] with z hf hg
    rw [hf,hg])

private theorem weighted_inner_integral (f g : QuantumTest) :
    inner ℂ (embed f) (embed g)=
      ∫ z : physicalChart,inner ℂ (weightedValue f z) (weightedValue g z) ∂GaussHistoryHilbert.chartMeasure := by
  rw [←fockHalfDensityEquiv.inner_map_map (embed f) (embed g),flat_inner_integral]
  apply integral_congr_ae
  filter_upwards [flat_embed_value f,flat_embed_value g] with z hf hg
  rw [hf,hg]

private theorem weighted_norm_integral (f : QuantumTest) :
    ‖embed f‖^2=∫ z : physicalChart, ‖weightedValue f z‖^2 ∂GaussHistoryHilbert.chartMeasure := by
  have h:=congrArg (RCLike.re : ℂ→ℝ) (weighted_inner_integral f f)
  rw [←integral_re (weighted_inner_integrable f f)] at h
  simpa only [inner_self_eq_norm_sq] using h

private theorem weighted_norm_integrable (f : QuantumTest) :
    Integrable (fun z : physicalChart=>‖weightedValue f z‖^2) GaussHistoryHilbert.chartMeasure := by
  simpa only [inner_self_eq_norm_sq] using (weighted_inner_integrable f f).re

theorem original_contact_lower (f : QuantumTest)
    (supported : tsupport f⊆fullCoordinates ⁻¹' sourceClosedBox) :
    ‖embed f‖^2≤4*(‖creationSource 1 0 f‖^2+‖annihilationSource 1 0 f‖^2) := by
  let g:=contactSource 1 0 1 0 f
  have point (z : physicalChart) : ‖weightedValue f z‖^2≤
      4*(inner ℂ (weightedValue f z) (weightedValue g z)).re := by
    by_cases active : z.val∈tsupport f
    · have lower:=scalar_coefficient_lower z.val (supported active)
      have term:=Finset.single_le_sum (s:=Finset.univ) (f:=fun c : Fin 3=>‖coefficient 1 c z.val‖^2)
        (fun c _=>sq_nonneg _) (Finset.mem_univ (2:Fin 3))
      change ‖weightedValue f z‖^2≤4*(inner ℂ (weightedValue f z)
        (weightedValue (scalarMultiplier (contactCoefficient 1 0 1 0) (contact_coefficient_smooth 1 0 1 0) f) z)).re
      rw [weighted_scalar_value,inner_smul_right,SourceGraph.gram_diagonal]
      change ‖weightedValue f z‖^2≤4*RCLike.re
        (((∑ c : Fin 3,‖coefficient 1 c z.val‖^2:ℝ):ℂ)*
          inner ℂ (weightedValue f z) (weightedValue f z))
      have realMul : RCLike.re
          (((∑ c : Fin 3,‖coefficient 1 c z.val‖^2:ℝ):ℂ)*
            inner ℂ (weightedValue f z) (weightedValue f z))=
          (∑ c : Fin 3,‖coefficient 1 c z.val‖^2)*RCLike.re
            (inner ℂ (weightedValue f z) (weightedValue f z)) := by
        exact RCLike.re_ofReal_mul _ _
      rw [realMul,inner_self_eq_norm_sq]
      have bound : 1≤4*(∑ c : Fin 3,‖coefficient 1 c z.val‖^2) := by nlinarith
      calc
        _=1*‖weightedValue f z‖^2 := by ring
        _≤(4*(∑ c : Fin 3,‖coefficient 1 c z.val‖^2))*‖weightedValue f z‖^2 :=
          mul_le_mul_of_nonneg_right bound (sq_nonneg _)
        _=_ := by ring
    · have zero : f z.val=0:=image_eq_zero_of_notMem_tsupport active
      have weighted : weightedValue f z=0 := by
        apply PiLp.ext
        intro word
        change (halfDensity word.card z:ℂ)*f z.val word=0
        rw [zero,PiLp.zero_apply,mul_zero]
      rw [weighted,norm_zero,zero_pow (by decide : 2≠0),inner_zero_left,Complex.zero_re,mul_zero]
  rw [weighted_norm_integral]
  have inequality:=integral_mono (weighted_norm_integrable f)
    ((weighted_inner_integrable f g).re.const_mul 4) point
  rw [integral_const_mul,integral_re (weighted_inner_integrable f g),←weighted_inner_integral] at inequality
  change _≤4*(GaussFockPair.sourcePair f (contactSource 1 0 1 0 f)).re at inequality
  rw [←source_contact_norm] at inequality
  exact inequality

/-- The original localized preparation, including its entire closed multiplier range, controls two actual CAR legs. -/
theorem localized_contact_lower (x : sourceLocalSpace) :
    ‖sourcePrepared x‖^2≤4*(‖sourceLeg true 1 0 x‖^2+‖sourceLeg false 1 0 x‖^2) := by
  refine localCore_dense.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [sourcePrepared_core,sourceLeg_core,sourceLeg_core,legTest_embed,legTest_embed]
  simp only [leg,if_true,Bool.false_eq_true,if_false]
  exact original_contact_lower (preparedCore f) (preparedCore_support f)

private theorem scalar_product_lower (f : QuantumTest)
    (supported : tsupport f⊆fullCoordinates ⁻¹' sourceClosedBox) :
    ‖embed f‖^2≤4*‖embed (scalarMultiplier (fun z=>star (coefficient 1 2 z))
      ((RCLike.conjCLE : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.contDiff.comp (coefficient_smooth 1 2)) f)‖^2 := by
  let g:=scalarMultiplier (fun z=>star (coefficient 1 2 z))
    ((RCLike.conjCLE : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.contDiff.comp (coefficient_smooth 1 2)) f
  have point (z : physicalChart) : ‖weightedValue f z‖^2≤4*‖weightedValue g z‖^2 := by
    change ‖weightedValue f z‖^2≤4*‖weightedValue
      (scalarMultiplier (fun z=>star (coefficient 1 2 z))
        ((RCLike.conjCLE : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.contDiff.comp (coefficient_smooth 1 2)) f) z‖^2
    rw [weighted_scalar_value,norm_smul,norm_star,mul_pow]
    by_cases active : z.val∈tsupport f
    · have lower:=scalar_coefficient_lower z.val (supported active)
      have bound : 1≤4*‖coefficient 1 2 z.val‖^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right bound (sq_nonneg ‖weightedValue f z‖)]
    · have zero : f z.val=0:=image_eq_zero_of_notMem_tsupport active
      have weighted : weightedValue f z=0 := by
        apply PiLp.ext
        intro word
        change (halfDensity word.card z:ℂ)*f z.val word=0
        rw [zero,PiLp.zero_apply,mul_zero]
      rw [weighted,norm_zero]
      norm_num
  rw [weighted_norm_integral]
  change _≤4*‖embed g‖^2
  rw [weighted_norm_integral,←integral_const_mul]
  exact integral_mono (weighted_norm_integrable f) ((weighted_norm_integrable g).const_mul 4) point

/-- The previously unused actual color2 mode extracts a nonzero component of the genuine creation leg. -/
theorem original_creation_lower (f : ScalarTest) :
    ‖embed (preparedCore f)‖^2≤4*‖creationSource 1 0 (preparedCore f)‖^2 := by
  have lower:=scalar_product_lower (preparedCore f) (preparedCore_support f)
  rw [←ActualDressedCreationSupport.original_creation_core_extract] at lower
  exact lower.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (GaussCARHistory.annihilate_bound (mode 0 2) _) 2) (by norm_num))

theorem localized_creation_lower (x : sourceLocalSpace) :
    ‖sourcePrepared x‖^2≤4*‖sourceLeg true 1 0 x‖^2 := by
  refine localCore_dense.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [sourcePrepared_core,sourceLeg_core,legTest_embed]
  exact original_creation_lower f

theorem actual_dressed_creation_nonzero (epsilon : ℝ) (precision : 0<epsilon) :
    emDressedCompleted true 1 0 (sourceProfile epsilon precision)≠0 := by
  have lower:=localized_creation_lower (sourcePreparation epsilon precision).point.val
  have unit : ‖sourcePrepared (sourcePreparation epsilon precision).point.val‖=1 :=
    (sourcePreparation epsilon precision).unit
  rw [unit] at lower
  intro zero
  have character : emDressedCharacter true≠0 := by
    norm_num [emDressedCharacter,emDressedChargeUnit_value]
  rw [emDressedCompleted_return] at zero
  have zeroLeg : completedLeg true 1 0 (sourceProfile epsilon precision)=0 :=
    (smul_eq_zero.mp zero).resolve_left character
  have same : sourceLeg true 1 0 (sourcePreparation epsilon precision).point.val=
      completedLeg true 1 0 (sourceProfile epsilon precision) := rfl
  rw [same,zeroLeg,norm_zero] at lower
  norm_num at lower

theorem actual_dressed_excitation_exists (epsilon : ℝ) (precision : 0<epsilon) :
    ∃ addition : Bool,emDressedCompleted addition 1 0 (sourceProfile epsilon precision)≠0 :=
  ⟨true,actual_dressed_creation_nonzero epsilon precision⟩

/-- A nonzero charged dressed excitation is selected from the existing actual source preparation by its original CAR lower bound. -/
def sourceDressedAddition (epsilon : ℝ) (_precision : 0<epsilon) : Bool :=
  true

def sourceDressedExcitation (epsilon : ℝ) (precision : 0<epsilon) : H :=
  emDressedCompleted (sourceDressedAddition epsilon precision) 1 0 (sourceProfile epsilon precision)

theorem source_dressed_excitation_nonzero (epsilon : ℝ) (precision : 0<epsilon) :
    sourceDressedExcitation epsilon precision≠0 :=
  actual_dressed_creation_nonzero epsilon precision

/-- The actual Hilbert norm supplies the sole external state normalization. -/
def sourceDressedUnit (epsilon : ℝ) (precision : 0<epsilon) : H :=
  (‖sourceDressedExcitation epsilon precision‖:ℂ)⁻¹ • sourceDressedExcitation epsilon precision

theorem source_dressed_unit_norm (epsilon : ℝ) (precision : 0<epsilon) :
    ‖sourceDressedUnit epsilon precision‖=1 := by
  rw [sourceDressedUnit,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr (source_dressed_excitation_nonzero epsilon precision))]

theorem source_dressed_unit_original (epsilon : ℝ) (precision : 0<epsilon) :
    sourceDressedUnit epsilon precision=
      ((‖sourceDressedExcitation epsilon precision‖:ℂ)⁻¹*
        emDressedCharacter (sourceDressedAddition epsilon precision)) •
        completedLeg (sourceDressedAddition epsilon precision) 1 0 (sourceProfile epsilon precision) := by
  rw [sourceDressedUnit,sourceDressedExcitation,emDressedCompleted_return,smul_smul]

end LowEnergy.GaussComposite.ActualDressedSourcePreparation
