import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceMovingCARCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumMixedFieldReturn PreparationVacuumFullFieldRiesz PreparationVacuumHalfDensityFiber
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart PreparationVacuumSourceFieldFamily
open PreparationVacuumSourceActionJets GaussHistoryHilbert MeasureTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology
local instance instDecidableEqMode_actualSourceSelectedNoether : DecidableEq Mode:=Classical.decEq _
local instance selectedFinite : FiniteDimensional ℂ FullMaterialMatrix:=Matrix.finiteDimensional
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] restBlockFrame sourceHSCoordinates projectedNoetherForm
  projectedNoetherContactForm frameVector frameTest noetherReader noetherReaderContact

def sourceRestSelectedMap : FullMaterialMatrix→L[ℂ]FullMaterialMatrix:=
  (show FullMaterialMatrix→ₗ[ℂ]FullMaterialMatrix from
    {toFun:=sourceRestSelectedMatrix
     map_add':=by
       intro A B
       simp only [sourceRestSelectedMatrix,Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
     map_smul':=by
       intro q A
       simp only [sourceRestSelectedMatrix,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum,RingHom.id_apply]}).toContinuousLinearMap

private theorem source_cross_outside_value (A : FullMaterialMatrix) :
    sourceRestCrossMatrix A+sourceRestOutsideMatrix A=A-sourceRestSelectedMatrix A:=by
  have original:=source_rest_whole_matrix_partition A
  have selected:=source_rest_light_heavy_selected A
  rw [selected] at original
  apply eq_sub_iff_add_eq.mpr
  calc
    _=sourceRestSelectedMatrix A+sourceRestCrossMatrix A+sourceRestOutsideMatrix A:=by abel
    _=A:=original

/-- Actual cross-frame and outside-frame arms retain every original material direction, including weak0. -/
def sourceRestCrossOutsideMap : FullMaterialMatrix→L[ℂ]FullMaterialMatrix:=
  (show FullMaterialMatrix→ₗ[ℂ]FullMaterialMatrix from
    {toFun:=fun A=>sourceRestCrossMatrix A+sourceRestOutsideMatrix A
     map_add':=by
       intro A B
       rw [source_cross_outside_value,source_cross_outside_value,source_cross_outside_value]
       change A+B-sourceRestSelectedMap (A+B)=_
       rw [map_add]
       abel
     map_smul':=by
       intro q A
       rw [source_cross_outside_value,source_cross_outside_value]
       change q • A-sourceRestSelectedMap (q • A)=_
       rw [map_smul,smul_sub]
       rfl}).toContinuousLinearMap

theorem source_selected_cross_outside_partition (A : FullMaterialMatrix) :
    sourceRestSelectedMap A+sourceRestCrossOutsideMap A=A:=by
  change sourceRestSelectedMatrix A+(sourceRestCrossMatrix A+sourceRestOutsideMatrix A)=A
  rw [source_cross_outside_value]
  abel

theorem source_moving_material_identity (A : FullMaterialMatrix) :
    sourceMovingMaterialMatrix (fun _=>1) A=sourceRestSelectedMatrix A:=by
  unfold sourceMovingMaterialMatrix sourceRestSelectedMatrix
  apply Finset.sum_congr rfl
  intro block _
  rw [one_apply_eq_self,LinearEquiv.symm_apply_apply]
  unfold restBlockProjector restBlockLift restBlockRestriction
  simp only [Matrix.mul_one,Matrix.mul_assoc]

abbrev SelectedCellIndex:=RestBlock×(HSIndex×HSIndex)

def sourceSelectedNoetherFormCells (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) : ℂ:=
  ∑cell : SelectedCellIndex,sourceHSOperatorCell cell.2.1 cell.2.2 1*
    projectedNoetherForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader p a b h

def sourceSelectedNoetherContactCells (reader force : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) : ℂ:=
  ∑cell : SelectedCellIndex,sourceHSOperatorCell cell.2.1 cell.2.2 1*
    projectedNoetherContactForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader force p a b

/-- The source identity on HS is precisely its original selected four-state material carrier under the full configuration integral. -/
theorem source_selected_noether_form_cells (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (small : ‖h‖<ambientRadius a) :
    sourceSelectedNoetherFormCells reader p a b h=projectedNoetherForm sourceRestSelectedMap reader p a b h:=by
  let sample (cell : SelectedCellIndex) (z : SourceCoordinateSlice):=
    pairSample z (a z) (projectedNoetherFiber (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader p (h,z) (b z))
  have integrable (cell : SelectedCellIndex) : Integrable (sample cell) GaussHistoryHilbert.configurationMeasure:=
    projected_noether_form_integrable _ reader p a b h small
  unfold sourceSelectedNoetherFormCells projectedNoetherForm
  change (∑cell : SelectedCellIndex,sourceHSOperatorCell cell.2.1 cell.2.2 1*
    ∫z,sample cell z ∂GaussHistoryHilbert.configurationMeasure)=_
  calc
    _=∑cell : SelectedCellIndex,∫z,sourceHSOperatorCell cell.2.1 cell.2.2 1*sample cell z
      ∂GaussHistoryHilbert.configurationMeasure:=by
      apply Finset.sum_congr rfl
      intro cell _
      exact (integral_const_mul _ _).symm
    _=∫z,∑cell : SelectedCellIndex,sourceHSOperatorCell cell.2.1 cell.2.2 1*sample cell z
      ∂GaussHistoryHilbert.configurationMeasure:=
      (integral_finsetSum Finset.univ (fun cell _=>(integrable cell).const_mul _)).symm
    _=_:=by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      symm
      change (pairRight z (a z)) (quantizer (sourceRestSelectedMatrix
        (transportedRawSymbol reader (sourceState z) (ambientState (h,z)) p)) (b z))=_
      rw [←source_moving_material_identity]
      rw [source_moving_material_CAR_cells]
      simp only [sum_apply,smul_apply,map_sum,map_smul,smul_eq_mul]
      rfl

theorem source_selected_noether_contact_cells (reader force : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) :
    sourceSelectedNoetherContactCells reader force p a b=projectedNoetherContactForm sourceRestSelectedMap reader force p a b:=by
  have derivative : HasDerivAt (fun r : ℝ=>sourceSelectedNoetherFormCells reader p a b (r • force))
      (sourceSelectedNoetherContactCells reader force p a b) 0:=by
    apply HasDerivAt.fun_sum
    intro cell _
    exact (projected_noether_form_generated _ reader force p a b).const_mul _
  have near : ∀ᶠr : ℝ in 𝓝 0,‖r • force‖<ambientRadius a:=
    ((continuous_id.smul (continuous_const (y:=force))).continuousAt.norm).eventually_lt
      continuousAt_const (by simpa using ambientRadius_positive a)
  have same : (fun r : ℝ=>projectedNoetherForm sourceRestSelectedMap reader p a b (r • force))=ᶠ[𝓝 0]
      (fun r : ℝ=>sourceSelectedNoetherFormCells reader p a b (r • force)):=by
    filter_upwards [near] with r bound
    exact (source_selected_noether_form_cells reader p a b (r • force) bound).symm
  exact (derivative.congr_of_eventuallyEq same).unique
    (projected_noether_form_generated sourceRestSelectedMap reader force p a b)

end LowEnergy.GaussComposite.ActualMovingSourceLight
