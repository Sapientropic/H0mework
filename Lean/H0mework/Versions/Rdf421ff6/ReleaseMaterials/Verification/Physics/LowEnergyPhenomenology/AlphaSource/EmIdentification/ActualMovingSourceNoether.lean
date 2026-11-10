import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourceResolventContact
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceMovingCARCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumMixedFieldReturn PreparationVacuumFullFieldRiesz
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open GaussQuantumMultiplier PreparationVacuumHalfDensityFiber
open ActualCompositeFieldCurrent ActualElectronPhysicalJointInverse
open GaussCoreDifferential PreparationVacuumSourceActionJets FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily ActualElectronPhysicalNormalization
open GaussHistoryHilbert MeasureTheory Filter
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology
local instance instDecidableEqMode_actualMovingSourceNoether : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] projectedNoetherForm projectedNoetherContactForm frameTest frameVector
  actualMovingSourceRieszLight actualMovingSourceRieszContact sourceMovingCARCellMap

abbrev MovingCellIndex:=RestBlock×(HSIndex×HSIndex)

def actualMovingSourceCoefficient (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (cell : MovingCellIndex) (h : Field289) : ℂ:=
  sourceHSOperatorCell cell.2.1 cell.2.2 (actualMovingSourceRieszLight cell.1 pL pR (h,reference))

def actualMovingSourceCoefficientContact (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (force : Field289) (cell : MovingCellIndex) : ℂ:=
  sourceHSOperatorCell cell.2.1 cell.2.2 (actualMovingSourceRieszContact cell.1 pL pR force reference)

theorem actual_moving_source_coefficient_generated (pL pR : PhysicalMomentum) (reference : physicalChart)
    (force : Field289) (cell : MovingCellIndex)
    (small : ‖actualMovingSourceSylvester cell.1 pL pR (0,reference.val)-sourceRestHSGenerator cell.1‖<1/8) :
    HasDerivAt (fun r : ℝ=>actualMovingSourceCoefficient pL pR reference.val cell (r • force))
      (actualMovingSourceCoefficientContact pL pR reference.val force cell) 0:=by
  exact ((sourceHSOperatorCell cell.2.1 cell.2.2).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (actual_moving_source_riesz_contact_generated cell.1 pL pR force reference small)

/-- Matching references select the moving material spectrum; the independent original configuration integral remains complete. -/
def actualMovingNoetherForm (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  ∑cell : MovingCellIndex,actualMovingSourceCoefficient pL pR reference cell h*
    projectedNoetherForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader p a b h

def actualMovingNoetherContactForm (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ:=
  ∑cell : MovingCellIndex,
    (actualMovingSourceCoefficient pL pR reference cell 0*
      projectedNoetherContactForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader force p a b+
    actualMovingSourceCoefficientContact pL pR reference force cell*
      projectedNoetherForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader p a b 0)

/-- The original transported contact and the source Riesz contact are differentiated together. -/
theorem actual_moving_noether_form_generated (pL pR : PhysicalMomentum) (reference : physicalChart)
    (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (small : ∀block : RestBlock,‖actualMovingSourceSylvester block pL pR (0,reference.val)-sourceRestHSGenerator block‖<1/8) :
    HasDerivAt (fun r : ℝ=>actualMovingNoetherForm pL pR reference.val reader p a b (r • force))
      (actualMovingNoetherContactForm pL pR reference.val reader force p a b) 0:=by
  apply HasDerivAt.fun_sum
  intro cell _
  have coefficient:=actual_moving_source_coefficient_generated pL pR reference force cell (small cell.1)
  have current:=projected_noether_form_generated (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2)
    reader force p a b
  simpa only [zero_smul,mul_comm,add_comm,Pi.mul_apply] using! coefficient.mul current

/-- The coefficient circuit is the original configuration integral of the actual source Riesz-projected CAR current. -/
theorem actual_moving_noether_form_source_integral (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    actualMovingNoetherForm pL pR reference reader p a b 0=
      ∫z,pairSample z (a z)
        (quantizer (sourceMovingMaterialMatrix
          (fun block=>actualMovingSourceRieszLight block pL pR (0,reference))
          (transportedRawSymbol reader (sourceState z) (ambientState (0,z)) p)) (b z))
        ∂GaussHistoryHilbert.configurationMeasure:=by
  let coefficient:=actualMovingSourceCoefficient pL pR reference
  let sample (cell : MovingCellIndex) (z : SourceCoordinateSlice):=
    pairSample z (a z) (projectedNoetherFiber (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader p (0,z) (b z))
  have integrable (cell : MovingCellIndex) : Integrable (sample cell) GaussHistoryHilbert.configurationMeasure:=
    projected_noether_form_integrable _ reader p a b 0 (by simpa using ambientRadius_positive a)
  unfold actualMovingNoetherForm projectedNoetherForm
  change (∑cell : MovingCellIndex,coefficient cell 0*
    ∫z,sample cell z ∂GaussHistoryHilbert.configurationMeasure)=_
  calc
    _=∑cell : MovingCellIndex,∫z,coefficient cell 0*sample cell z ∂GaussHistoryHilbert.configurationMeasure:=by
      apply Finset.sum_congr rfl
      intro cell _
      exact (integral_const_mul _ _).symm
    _=∫z,∑cell : MovingCellIndex,coefficient cell 0*sample cell z ∂GaussHistoryHilbert.configurationMeasure:=by
      exact (integral_finsetSum Finset.univ (fun cell _=>(integrable cell).const_mul _)).symm
    _=_:=by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      symm
      change (pairRight z (a z)) (quantizer (sourceMovingMaterialMatrix
        (fun block=>actualMovingSourceRieszLight block pL pR (0,reference))
        (transportedRawSymbol reader (sourceState z) (ambientState (0,z)) p)) (b z))=_
      rw [source_moving_material_CAR_cells]
      simp only [sum_apply,smul_apply,map_sum,map_smul,smul_eq_mul]
      rfl

/-- The actual N3 Gram consumes the moving source projector under the original complete preparation measure. -/
theorem actual_prepared_moving_noether_finite_integral (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (leg : CompositeLeg) (reader : Field289) (p : PhysicalMomentum) :
    actualMovingNoetherForm pL pR reference reader p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg) 0=
      ∫z,(actualMaterialProbabilityDensity leg z/2)*sourceMovingMaterialCandidateRead
        (fun block=>actualMovingSourceRieszLight block pL pR (0,reference)) leg.dual
        (transportedRawSymbol reader (sourceState z) (ambientState (0,z)) p)
        ∂GaussHistoryHilbert.configurationMeasure:=by
  rw [actual_moving_noether_form_source_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [actual_material_pair_sample,source_moving_material_candidate_kernel]

def actualMovingNoetherReader (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : H→L[ℂ]H:=
  finiteRiesz F (fun i j=>actualMovingNoetherForm pL pR reference reader p (frameTest F i) (frameTest F j) h)

def actualMovingNoetherReaderContact (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H:=
  finiteRiesz F (fun i j=>actualMovingNoetherContactForm pL pR reference reader force p (frameTest F i) (frameTest F j))

theorem actual_moving_noether_reader_generated (pL pR : PhysicalMomentum) (reference : physicalChart)
    (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (small : ∀block : RestBlock,‖actualMovingSourceSylvester block pL pR (0,reference.val)-sourceRestHSGenerator block‖<1/8) :
    HasDerivAt (fun r : ℝ=>actualMovingNoetherReader pL pR reference.val reader p F (r • force))
      (actualMovingNoetherReaderContact pL pR reference.val reader force p F) 0:=by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (actual_moving_noether_form_generated pL pR reference reader force p (frameTest F i) (frameTest F j) small).smul_const
    (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))

/-- The rest source pays its own gap, so the projector derivative reaches the actual reader with no supplied gap witness. -/
theorem actual_rest_moving_noether_reader_generated (reader force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    HasDerivAt (fun r : ℝ=>actualMovingNoetherReader 0 0 GaussHistoryHilbert.sourcePoint.val reader p F (r • force))
      (actualMovingNoetherReaderContact 0 0 GaussHistoryHilbert.sourcePoint.val reader force p F) 0:=by
  apply actual_moving_noether_reader_generated 0 0 GaussHistoryHilbert.sourcePoint reader force p F
  intro block
  rw [actual_moving_sylvester_at_rest]
  norm_num

end LowEnergy.GaussComposite.ActualMovingSourceLight
