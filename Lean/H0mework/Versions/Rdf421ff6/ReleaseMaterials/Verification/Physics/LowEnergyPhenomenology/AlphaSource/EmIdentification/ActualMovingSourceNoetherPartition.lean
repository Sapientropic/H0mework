import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourceNoether
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceSelectedNoether

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
local instance instDecidableEqMode_actualMovingSourceNoetherPartition : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] projectedNoetherForm projectedNoetherContactForm
  frameVector frameTest noetherReader noetherReaderContact actualMovingSourceCoefficient
  actualMovingSourceCoefficientContact
attribute [local irreducible] actualMovingNoetherForm
  actualMovingNoetherContactForm sourceSelectedNoetherFormCells
  sourceSelectedNoetherContactCells actualMovingNoetherReader actualMovingNoetherReaderContact
  finiteRiesz sourceRestCrossOutsideMap sourceRestSelectedMap

/-- This is the source selected I-P current, while cross and outside remain separate original arms. -/
def actualMovingHeavyNoetherForm (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  ∑cell : MovingCellIndex,(sourceHSOperatorCell cell.2.1 cell.2.2 1-
    actualMovingSourceCoefficient pL pR reference cell h)*
      projectedNoetherForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader p a b h

def actualMovingHeavyNoetherContactForm (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ:=
  ∑cell : MovingCellIndex,
    ((sourceHSOperatorCell cell.2.1 cell.2.2 1-actualMovingSourceCoefficient pL pR reference cell 0)*
      projectedNoetherContactForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader force p a b-
    actualMovingSourceCoefficientContact pL pR reference force cell*
      projectedNoetherForm (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader p a b 0)

attribute [local irreducible] actualMovingHeavyNoetherForm actualMovingHeavyNoetherContactForm

theorem actual_moving_heavy_noether_form_generated (pL pR : PhysicalMomentum) (reference : physicalChart)
    (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (small : ∀block : RestBlock,‖actualMovingSourceSylvester block pL pR (0,reference.val)-sourceRestHSGenerator block‖<1/8) :
    HasDerivAt (fun r : ℝ=>actualMovingHeavyNoetherForm pL pR reference.val reader p a b (r • force))
      (actualMovingHeavyNoetherContactForm pL pR reference.val reader force p a b) 0:=by
  unfold actualMovingHeavyNoetherForm actualMovingHeavyNoetherContactForm
  apply HasDerivAt.fun_sum
  intro cell _
  have coefficient:=(hasDerivAt_const (0:ℝ) (sourceHSOperatorCell cell.2.1 cell.2.2 1)).sub
    (actual_moving_source_coefficient_generated pL pR reference force cell (small cell.1))
  have current:=projected_noether_form_generated (sourceMovingCARCellMap cell.1 cell.2.1 cell.2.2) reader force p a b
  simpa only [zero_smul,zero_sub,neg_mul,sub_eq_add_neg,mul_comm,add_comm,Pi.mul_apply,Pi.sub_apply,
    Pi.add_apply,Pi.neg_apply,zero_add] using!
    coefficient.mul current

theorem actual_moving_light_heavy_form_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) :
    actualMovingNoetherForm pL pR reference reader p a b h+
      actualMovingHeavyNoetherForm pL pR reference reader p a b h=sourceSelectedNoetherFormCells reader p a b h:=by
  unfold actualMovingNoetherForm actualMovingHeavyNoetherForm sourceSelectedNoetherFormCells
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro cell _
  ring

theorem actual_moving_light_heavy_contact_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    actualMovingNoetherContactForm pL pR reference reader force p a b+
      actualMovingHeavyNoetherContactForm pL pR reference reader force p a b=sourceSelectedNoetherContactCells reader force p a b:=by
  unfold actualMovingNoetherContactForm actualMovingHeavyNoetherContactForm sourceSelectedNoetherContactCells
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro cell _
  ring

theorem source_selected_cross_outside_noether_form (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (small : ‖h‖<ambientRadius a) :
    projectedNoetherForm sourceRestSelectedMap reader p a b h+
      projectedNoetherForm sourceRestCrossOutsideMap reader p a b h=noetherForm reader p a b h:=by
  have selected:=projected_noether_form_integrable sourceRestSelectedMap reader p a b h small
  have omitted:=projected_noether_form_integrable sourceRestCrossOutsideMap reader p a b h small
  unfold projectedNoetherForm
  change (∫z,pairSample z (a z) (projectedNoetherFiber sourceRestSelectedMap reader p (h,z) (b z))
    ∂GaussHistoryHilbert.configurationMeasure)+
    (∫z,pairSample z (a z) (projectedNoetherFiber sourceRestCrossOutsideMap reader p (h,z) (b z))
      ∂GaussHistoryHilbert.configurationMeasure)=_
  rw [←integral_add selected omitted]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change pairSample z (a z) _+pairSample z (a z) _=pairSample z (a z) _
  rw [←pairSample_add_right,←add_apply]
  congr 2
  unfold projectedNoetherFiber noetherFiber
  rw [←map_add,source_selected_cross_outside_partition]

theorem source_selected_cross_outside_noether_contact (reader force : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) :
    projectedNoetherContactForm sourceRestSelectedMap reader force p a b+
      projectedNoetherContactForm sourceRestCrossOutsideMap reader force p a b=noetherContactForm reader force p a b:=by
  have derivative:=(projected_noether_form_generated sourceRestSelectedMap reader force p a b).add
    (projected_noether_form_generated sourceRestCrossOutsideMap reader force p a b)
  have near : ∀ᶠr : ℝ in 𝓝 0,‖r • force‖<ambientRadius a:=
    ((continuous_id.smul (continuous_const (y:=force))).continuousAt.norm).eventually_lt
      continuousAt_const (by simpa using ambientRadius_positive a)
  have same : (fun r : ℝ=>noetherForm reader p a b (r • force))=ᶠ[𝓝 0]
      (fun r : ℝ=>projectedNoetherForm sourceRestSelectedMap reader p a b (r • force)+
        projectedNoetherForm sourceRestCrossOutsideMap reader p a b (r • force)):=by
    filter_upwards [near] with r bound
    exact (source_selected_cross_outside_noether_form reader p a b (r • force) bound).symm
  exact (derivative.congr_of_eventuallyEq same).unique (noetherForm_generated reader force p a b)

def actualMovingHeavyNoetherReader (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : H→L[ℂ]H:=
  finiteRiesz F (fun i j=>actualMovingHeavyNoetherForm pL pR reference reader p (frameTest F i) (frameTest F j) h)

def actualMovingHeavyNoetherReaderContact (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H:=
  finiteRiesz F (fun i j=>actualMovingHeavyNoetherContactForm pL pR reference reader force p (frameTest F i) (frameTest F j))

attribute [local irreducible] actualMovingHeavyNoetherReader actualMovingHeavyNoetherReaderContact

private theorem moving_riesz_add (F : GaussUnitaryHistory.Index)
    (a b : FrameIndex F→FrameIndex F→ℂ) :
    finiteRiesz F a+finiteRiesz F b=finiteRiesz F (fun i j=>a i j+b i j):=by
  simp only [finiteRiesz,add_smul,Finset.sum_add_distrib]

/-- Actual moving light, its selected I-P heavy, and the complete original cross/outside arms exhaust the unchanged current. -/
theorem actual_moving_noether_reader_whole_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    actualMovingNoetherReader pL pR reference reader p F 0+
      actualMovingHeavyNoetherReader pL pR reference reader p F 0+
      projectedNoetherReader sourceRestCrossOutsideMap reader p F 0=noetherReader reader p F 0:=by
  unfold actualMovingNoetherReader actualMovingHeavyNoetherReader projectedNoetherReader noetherReader
  rw [moving_riesz_add,moving_riesz_add]
  apply congrArg (finiteRiesz F)
  funext i j
  rw [actual_moving_light_heavy_form_partition,source_selected_noether_form_cells reader p
    (frameTest F i) (frameTest F j) 0 (by simpa using ambientRadius_positive (frameTest F i))]
  exact source_selected_cross_outside_noether_form reader p (frameTest F i) (frameTest F j) 0
    (by simpa using ambientRadius_positive (frameTest F i))

/-- P'J is retained in both differentiated source spectral arms and cancels only in their complete sum. -/
theorem actual_moving_noether_reader_contact_whole_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    actualMovingNoetherReaderContact pL pR reference reader force p F+
      actualMovingHeavyNoetherReaderContact pL pR reference reader force p F+
      projectedNoetherReaderContact sourceRestCrossOutsideMap reader force p F=noetherReaderContact reader force p F:=by
  let light : FrameIndex F→FrameIndex F→ℂ:=fun i j=>
    actualMovingNoetherContactForm pL pR reference reader force p (frameTest F i) (frameTest F j)
  let heavy : FrameIndex F→FrameIndex F→ℂ:=fun i j=>
    actualMovingHeavyNoetherContactForm pL pR reference reader force p (frameTest F i) (frameTest F j)
  let outside : FrameIndex F→FrameIndex F→ℂ:=fun i j=>
    projectedNoetherContactForm sourceRestCrossOutsideMap reader force p (frameTest F i) (frameTest F j)
  unfold actualMovingNoetherReaderContact actualMovingHeavyNoetherReaderContact projectedNoetherReaderContact
  change finiteRiesz F light+finiteRiesz F heavy+finiteRiesz F outside=_
  calc
    _=finiteRiesz F (fun i j=>light i j+heavy i j)+finiteRiesz F outside:=
      congrArg (fun A : H→L[ℂ]H=>A+finiteRiesz F outside) (moving_riesz_add F light heavy)
    _=finiteRiesz F (fun i j=>light i j+heavy i j+outside i j):=
      moving_riesz_add F (fun i j=>light i j+heavy i j) outside
    _=noetherReaderContact reader force p F:=by
      rw [noetherReaderContact_source]
      apply congrArg (finiteRiesz F)
      funext i j
      change actualMovingNoetherContactForm pL pR reference reader force p (frameTest F i) (frameTest F j)+
        actualMovingHeavyNoetherContactForm pL pR reference reader force p (frameTest F i) (frameTest F j)+
        projectedNoetherContactForm sourceRestCrossOutsideMap reader force p (frameTest F i) (frameTest F j)=_
      rw [actual_moving_light_heavy_contact_partition,source_selected_noether_contact_cells]
      exact source_selected_cross_outside_noether_contact reader force p (frameTest F i) (frameTest F j)

end LowEnergy.GaussComposite.ActualMovingSourceLight
