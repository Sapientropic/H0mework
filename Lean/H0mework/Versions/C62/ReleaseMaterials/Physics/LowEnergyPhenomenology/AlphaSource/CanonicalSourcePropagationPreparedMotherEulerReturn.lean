import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeVariationDirections
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationMotherConnectionDirections
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeAlgebraicEulerIdentification
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeScalarEulerIdentification
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativePrimalEulerIdentification
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeConnectionEulerIdentification

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineScalarVariation StageNineScalarPointwiseEquation StageNineMatterVariation StageNineMatterPointwiseEquation
open StageNineTopologicalLorentzThreeFormDuality StageNineTopologicalP286GaugeThreeFormDuality
open StageNineDiracMatterCoordinateCalculus StageNineLorentzConnectionVariation StageNineGravityBianchi StageNineP286Bianchi StageNineResidualLinearPlebanskiTorsionReduction
open StageNineGlobalIntegratedAction Stage9C.Material.SpinPair
open StageNineTopologicalFourFormPairing StageNineFormNativeGaugeWedge StageNineConjugateMatterVariation DiracExteriorMatterAction
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel SourcePropagationNativeEulerHistory
open PreparationVacuumMixedFieldReturn PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumFieldConstraintResponse PreparationVacuumGaugeSourceInjection
open SourcePropagationNoetherTime
open Filter MeasureTheory
open scoped Topology ContDiff BigOperators Matrix
attribute [local irreducible] nativeDensity nativeJetDensity nativeHessian nativeHolonomicEuler
  actualPreparedHistorySource actualHistoryLinearSource originalJacobi originalReader36

theorem motherHistoryRegular (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) :
    ContDiffAt ℝ 1 (nativeTimeHistory signal) 0 :=
  (nativeTimeHistory_smooth signal smooth).contDiffAt.of_le (by
    change ((1 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top)

theorem motherSignalC2 (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal) (point : BasePoint) :
    ContDiffAt ℝ 2 signal point := smooth.contDiffAt.of_le (by
  change ((2 : ℕ∞) : ℕ∞ω)≤((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top)

/-- The original ordinary Euler and the actual nonlinear prepared source use the same field amplitude and the same physical clock. -/
def actualPreparedMotherEuler (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (amplitude t : ℝ) (field : Fin 289) : ℂ :=
  Complex.ofReal (nativeHolonomicEuler (fun point=>amplitude • signal point) (nativeTimePoint t) field)-
    actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) amplitude t field

def actualPreparedMotherFirstVariation (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (variation : BasePoint→Field289) (t : ℝ) : ℂ :=
  Complex.ofReal (deriv (fun a : ℝ=>nativeDensity (fun point=>signal point+a • variation point) (nativeTimePoint t)) 0)-
    ∑ field : Fin 289,Complex.ofReal (variation (nativeTimePoint t) field)*
      actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) 1 t field

theorem actualPreparedMotherFirstVariation_euler (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (variation : BasePoint→Field289) (t : ℝ)
    (variationSmooth : DifferentiableAt ℝ variation (nativeTimePoint t))
    (inside : signalFirstJet signal (nativeTimePoint t)∈nativeEulerSourceDomain) :
    actualPreparedMotherFirstVariation q signal smooth variation t=
      (∑ field : Fin 289,Complex.ofReal (variation (nativeTimePoint t) field)*
        actualPreparedMotherEuler q signal smooth 1 t field)+
        Complex.ofReal (∑ mu : Fin 4,fieldDirectionalDerivative (nativeVariationFlux signal variation mu) (nativeTimePoint t) mu) := by
  have density:=nativeDensity_variation_euler signal variation (nativeTimePoint t)
    (motherSignalC2 signal smooth _) variationSmooth inside
  unfold actualPreparedMotherFirstVariation actualPreparedMotherEuler
  rw [density]
  simp only [one_smul,Complex.ofReal_add,Complex.ofReal_sum,Complex.ofReal_mul,mul_sub,
    Finset.sum_sub_distrib]
  ring

/-- This derivative is generated from the nonlinear source family, with both material preparation legs and the observation contact retained. -/
theorem actualPreparedMotherEuler_generated (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ)
    (nonnegative : 0≤t) (inside : t<preparedHistoryDuration q (nativeTimeHistory signal) (motherHistoryRegular signal smooth))
    (field : Fin 289) :
    HasDerivAt (fun a : ℝ=>actualPreparedMotherEuler q signal smooth a t field)
      (Complex.ofReal (nativeEulerLinearJet (signalSecondJet signal (nativeTimePoint t)) field)-
        (noetherHistorySourceJet q (nativeTimeSignal signal) t field).value) 0 := by
  have ordinary:=nativeHolonomicEuler_source_linear signal (nativeTimePoint t) (motherSignalC2 signal smooth _) field
  have realOrdinary:=(Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ordinary)
  have prepared:=actualPreparedHistorySource_generated q (nativeTimeSignal signal)
    (motherHistoryRegular signal smooth) hz hw t nonnegative inside field
  have generated:=realOrdinary.sub prepared
  convert! generated using 1

theorem actualPreparedMotherEuler_linear (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ)
    (nonnegative : 0≤t) (inside : t<preparedHistoryDuration q (nativeTimeHistory signal) (motherHistoryRegular signal smooth))
    (field : Fin 289) :
    deriv (fun a : ℝ=>actualPreparedMotherEuler q signal smooth a t field) 0=
      Complex.ofReal (nativeEulerLinearJet (signalSecondJet signal (nativeTimePoint t)) field)-
        actualHistoryLinearSource q (nativeTimeSignal signal) (motherHistoryRegular signal smooth) t field := by
  rw [(actualPreparedMotherEuler_generated q signal smooth hz hw t nonnegative inside field).deriv,
    actualHistoryLinearSource_value q (nativeTimeSignal signal) (motherHistoryRegular signal smooth) hz hw t nonnegative inside]

/-- The ordinary quadratic responsibility remains the second coefficient of the very same original Euler family. -/
theorem motherOrdinaryRemainder_generated (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal)
    (t : ℝ) (field : Fin 289) :
    HasDerivAt (deriv (fun a : ℝ=>nativeHolonomicEuler (fun point=>a • signal point) (nativeTimePoint t) field))
      (2*nativeOrdinaryRemainder signal t field) 0 := nativeOrdinaryRemainder_generated signal smooth t field

theorem preparedMotherSource_actual (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ)
    (nonnegative : 0≤t) (inside : t<preparedHistoryDuration q (nativeTimeHistory signal) (motherHistoryRegular signal smooth))
    (field : Fin 289) :
    preparedOrdinarySource q signal t field=
      actualHistoryLinearSource q (nativeTimeSignal signal) (motherHistoryRegular signal smooth) t field-
        Complex.ofReal (nativeOrdinaryRemainder signal t field) :=
  preparedOrdinarySource_actual q signal smooth hz hw t nonnegative inside field

theorem preparedMotherField_native (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      preparedOrdinaryField q signal lambda T=
        preparedOrdinaryForcing q signal lambda.val T-
          originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val) (preparedOrdinaryForcing q signal lambda.val T) :=
  preparedOrdinaryField_native q signal lambda T

theorem preparedMotherField_native36 (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ preparedOrdinaryField q signal lambda T)=
        originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ preparedOrdinaryForcing q signal lambda.val T-
          originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            (originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
              sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val) (preparedOrdinaryForcing q signal lambda.val T)) :=
  preparedOrdinaryField_native36 q signal lambda T

theorem preparedMotherForcing_cosources (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda) *ᵥ preparedOrdinaryForcing q signal lambda T) row=
      (∫ t in (0 : ℝ)..T,laplaceWeight lambda t*preparedOrdinaryTimeSource q signal spatial t row)-
        (preparedOrdinaryBoundary q signal spatial lambda T row-preparedOrdinaryBoundary q signal spatial lambda 0 row) :=
  preparedOrdinaryForcing_cosources q signal smooth spatial lambda T row

/-- The actual auxiliary source equations enter the identical prepared nonlinear family, with the quantum source sign unchanged. -/
theorem actualPreparedMotherEuler_multiplier (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (t : ℝ)
    (inside : signalFirstJet signal (nativeTimePoint t)∈nativeEulerSourceDomain)
    (field : Fin 289) (range : 181≤field.val ∧ field.val<217) :
    actualPreparedMotherEuler q signal smooth 1 t field=
      Complex.ofReal (gravityTopologicalWedgeCoefficient (fieldMultiplier (Pi.single field 1))
        (nativeEuler signal (nativeTimePoint t)).gravityMultiplier)-
      actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) 1 t field := by
  unfold actualPreparedMotherEuler
  simp only [one_smul]
  rw [nativeMultiplierEuler_identification signal _ (smooth.differentiable (by simp) |>.differentiableAt) inside field range]

theorem actualPreparedMotherEuler_gravityAuxiliary (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (t : ℝ)
    (inside : signalFirstJet signal (nativeTimePoint t)∈nativeEulerSourceDomain)
    (field : Fin 289) (range : 145≤field.val ∧ field.val<181) :
    actualPreparedMotherEuler q signal smooth 1 t field=
      Complex.ofReal (gravityTopologicalWedgeCoefficient (fieldGravityB (Pi.single field 1))
        (nativeEuler signal (nativeTimePoint t)).gravityAuxiliary)-
      actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) 1 t field := by
  unfold actualPreparedMotherEuler
  simp only [one_smul]
  rw [nativeGravityAuxiliaryEuler_identification signal _ (smooth.differentiable (by simp) |>.differentiableAt) inside field range]

theorem actualPreparedMotherEuler_gaugeAuxiliary (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (t : ℝ)
    (inside : signalFirstJet signal (nativeTimePoint t)∈nativeEulerSourceDomain)
    (nondegenerate : Matrix.det (nativePoint signal (nativeTimePoint t)).coframe≠0)
    (field : Fin 289) (range : 217≤field.val) :
    actualPreparedMotherEuler q signal smooth 1 t field=
      Complex.ofReal (formNativeP286GaugeWedgeCoefficient (gaugeBInsertion (Pi.single field 1))
        (nativeEuler signal (nativeTimePoint t)).p286GaugeAuxiliary)-
      actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) 1 t field := by
  unfold actualPreparedMotherEuler
  simp only [one_smul]
  rw [nativeGaugeAuxiliaryEuler_identification signal _ (smooth.differentiable (by simp) |>.differentiableAt) inside nondegenerate field range]

theorem actualPreparedMotherEuler_coframe (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (t : ℝ)
    (inside : signalFirstJet signal (nativeTimePoint t)∈nativeEulerSourceDomain)
    (nondegenerate : Matrix.det (nativePoint signal (nativeTimePoint t)).coframe≠0)
    (field : Fin 289) (range : 57≤field.val ∧ field.val<73) :
    actualPreparedMotherEuler q signal smooth 1 t field=
      Complex.ofReal ((nativeEuler signal (nativeTimePoint t)).coframe (fieldCoframe (Pi.single field 1)))-
      actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) 1 t field := by
  unfold actualPreparedMotherEuler
  simp only [one_smul]
  rw [nativeCoframeEuler_identification signal _ (smooth.differentiable (by simp) |>.differentiableAt) inside nondegenerate field range]

theorem actualPreparedMotherEuler_independentDual (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (t : ℝ)
    (inside : signalFirstJet signal (nativeTimePoint t)∈nativeEulerSourceDomain)
    (field : Fin 289) (range : 97≤field.val ∧ field.val<121) :
    actualPreparedMotherEuler q signal smooth 1 t field=
      Complex.ofReal ((nativeEuler signal (nativeTimePoint t)).conjugateMatter
        (matterDualCoordinates ((dualInsertion (Pi.single field 1)).comp (diracMatrixMatterAction (ActiveGauge.rotation (nativeTimePoint t))))))-
      actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) 1 t field := by
  unfold actualPreparedMotherEuler
  simp only [one_smul]
  rw [nativeIndependentDualEuler_identification signal _ (smooth.differentiable (by simp) |>.differentiableAt) inside field range]


private theorem originalUnit_read_off (field entry : Fin 289) (lower upper : ℕ)
    (entryInside : lower≤entry.val ∧ entry.val<upper) (outside : field.val<lower ∨ upper≤field.val) :
    (Pi.single field (1 : ℝ) : Field289) entry=0 := by
  have different : entry≠field := by intro same;subst entry;omega
  simp [different]

private theorem unitScalar_off (field : Fin 289) (outside : 9≤field.val) : fieldScalar (Pi.single field 1)=0 := by
  have each (index : Fin 9) : (Pi.single field (1 : ℝ) : Field289) (scalarSlot index)=0 :=
    originalUnit_read_off field _ 0 9 (by simp only [scalarSlot];omega) (Or.inr outside)
  simp only [fieldScalar,each,zero_smul,Finset.sum_const_zero]

private theorem unitGauge_off (field : Fin 289) (outside : field.val<9 ∨ 57≤field.val) : fieldGauge (Pi.single field 1)=0 := by
  funext mu
  have each (index : Fin 12) : (Pi.single field (1 : ℝ) : Field289) (gaugeSlot mu index)=0 :=
    originalUnit_read_off field _ 9 57 (by simp only [gaugeSlot];omega) outside
  simp only [fieldGauge,each,zero_smul,Finset.sum_const_zero,Pi.zero_apply]

private theorem unitCoframe_off (field : Fin 289) (outside : field.val<57 ∨ 73≤field.val) : fieldCoframe (Pi.single field 1)=0 := by
  funext a mu
  exact originalUnit_read_off field _ 57 73 (by simp only [coframeSlot];omega) outside

private theorem unitPrimal_off (field : Fin 289) (outside : field.val<73 ∨ 97≤field.val) : primalInsertion (Pi.single field 1)=0 := by
  have each (part : Fin 2) (spin : Fin 4) (color : Fin 3) : fieldPrimal (Pi.single field 1) part spin color=0 :=
    originalUnit_read_off field _ 73 97 (by simp only [primalSlot];omega) outside
  simp only [primalInsertion,fieldPrimalComplex,each,Complex.ofReal_zero,mul_zero,add_zero,zero_smul,Finset.sum_const_zero]

private theorem unitDual_off (field : Fin 289) (outside : field.val<97 ∨ 121≤field.val) : dualInsertion (Pi.single field 1)=0 := by
  have each (part : Fin 2) (spin : Fin 4) (color : Fin 3) : fieldDual (Pi.single field 1) part spin color=0 :=
    originalUnit_read_off field _ 97 121 (by simp only [dualSlot];omega) outside
  apply LinearMap.ext
  intro matter
  simp only [dualInsertion,fieldDualComplex,each,Complex.ofReal_zero,mul_zero,add_zero,LinearMap.coe_mk,AddHom.coe_mk,zero_mul,Finset.sum_const_zero,LinearMap.zero_apply]

private theorem unitLorentz_off (field : Fin 289) (outside : field.val<121 ∨ 145≤field.val) : fieldLorentz (Pi.single field 1)=0 := by
  funext mu a
  exact originalUnit_read_off field _ 121 145 (by simp only [lorentzSlot];omega) outside

private theorem unitGravity_off (field : Fin 289) (outside : field.val<145 ∨ 181≤field.val) : fieldGravityB (Pi.single field 1)=0 := by
  funext pair a
  exact originalUnit_read_off field _ 145 181 (by simp only [gravitySlot];omega) outside

private theorem unitMultiplier_off (field : Fin 289) (outside : field.val<181 ∨ 217≤field.val) : fieldMultiplier (Pi.single field 1)=0 := by
  funext pair a
  exact originalUnit_read_off field _ 181 217 (by simp only [multiplierSlot];omega) outside

private theorem unitGaugeAuxiliary_off (field : Fin 289) (outside : field.val<217) : gaugeBInsertion (Pi.single field 1)=0 := by
  funext pair
  have each (index : Fin 12) : (Pi.single field (1 : ℝ) : Field289) (gaugeBSlot pair index)=0 :=
    originalUnit_read_off field _ 217 289 (by simp only [gaugeBSlot];omega) (Or.inl outside)
  simp only [gaugeBInsertion,fieldGaugeB,each,zero_smul,Finset.sum_const_zero,map_zero,Pi.zero_apply]

private theorem lorentzWedge_zero (residual : PhysicalBivectorThreeForm) : lorentzOneFormThreeFormWedgeCoefficient 0 residual=0 := by
  have additive:=lorentzOneFormThreeFormWedgeCoefficient_add_left 0 0 residual
  simp only [zero_add] at additive
  linarith

private theorem gaugeWedge_zero (residual : P286GaugeThreeForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient 0 residual=0 := by
  have additive:=p286GaugeOneFormThreeFormWedgeCoefficient_add_left 0 0 residual
  simp only [zero_add] at additive
  linarith

private theorem matterSmul_zero (a : ℝ) : a • (0 : DiracExteriorMatterCarrier)=0 := by
  change (a : ℂ) • (0 : DiracExteriorMatterCarrier)=0
  exact smul_zero (a : ℂ)

private theorem scalarCurve_zero (signal : BasePoint→Field289) (point : BasePoint) :
    motherScalarCurve signal point 0 0=(fun _ : ℝ=>motherDensityAt point (nativePoint signal point)) := by
  funext a
  unfold motherScalarCurve
  simp only [smul_zero,add_zero]
  congr 1

private theorem primalCurve_zero (signal : BasePoint→Field289) (point : BasePoint) :
    motherPrimalCurve signal point 0 0=(fun _ : ℝ=>motherDensityAt point (nativePoint signal point)) := by
  funext a
  unfold motherPrimalCurve
  have functionZero : a • (0 : Fin 4→DiracExteriorMatterCarrier)=0 := by funext mu;exact matterSmul_zero a
  rw [matterSmul_zero,functionZero,add_zero,add_zero]
  congr 1

private theorem rawScalar_zero (signal : BasePoint→Field289) (point : BasePoint) : (nativeEuler signal point).scalar 0=0 := by
  have algebraic : motherScalarAlgebraicCurve signal point 0=motherScalarCurve signal point 0 0 := by
    unfold motherScalarAlgebraicCurve
    congr 1
    funext mu
    simp only [pointwiseScalarVariationAlgebraicDirection,StageNineHolonomicField.scalarMotherLieAction,map_zero]
    rfl
  have momentum (position : BasePoint) (mu : Fin 4) : motherScalarMomentumCurve signal position 0 mu=motherScalarCurve signal position 0 0 := by
    unfold motherScalarMomentumCurve
    congr 1
    funext nu
    simp only [scalarVariationDifferentialDirection,ite_self,Pi.zero_apply]
  rw [motherScalarEuler_action,algebraic,scalarCurve_zero]
  simp_rw [momentum,scalarCurve_zero]
  simp only [deriv_const,fieldDirectionalDerivative]
  simp only [(hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) point).fderiv,zero_apply,Finset.sum_const_zero,sub_self]

private theorem rawPrimal_zero (signal : BasePoint→Field289) (point : BasePoint) : (nativeEuler signal point).matter 0=0 := by
  have algebraic : motherPrimalAlgebraicCurve signal point 0=motherPrimalCurve signal point 0 0 := by
    unfold motherPrimalAlgebraicCurve
    simp only [map_zero]
    congr 1
    funext mu
    simp only [pointwiseMatterVariationAlgebraicDirection,map_zero,zero_add,Pi.zero_apply]
  have momentum (position : BasePoint) (mu : Fin 4) : motherPrimalMomentumCurve signal position 0 mu=motherPrimalCurve signal position 0 0 := by
    unfold motherPrimalMomentumCurve
    simp only [map_zero,ite_self]
    rfl
  rw [motherPrimalEuler_action,algebraic,primalCurve_zero]
  simp_rw [momentum,primalCurve_zero]
  simp only [deriv_const,fieldDirectionalDerivative]
  simp only [(hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) point).fderiv,zero_apply,Finset.sum_const_zero,sub_self]

private theorem rawDual_zero (signal : BasePoint→Field289) (point : BasePoint) : (nativeEuler signal point).conjugateMatter 0=0 := by
  rw [motherIndependentDualEuler_action]
  have curve : motherIndependentDualCurve signal point 0=(fun _ : ℝ=>motherDensityAt point (nativePoint signal point)) := by
    funext a
    unfold motherIndependentDualCurve
    rw [matterDualOfCoordinates_zero,smul_zero,add_zero]
    congr 1
  rw [curve,deriv_const]

private theorem dualCoordinates_zero (point : BasePoint) :
    matterDualCoordinates ((0 : Module.Dual ℂ DiracExteriorMatterCarrier).comp (diracMatrixMatterAction (ActiveGauge.rotation point)))=0 := by
  rfl

/-- Every original mother residual component is recognized from the same actual holonomic density. -/
theorem nativeHolonomicEuler_raw (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiff ℝ ∞ signal) (inside : signalFirstJet signal point∈nativeEulerSourceDomain)
    (nondegenerate : Matrix.det (nativePoint signal point).coframe≠0) (field : Fin 289) :
    nativeHolonomicEuler signal point field=actualMotherEulerRead signal point (Pi.single field 1) := by
  have c2:=motherSignalC2 signal smooth point
  have differentiable:=(smooth.differentiable (by simp)).differentiableAt (x := point)
  have configurationSmooth:=nativeConfiguration_source_smooth signal smooth
  have admissible:=nativeConfiguration_lorentzAdmissible signal
  unfold actualMotherEulerRead motherResidualPullback
  by_cases sector0 : field.val<9
  · simp only [unitGauge_off field (by omega),
      unitCoframe_off field (by omega),
      unitPrimal_off field (by omega),
      unitDual_off field (by omega),
      unitLorentz_off field (by omega),
      unitGravity_off field (by omega),
      unitMultiplier_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      lorentzWedge_zero,gaugeWedge_zero,map_zero,dualCoordinates_zero,rawPrimal_zero,rawDual_zero,zero_add,add_zero]
    let index : Fin 9:=⟨field.val,sector0⟩
    have original : scalarSlot index=field := by apply Fin.ext;rfl
    simpa only [original] using nativeScalarEuler_identification signal point c2 inside index
  by_cases sector1 : field.val<57
  · simp only [unitScalar_off field (by omega),
      unitCoframe_off field (by omega),
      unitPrimal_off field (by omega),
      unitDual_off field (by omega),
      unitLorentz_off field (by omega),
      unitGravity_off field (by omega),
      unitMultiplier_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      lorentzWedge_zero,map_zero,dualCoordinates_zero,rawScalar_zero,rawPrimal_zero,rawDual_zero,zero_add,add_zero]
    exact nativeGaugeEuler_identification signal point c2 configurationSmooth inside field (by omega)
  by_cases sector2 : field.val<73
  · simp only [unitScalar_off field (by omega),
      unitGauge_off field (by omega),
      unitPrimal_off field (by omega),
      unitDual_off field (by omega),
      unitLorentz_off field (by omega),
      unitGravity_off field (by omega),
      unitMultiplier_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      lorentzWedge_zero,gaugeWedge_zero,map_zero,dualCoordinates_zero,rawScalar_zero,rawPrimal_zero,rawDual_zero,zero_add,add_zero]
    exact nativeCoframeEuler_identification signal point differentiable inside nondegenerate field (by omega)
  by_cases sector3 : field.val<97
  · simp only [unitScalar_off field (by omega),
      unitGauge_off field (by omega),
      unitCoframe_off field (by omega),
      unitDual_off field (by omega),
      unitLorentz_off field (by omega),
      unitGravity_off field (by omega),
      unitMultiplier_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      lorentzWedge_zero,gaugeWedge_zero,map_zero,dualCoordinates_zero,rawScalar_zero,rawDual_zero,zero_add,add_zero]
    exact nativePrimalEuler_identification signal point c2 inside field (by omega)
  by_cases sector4 : field.val<121
  · simp only [unitScalar_off field (by omega),
      unitGauge_off field (by omega),
      unitCoframe_off field (by omega),
      unitPrimal_off field (by omega),
      unitLorentz_off field (by omega),
      unitGravity_off field (by omega),
      unitMultiplier_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      lorentzWedge_zero,gaugeWedge_zero,map_zero,rawScalar_zero,rawPrimal_zero,zero_add,add_zero]
    exact nativeIndependentDualEuler_identification signal point differentiable inside field (by omega)
  by_cases sector5 : field.val<145
  · simp only [unitScalar_off field (by omega),
      unitGauge_off field (by omega),
      unitCoframe_off field (by omega),
      unitPrimal_off field (by omega),
      unitDual_off field (by omega),
      unitGravity_off field (by omega),
      unitMultiplier_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      gaugeWedge_zero,map_zero,dualCoordinates_zero,rawScalar_zero,rawPrimal_zero,rawDual_zero,zero_add,add_zero]
    exact nativeLorentzEuler_identification signal point c2 configurationSmooth admissible inside field (by omega)
  by_cases sector6 : field.val<181
  · simp only [unitScalar_off field (by omega),
      unitGauge_off field (by omega),
      unitCoframe_off field (by omega),
      unitPrimal_off field (by omega),
      unitDual_off field (by omega),
      unitLorentz_off field (by omega),
      unitMultiplier_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      lorentzWedge_zero,gaugeWedge_zero,map_zero,dualCoordinates_zero,rawScalar_zero,rawPrimal_zero,rawDual_zero,zero_add,add_zero]
    exact nativeGravityAuxiliaryEuler_identification signal point differentiable inside field (by omega)
  by_cases sector7 : field.val<217
  · simp only [unitScalar_off field (by omega),
      unitGauge_off field (by omega),
      unitCoframe_off field (by omega),
      unitPrimal_off field (by omega),
      unitDual_off field (by omega),
      unitLorentz_off field (by omega),
      unitGravity_off field (by omega),
      unitGaugeAuxiliary_off field (by omega),
      gravityTopologicalWedgeCoefficient_zero_left,formNativeP286GaugeWedgeCoefficient_zero_left,
      lorentzWedge_zero,gaugeWedge_zero,map_zero,dualCoordinates_zero,rawScalar_zero,rawPrimal_zero,rawDual_zero,add_zero]
    exact nativeMultiplierEuler_identification signal point differentiable inside field (by omega)
  simp only [unitScalar_off field (by omega),
    unitGauge_off field (by omega),
    unitCoframe_off field (by omega),
    unitPrimal_off field (by omega),
    unitDual_off field (by omega),
    unitLorentz_off field (by omega),
    unitGravity_off field (by omega),
    unitMultiplier_off field (by omega),
    gravityTopologicalWedgeCoefficient_zero_left,
    lorentzWedge_zero,gaugeWedge_zero,map_zero,dualCoordinates_zero,rawScalar_zero,rawPrimal_zero,rawDual_zero,zero_add,add_zero]
  exact nativeGaugeAuxiliaryEuler_identification signal point differentiable inside nondegenerate field (by omega)

/-- The generated nonlinear preparation is subtracted from the original nine-channel mother residual at the same amplitude and event. -/
theorem actualPreparedMotherEuler_raw (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (amplitude t : ℝ)
    (inside : signalFirstJet (fun point=>amplitude • signal point) (nativeTimePoint t)∈nativeEulerSourceDomain)
    (nondegenerate : Matrix.det (nativePoint (fun point=>amplitude • signal point) (nativeTimePoint t)).coframe≠0)
    (field : Fin 289) :
    actualPreparedMotherEuler q signal smooth amplitude t field=
      Complex.ofReal (actualMotherEulerRead (fun point=>amplitude • signal point) (nativeTimePoint t) (Pi.single field 1))-
        actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) amplitude t field := by
  have scaled : ContDiff ℝ ∞ (fun point=>amplitude • signal point) := smooth.const_smul amplitude
  have original:=nativeHolonomicEuler_raw (fun point=>amplitude • signal point) (nativeTimePoint t)
    scaled inside nondegenerate field
  exact congrArg (fun value : ℝ=>Complex.ofReal value-
    actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) amplitude t field) original


/-- The original positive source generates the amplitude neighborhood in which the actual raw mother read is the holonomic Euler. -/
theorem nativeHolonomicEuler_raw_near (signal : BasePoint→Field289) (point : BasePoint)
    (smooth : ContDiff ℝ ∞ signal) (field : Fin 289) :
    (fun a : ℝ=>nativeHolonomicEuler (fun position=>a • signal position) point field)=ᶠ[𝓝 0]
      fun a=>actualMotherEulerRead (fun position=>a • signal position) point (Pi.single field 1) := by
  have ray : Continuous (fun a : ℝ=>a • signalFirstJet signal point) := continuous_id.smul continuous_const
  have domainNear : ∀ᶠ a : ℝ in 𝓝 0,a • signalFirstJet signal point∈nativeEulerSourceDomain :=
    (ray.continuousAt (x:= (0 : ℝ))).eventually_mem
      (by simpa only [zero_smul] using nativeEulerSourceDomain_generated)
  have coframe (a : ℝ) : (nativePoint (fun position=>a • signal position) point).coframe=
      actual.coframe point+a • coframeInsertionCLM (signal point) := by
    unfold nativePoint toContinuumPointField nativeConfiguration
    change actual.coframe point+coframeInsertionCLM (a • signal point)=_
    rw [map_smul]
  have determinant : Continuous (fun a : ℝ=>Matrix.det (actual.coframe point+a • coframeInsertionCLM (signal point))) := by
    fun_prop
  have nondegenerateNear : ∀ᶠ a : ℝ in 𝓝 0,Matrix.det (actual.coframe point+a • coframeInsertionCLM (signal point))≠0 :=
    (isOpen_ne_fun determinant continuous_const).mem_nhds (by simpa only [Set.mem_ofPred_eq,zero_smul,add_zero] using actual_nondegenerate point)
  filter_upwards [domainNear,nondegenerateNear] with a domain regular
  have inside : signalFirstJet (fun position=>a • signal position) point∈nativeEulerSourceDomain := by
    rwa [signalFirstJet_smul signal point (smooth.differentiable (by simp) |>.differentiableAt) a]
  exact nativeHolonomicEuler_raw _ _ (smooth.const_smul a) inside (by rwa [coframe]) field

/-- This is the original full mother residual, before any linearization, with the same nonlinear prepared source. -/
def actualPreparedRawMotherEuler (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (amplitude t : ℝ) (field : Fin 289) : ℂ :=
  Complex.ofReal (actualMotherEulerRead (fun point=>amplitude • signal point) (nativeTimePoint t) (Pi.single field 1))-
    actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) amplitude t field

theorem actualPreparedRawMotherEuler_generated (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ)
    (nonnegative : 0≤t) (inside : t<preparedHistoryDuration q (nativeTimeHistory signal) (motherHistoryRegular signal smooth))
    (field : Fin 289) :
    HasDerivAt (fun a : ℝ=>actualPreparedRawMotherEuler q signal smooth a t field)
      (Complex.ofReal (nativeEulerLinearJet (signalSecondJet signal (nativeTimePoint t)) field)-
        (noetherHistorySourceJet q (nativeTimeSignal signal) t field).value) 0 := by
  have near : (fun a : ℝ=>actualPreparedMotherEuler q signal smooth a t field)=ᶠ[𝓝 0]
      fun a=>actualPreparedRawMotherEuler q signal smooth a t field := by
    filter_upwards [nativeHolonomicEuler_raw_near signal (nativeTimePoint t) smooth field] with a original
    exact congrArg (fun value : ℝ=>Complex.ofReal value-
      actualPreparedHistorySource q (nativeTimeHistory signal) (motherHistoryRegular signal smooth) a t field) original
  exact (actualPreparedMotherEuler_generated q signal smooth hz hw t nonnegative inside field).congr_of_eventuallyEq near.symm

theorem actualPreparedRawMotherEuler_linear (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ)
    (nonnegative : 0≤t) (inside : t<preparedHistoryDuration q (nativeTimeHistory signal) (motherHistoryRegular signal smooth))
    (field : Fin 289) :
    deriv (fun a : ℝ=>actualPreparedRawMotherEuler q signal smooth a t field) 0=
      Complex.ofReal (nativeEulerLinearJet (signalSecondJet signal (nativeTimePoint t)) field)-
        actualHistoryLinearSource q (nativeTimeSignal signal) (motherHistoryRegular signal smooth) t field := by
  rw [(actualPreparedRawMotherEuler_generated q signal smooth hz hw t nonnegative inside field).deriv,
    actualHistoryLinearSource_value q (nativeTimeSignal signal) (motherHistoryRegular signal smooth) hz hw t nonnegative inside]


/-- The second ordinary coefficient belongs to the actual raw nine-channel family as well. -/
theorem rawMotherOrdinaryRemainder_generated (signal : BasePoint→Field289) (smooth : ContDiff ℝ ∞ signal)
    (t : ℝ) (field : Fin 289) :
    HasDerivAt (deriv (fun a : ℝ=>actualMotherEulerRead (fun point=>a • signal point) (nativeTimePoint t) (Pi.single field 1)))
      (2*nativeOrdinaryRemainder signal t field) 0 := by
  exact (motherOrdinaryRemainder_generated signal smooth t field).congr_of_eventuallyEq
    (nativeHolonomicEuler_raw_near signal (nativeTimePoint t) smooth field).deriv.symm

theorem actualPreparedMotherFirstVariation_raw (q : PhysicalResponsePoint) (signal : BasePoint→Field289)
    (smooth : ContDiff ℝ ∞ signal) (variation : BasePoint→Field289) (t : ℝ)
    (variationSmooth : DifferentiableAt ℝ variation (nativeTimePoint t))
    (inside : signalFirstJet signal (nativeTimePoint t)∈nativeEulerSourceDomain)
    (nondegenerate : Matrix.det (nativePoint signal (nativeTimePoint t)).coframe≠0) :
    actualPreparedMotherFirstVariation q signal smooth variation t=
      (∑ field : Fin 289,Complex.ofReal (variation (nativeTimePoint t) field)*
        actualPreparedRawMotherEuler q signal smooth 1 t field)+
      Complex.ofReal (∑ mu : Fin 4,fieldDirectionalDerivative (nativeVariationFlux signal variation mu) (nativeTimePoint t) mu) := by
  have original:=actualPreparedMotherFirstVariation_euler q signal smooth variation t variationSmooth inside
  have equations (field : Fin 289) : actualPreparedMotherEuler q signal smooth 1 t field=
      actualPreparedRawMotherEuler q signal smooth 1 t field := by
    have domain : signalFirstJet (fun point=> (1 : ℝ) • signal point) (nativeTimePoint t)∈nativeEulerSourceDomain := by
      simpa only [one_smul] using inside
    have nd : Matrix.det (nativePoint (fun point=>(1 : ℝ) • signal point) (nativeTimePoint t)).coframe≠0 := by
      simpa only [one_smul] using nondegenerate
    exact actualPreparedMotherEuler_raw q signal smooth 1 t domain nd field
  simpa only [equations] using original

end LowEnergy.SourcePropagationMotherResidualDirections
