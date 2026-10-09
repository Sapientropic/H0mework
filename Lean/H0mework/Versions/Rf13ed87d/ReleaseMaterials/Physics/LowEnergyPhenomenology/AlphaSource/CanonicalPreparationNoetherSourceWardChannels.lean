import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNoetherCurrentTimeBalance

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherOrdinaryWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumOriginalDensity PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open PreparationVacuumOrderedRealSignal PreparationVacuumOriginalGreenFeedback
open PreparationVacuumSourceFieldFamily PreparationVacuumFullFieldRiesz PreparationVacuumGaugeSourceInjection
open Filter Set
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _
attribute [local irreducible] jointGenerator jointResolvent physicalTime preparedDual preparedPrimal
  noetherReader noetherReaderContact rawReader rawReaderContact noetherPreparedCurrent noetherPreparedSlope

/-- Both endpoints are the original inverse-time and primal source, including their two resolvents. -/
def preparedTimeJet (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) : SourceJet ℂ:=
  pairJet (responseLeft q) (responseRight q)
    (PreparationVacuumPhysicalFeedback.rawKernelJet reader q.p q.k q.F q.z q.w 0 t)

theorem preparedTimeJets_generated (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) :
    HasSourceJets (preparedTimeJet q reader) t:=
  pairJets_generated _ _ _ _ (PreparationVacuumPhysicalFeedback.rawKernelJet_generated _ _ _ _ _ _ _ _)

theorem preparedTimeJet_value (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) :
    (preparedTimeJet q reader t).value=noetherPreparedCurrent q reader 0 t :=by
  rw [noetherPreparedCurrent_source,densityRead_actual]
  simp only [preparedTimeJet,pairJet,PreparationVacuumPhysicalFeedback.rawKernelJet_value,
    rawPrepared,responseLeft,responseRight]

theorem preparedTimeJet_first (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    (preparedTimeJet q reader t).first=noetherTimeCurrent q reader t :=by
  have source:=(preparedTimeJets_generated q reader t).1
  simp only [preparedTimeJet_value] at source
  exact source.unique (noetherPreparedCurrent_time q reader t hz hw)

/-- The fixed-pi field derivative changes the contact inside the same five factors. -/
def correctedContactJet (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) : SourceJet Operator:=
  jetMul (jetMul (jetMul (jetMul (physicalTimeJet (q.p+q.k) q.F 0 (-1) 0 t)
    (jetConst (jointResolvent (q.p+q.k) q.F q.z 0)))
      (jetConst (noetherReaderContact reader force q.p q.F-rawReaderContact reader force q.p q.F)))
        (jetConst (jointResolvent q.p q.F q.w 0))) (physicalTimeJet q.p q.F 0 1 0 t)

theorem correctedContactJets_generated (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) :
    HasSourceJets (correctedContactJet q reader force) t:=
  productJets _ _ t (productJets _ _ t (productJets _ _ t (productJets _ _ t
    (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
      (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)

def preparedSlopeTimeJet (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) : SourceJet ℂ:=
  pairJet (responseLeft q) (responseRight q)
    (addJet (slopeKernelJet reader force q.p q.k q.F q.z q.w t) (correctedContactJet q reader force t))

theorem preparedSlopeTimeJets_generated (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) :
    HasSourceJets (preparedSlopeTimeJet q reader force) t:=
  pairJets_generated _ _ _ _ (sumJets _ _ t (slopeKernelJet_generated _ _ _ _ _ _ _ _) (correctedContactJets_generated _ _ _ _))

theorem preparedSlopeTimeJet_value (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) :
    (preparedSlopeTimeJet q reader force t).value=noetherPreparedSlope q reader force t :=by
  rw [noetherPreparedSlope,densitySlope_actual]
  simp only [preparedSlopeTimeJet,pairJet,addJet,slopeKernelJet_value,correctedContactJet,jetMul,jetConst,
    physicalTimeJet,timeJet,neg_one_mul,one_mul,add_zero,rawPreparedSlope,responseLeft,responseRight,
    preparedDual,independentDual,preparedPrimal,physicalTime,sub_apply,add_apply,mul_apply_eq_comp,
    map_sub,inner_add_right,inner_sub_right,ContinuousLinearMap.comp_apply,innerSL_apply_apply]
  abel

def branchTimeJet (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool) (t : ℝ) : SourceJet ℂ:=
  if response then preparedSlopeTimeJet q reader force t else preparedTimeJet q reader t

theorem branchTimeJets_generated (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool) (t : ℝ) :
    HasSourceJets (branchTimeJet q reader force response) t:=by
  cases response
  · exact preparedTimeJets_generated _ _ _
  · exact preparedSlopeTimeJets_generated _ _ _ _

private def scalarHalfJet (a b : SourceJet ℂ) : SourceJet ℂ:=
  ⟨(1/2:ℂ)*(a.value+star b.value),(1/2:ℂ)*(a.first+star b.first),(1/2:ℂ)*(a.second+star b.second)⟩

private theorem star_derivative {f : ℝ→ℂ} {d : ℂ} {r : ℝ} (source : HasDerivAt f d r) :
    HasDerivAt (fun s=>star (f s)) (star d) r :=by
  have generated:=Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r source
  convert! generated using 1

private theorem scalarHalfJets_generated (a b : ℝ→SourceJet ℂ) (t : ℝ)
    (ha : HasSourceJets a t) (hb : HasSourceJets b t) :
    HasSourceJets (fun r=>scalarHalfJet (a r) (b r)) t:=
  ⟨(ha.1.add (star_derivative hb.1)).const_mul (1/2:ℂ),(ha.2.add (star_derivative hb.2)).const_mul (1/2:ℂ)⟩

private def atMode (key momentum : PhysicalMomentum) (a : SourceJet ℂ) : SourceJet ℂ:=
  if key=momentum then a else ⟨0,0,0⟩
private theorem atMode_value (key momentum : PhysicalMomentum) (a : SourceJet ℂ) :
    (atMode key momentum a).value=if key=momentum then a.value else 0 :=by
  by_cases same : key=momentum
  · simp only [atMode,if_pos same]
  · simp only [atMode,if_neg same]
private theorem atMode_first (key momentum : PhysicalMomentum) (a : SourceJet ℂ) :
    (atMode key momentum a).first=if key=momentum then a.first else 0 :=by
  by_cases same : key=momentum
  · simp only [atMode,if_pos same]
  · simp only [atMode,if_neg same]

private def plusJet (a b : SourceJet ℂ) : SourceJet ℂ:=
  ⟨a.value+b.value,a.first+b.first,a.second+b.second⟩

private theorem atMode_generated (key momentum : PhysicalMomentum) (a : ℝ→SourceJet ℂ) (t : ℝ)
    (source : HasSourceJets a t) : HasSourceJets (fun r=>atMode key momentum (a r)) t :=by
  by_cases same : key=momentum
  · simpa only [atMode,if_pos same] using source
  · simp only [atMode,if_neg same,HasSourceJets]
    exact ⟨hasDerivAt_const _ _,hasDerivAt_const _ _⟩

private theorem plusJets_generated (a b : ℝ→SourceJet ℂ) (t : ℝ)
    (ha : HasSourceJets a t) (hb : HasSourceJets b t) :
    HasSourceJets (fun r=>plusJet (a r) (b r)) t:=⟨ha.1.add hb.1,ha.2.add hb.2⟩

/-- Coincident physical modes are added, including both cross terms and zero harmonics. -/
def realCoefficientJet (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool)
    (t : ℝ) (momentum : PhysicalMomentum) : SourceJet ℂ:=
  let F:=branchTimeJet q reader force response t
  let R:=branchTimeJet (oppositeCoordinates q) reader force response t
  let DR:=branchTimeJet (crossRightCoordinates q) reader force response t
  let DL:=branchTimeJet (crossLeftCoordinates q) reader force response t
  plusJet (plusJet (plusJet (atMode (-q.k) momentum (scalarHalfJet F R))
    (atMode q.k momentum (scalarHalfJet R F)))
    (atMode (2 • q.p+q.k) momentum (scalarHalfJet DR DL)))
    (atMode (-(2 • q.p+q.k)) momentum (scalarHalfJet DL DR))

theorem realCoefficientJets_generated (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool)
    (t : ℝ) (momentum : PhysicalMomentum) :
    HasSourceJets (fun r=>realCoefficientJet q reader force response r momentum) t:=by
  have F:=branchTimeJets_generated q reader force response t
  have R:=branchTimeJets_generated (oppositeCoordinates q) reader force response t
  have DR:=branchTimeJets_generated (crossRightCoordinates q) reader force response t
  have DL:=branchTimeJets_generated (crossLeftCoordinates q) reader force response t
  exact plusJets_generated _ _ t (plusJets_generated _ _ t (plusJets_generated _ _ t
    (atMode_generated _ _ _ _ (scalarHalfJets_generated _ _ t F R))
    (atMode_generated _ _ _ _ (scalarHalfJets_generated _ _ t R F)))
    (atMode_generated _ _ _ _ (scalarHalfJets_generated _ _ t DR DL)))
    (atMode_generated _ _ _ _ (scalarHalfJets_generated _ _ t DL DR))

theorem realCoefficientJet_value (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool)
    (t : ℝ) (momentum : PhysicalMomentum) :
    (realCoefficientJet q reader force response t momentum).value=
      if response then coefficientSlope q reader force t momentum else realDensityCoefficients q reader 0 t momentum :=by
  cases response <;>
    simp only [realCoefficientJet,branchTimeJet,Bool.false_eq_true,↓reduceIte,plusJet,atMode_value,scalarHalfJet,
      preparedTimeJet_value,preparedSlopeTimeJet_value,coefficientSlope,realDensityCoefficients,Finsupp.add_apply,
      Finsupp.single_apply,oppositeCurrent_actual,crossRight_actual,crossLeft_actual]

def realTimeCoefficients (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) : MomentumCoefficients:=
  let F:=noetherTimeCurrent q reader t
  let R:=noetherTimeCurrent (oppositeCoordinates q) reader t
  let DR:=noetherTimeCurrent (crossRightCoordinates q) reader t
  let DL:=noetherTimeCurrent (crossLeftCoordinates q) reader t
  Finsupp.single (-q.k) ((1/2:ℂ)*(F+star R))+Finsupp.single q.k ((1/2:ℂ)*(R+star F))+
    Finsupp.single (2 • q.p+q.k) ((1/2:ℂ)*(DR+star DL))+
      Finsupp.single (-(2 • q.p+q.k)) ((1/2:ℂ)*(DL+star DR))

theorem realCoefficientJet_first (q : PhysicalResponsePoint) (reader force : Field289)
    (t : ℝ) (momentum : PhysicalMomentum) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    (realCoefficientJet q reader force false t momentum).first=realTimeCoefficients q reader t momentum :=by
  simp only [realCoefficientJet,branchTimeJet,Bool.false_eq_true,↓reduceIte,plusJet,atMode_first,scalarHalfJet,
    realTimeCoefficients,Finsupp.add_apply,Finsupp.single_apply]
  rw [preparedTimeJet_first q reader t hz hw,
    preparedTimeJet_first (oppositeCoordinates q) reader t hw hz,
    preparedTimeJet_first (crossRightCoordinates q) reader t hw hw,
    preparedTimeJet_first (crossLeftCoordinates q) reader t hz hz]

theorem preparedTimeJets_continuous (q : PhysicalResponsePoint) (reader : Field289) :
    ContinuousJets (preparedTimeJet q reader):=
  pairJets_continuous q _ (rawKernelJets_continuous _ _ _ _ _ _ _)

theorem correctedContactJets_continuous (q : PhysicalResponsePoint) (reader force : Field289) :
    ContinuousJets (correctedContactJet q reader force):=
  productJets_continuous _ _ (productJets_continuous _ _ (productJets_continuous _ _ (productJets_continuous _ _
    (physicalTimeJets_continuous _ _ _ _ _) (constantJets_continuous _)) (constantJets_continuous _))
      (constantJets_continuous _)) (physicalTimeJets_continuous _ _ _ _ _)

theorem preparedSlopeTimeJets_continuous (q : PhysicalResponsePoint) (reader force : Field289) :
    ContinuousJets (preparedSlopeTimeJet q reader force):=
  pairJets_continuous q _ (sumJets_continuous _ _ (slopeKernelJets_continuous _ _ _ _ _ _ _)
    (correctedContactJets_continuous _ _ _))

theorem branchTimeJets_continuous (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool) :
    ContinuousJets (branchTimeJet q reader force response):=by
  cases response
  · exact preparedTimeJets_continuous _ _
  · exact preparedSlopeTimeJets_continuous _ _ _

private theorem scalarHalfJets_continuous (a b : ℝ→SourceJet ℂ)
    (ha : ContinuousJets a) (hb : ContinuousJets b) :
    ContinuousJets (fun r=>scalarHalfJet (a r) (b r)):=
  ⟨(ha.1.add (Complex.conjCLE.continuous.comp hb.1)).const_mul _,
    (ha.2.1.add (Complex.conjCLE.continuous.comp hb.2.1)).const_mul _,
    (ha.2.2.add (Complex.conjCLE.continuous.comp hb.2.2)).const_mul _⟩

private theorem atMode_continuous (key momentum : PhysicalMomentum) (a : ℝ→SourceJet ℂ)
    (source : ContinuousJets a) : ContinuousJets (fun r=>atMode key momentum (a r)) :=by
  by_cases same : key=momentum
  · simpa only [atMode,if_pos same] using source
  · simp only [atMode,if_neg same,ContinuousJets]
    exact ⟨continuous_const,continuous_const,continuous_const⟩

private theorem plusJets_continuous (a b : ℝ→SourceJet ℂ)
    (ha : ContinuousJets a) (hb : ContinuousJets b) :
    ContinuousJets (fun r=>plusJet (a r) (b r)):=⟨ha.1.add hb.1,ha.2.1.add hb.2.1,ha.2.2.add hb.2.2⟩

theorem realCoefficientJets_continuous (q : PhysicalResponsePoint) (reader force : Field289) (response : Bool)
    (momentum : PhysicalMomentum) : ContinuousJets (fun r=>realCoefficientJet q reader force response r momentum) :=by
  have F:=branchTimeJets_continuous q reader force response
  have R:=branchTimeJets_continuous (oppositeCoordinates q) reader force response
  have DR:=branchTimeJets_continuous (crossRightCoordinates q) reader force response
  have DL:=branchTimeJets_continuous (crossLeftCoordinates q) reader force response
  exact plusJets_continuous _ _ (plusJets_continuous _ _ (plusJets_continuous _ _
    (atMode_continuous _ _ _ (scalarHalfJets_continuous _ _ F R))
    (atMode_continuous _ _ _ (scalarHalfJets_continuous _ _ R F)))
    (atMode_continuous _ _ _ (scalarHalfJets_continuous _ _ DR DL)))
    (atMode_continuous _ _ _ (scalarHalfJets_continuous _ _ DL DR))

/-- The complete all289 source sign is taken once after the original real-density assembly. -/
def realEulerTimeJet (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (t : ℝ) (momentum : PhysicalMomentum) (i : Fin 289) : SourceJet ℂ:=
  negativeJet (realCoefficientJet q (PreparationVacuumActionFieldLift.fieldUnit i) force response t momentum)

theorem realEulerTimeJets_generated (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (t : ℝ) (momentum : PhysicalMomentum) (i : Fin 289) :
    HasSourceJets (fun r=>realEulerTimeJet q force response r momentum i) t:=
  negativeJets_generated _ _ (realCoefficientJets_generated _ _ _ _ _ _)

theorem realEulerTimeJet_value (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (t : ℝ) (momentum : PhysicalMomentum) (i : Fin 289) :
    (realEulerTimeJet q force response t momentum i).value=
      if response then realEulerSlope q force t momentum i else realEulerCoefficients q 0 t momentum i :=by
  rw [realEulerTimeJet,negativeJet,realCoefficientJet_value]
  cases response <;> rfl

theorem realEulerTimeJets_continuous (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (momentum : PhysicalMomentum) (i : Fin 289) : ContinuousJets (fun r=>realEulerTimeJet q force response r momentum i) :=by
  have source:=realCoefficientJets_continuous q (PreparationVacuumActionFieldLift.fieldUnit i) force response momentum
  exact ⟨source.1.neg,source.2.1.neg,source.2.2.neg⟩

end LowEnergy.PreparationVacuumNoetherOrdinaryWard
