import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalHistoryConjugation

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumOrderedRealSignal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumOriginalDensity PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open CanonicalPreparationCore.Completed GaussComposite.SourceGraph
open PreparationVacuumSourceFieldFamily PreparationVacuumFullFieldRiesz
open Filter Set
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Operator:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] historyConjugation conjugatedOperator jointGenerator jointResolvent noetherReader noetherReaderContact

private def conjugationAlgebra : Operator→ₐ[ℝ] Operator where
  toFun:=conjugatedOperator
  map_one':=conjugatedOperator_one
  map_mul':=conjugatedOperator_mul
  map_zero':=map_zero conjugationMap
  map_add':=conjugatedOperator_add
  commutes' r:=by
    rw [Algebra.algebraMap_eq_smul_one]
    change conjugationMap (r • (1:Operator))=r • (1:Operator)
    rw [map_smul]
    change r • conjugatedOperator (1:Operator)=_
    rw [conjugatedOperator_one]

private theorem conjugatedOperator_sub (A B : Operator) :
    conjugatedOperator (A-B)=conjugatedOperator A-conjugatedOperator B :=
  map_sub conjugationMap A B

private theorem conjugatedSpectral_sub (A : Operator) (z : ℂ) :
    conjugatedOperator (A-z • (1:Operator))=conjugatedOperator A-star z • (1:Operator) :=by
  rw [conjugatedOperator_sub,conjugatedOperator_smul,conjugatedOperator_one]

def conjugatedGenerator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (h : Field289) : Operator:=
  conjugatedOperator (jointGenerator p F z h)

theorem conjugatedGenerator_spectral (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (h : Field289) :
    conjugatedGenerator p F z h=conjugatedGenerator p F 0 h-star z • (1:Operator) :=by
  have original : jointGenerator p F z h=jointGenerator p F 0 h-z • (1:Operator):=by
    unfold jointGenerator
    have zero : (0:ℂ) • (1:Operator)=0:=by apply ContinuousLinearMap.ext;intro v;exact zero_smul ℂ v
    rw [zero,sub_zero]
  exact (congrArg conjugatedOperator original).trans (conjugatedSpectral_sub (jointGenerator p F 0 h) z)

def conjugatedResolvent (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (h : Field289) : Operator:=
  conjugatedOperator (jointResolvent p F z h)

def conjugatedTime (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (age : ℝ) (h : Field289) : Operator:=
  NormedSpace.exp (age • (Complex.I • conjugatedGenerator p F 0 h))

theorem conjugatedTime_source (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (age : ℝ) (h : Field289) :
    conjugatedTime p F age h=conjugatedOperator (physicalTime p F age h) :=by
  unfold physicalTime SourceFiniteUnitary.time conjugatedTime conjugatedGenerator
  have source:=NormedSpace.map_exp conjugationAlgebra conjugationMap.continuous
    (age • ((-Complex.I) • jointGenerator p F 0 h))
  change conjugatedOperator (NormedSpace.exp _)=NormedSpace.exp _ at source
  rw [source]
  apply congrArg NormedSpace.exp
  change _=conjugationMap (age • ((-Complex.I) • jointGenerator p F 0 h))
  rw [map_smul]
  change _=age • conjugatedOperator ((-Complex.I) • jointGenerator p F 0 h)
  rw [conjugatedOperator_smul]
  simp only [star_neg,Complex.star_def,Complex.conj_I,neg_neg]

theorem conjugatedTime_inverse (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (age : ℝ) (h : Field289) :
    conjugatedTime p F (-age) h*conjugatedTime p F age h=1 ∧
      conjugatedTime p F age h*conjugatedTime p F (-age) h=1 :=by
  rw [conjugatedTime_source,conjugatedTime_source]
  constructor
  · rw [←conjugatedOperator_mul,(physicalTime_inverse p F age h).1,conjugatedOperator_one]
  · rw [←conjugatedOperator_mul,(physicalTime_inverse p F age h).2,conjugatedOperator_one]

theorem conjugatedTime_initial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    conjugatedTime p F 0 h=1 :=by
  rw [conjugatedTime_source,physicalTime_initial,conjugatedOperator_one]

theorem conjugatedResolvent_source (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0) :
    conjugatedGenerator p F z 0*conjugatedResolvent p F z 0=1 ∧
      conjugatedResolvent p F z 0*conjugatedGenerator p F z 0=1 :=by
  unfold conjugatedGenerator conjugatedResolvent
  rw [←conjugatedOperator_mul,←conjugatedOperator_mul]
  have unit:=jointGenerator_unit p F z hz
  unfold jointResolvent
  rw [Ring.mul_inverse_cancel _ unit,Ring.inverse_mul_cancel _ unit,conjugatedOperator_one]
  exact ⟨rfl,rfl⟩

/-- Coordinates of the other original ordered signal; conjugation is paid separately. -/
def oppositeCoordinates (q : PhysicalResponsePoint) : PhysicalResponsePoint:=
  {q with
    p := -q.p
    k := -q.k
    z := q.w
    w := q.z
    left := q.right
    right := q.left
    lc := q.rc
    ls := q.rs
    rc := q.lc
    rs := q.ls}

theorem opposite_left_momentum (q : PhysicalResponsePoint) :
    (oppositeCoordinates q).p+(oppositeCoordinates q).k= -(q.p+q.k) :=by
  change -q.p + -q.k= -(q.p+q.k)
  abel

theorem opposite_source_legs (q : PhysicalResponsePoint) :
    responseLeft (oppositeCoordinates q)=responseRight q ∧
      responseRight (oppositeCoordinates q)=responseLeft q :=⟨rfl,rfl⟩

def oppositeKernel (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : Operator:=
  physicalTime (-(q.p+q.k)) q.F (-age) h*jointResolvent (-(q.p+q.k)) q.F q.w h*
    noetherReader reader (-q.p) q.F h*jointResolvent (-q.p) q.F q.z h*physicalTime (-q.p) q.F age h

def conjugatedOppositeKernel (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : Operator:=
  conjugatedTime (-(q.p+q.k)) q.F (-age) h*conjugatedResolvent (-(q.p+q.k)) q.F q.w h*
    conjugatedOperator (noetherReader reader (-q.p) q.F h)*conjugatedResolvent (-q.p) q.F q.z h*
      conjugatedTime (-q.p) q.F age h

theorem oppositeKernel_conjugated (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    conjugatedOppositeKernel q reader h age=conjugatedOperator (oppositeKernel q reader h age) :=by
  unfold conjugatedOppositeKernel oppositeKernel conjugatedResolvent
  simp only [conjugatedTime_source,conjugatedOperator_mul]

def oppositeCurrent (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  inner ℂ (responseRight q) (oppositeKernel q reader h age (responseLeft q))

theorem oppositeCurrent_actual (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    oppositeCurrent q reader h age=noetherPreparedCurrent (oppositeCoordinates q) reader h age :=by
  unfold noetherPreparedCurrent preparedDual independentDual preparedPrimal
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,mul_apply_eq_comp]
  rw [opposite_left_momentum]
  rfl

def conjugatedOppositeCurrent (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  inner ℂ (historyConjugation (responseRight q))
    (conjugatedOppositeKernel q reader h age (historyConjugation (responseLeft q)))

theorem conjugatedOppositeCurrent_source (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    conjugatedOppositeCurrent q reader h age=star (oppositeCurrent q reader h age) :=by
  rw [conjugatedOppositeCurrent,oppositeKernel_conjugated,conjugatedOperator_pair]
  rfl

def conjugatedOppositeSlope (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ) : ℂ:=
  star (noetherPreparedSlope (oppositeCoordinates q) reader force age)

theorem conjugatedOppositeCurrent_generated (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>conjugatedOppositeCurrent q reader (r • force) age)
      (conjugatedOppositeSlope q reader force age) 0 :=by
  have generated:=Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (noetherPreparedCurrent_generated (oppositeCoordinates q) reader force age hw hz)
  convert! generated using 1
  all_goals simp only [conjugatedOppositeCurrent_source,oppositeCurrent_actual,conjugatedOppositeSlope,
    Function.comp_apply,Complex.conjCLE_apply,←Complex.star_def]
  all_goals funext r;rfl

def conjugatedOppositeDual (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) : H→L[ℂ] ℂ:=
  (innerSL ℂ (historyConjugation (responseRight q))).comp
    (conjugatedTime (-(q.p+q.k)) q.F (-age) h*conjugatedResolvent (-(q.p+q.k)) q.F q.w h)

def conjugatedOppositePrimal (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) : H:=
  conjugatedResolvent (-q.p) q.F q.z h (conjugatedTime (-q.p) q.F age h (historyConjugation (responseLeft q)))

theorem conjugatedOppositeDual_source (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) (v : H) :
    conjugatedOppositeDual q h age (historyConjugation v)=
      star (preparedDual (oppositeCoordinates q) h age v) :=by
  unfold conjugatedOppositeDual
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,conjugatedTime_source,conjugatedResolvent,
    ←conjugatedOperator_mul]
  rw [conjugatedOperator_pair]
  unfold preparedDual independentDual
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,mul_apply_eq_comp]
  rw [opposite_left_momentum]
  rfl

theorem conjugatedOppositePrimal_source (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) :
    conjugatedOppositePrimal q h age=historyConjugation (preparedPrimal (oppositeCoordinates q) h age) :=by
  unfold conjugatedOppositePrimal preparedPrimal
  simp only [conjugatedTime_source,conjugatedResolvent,conjugatedOperator_apply,historyConjugation_twice]
  rfl

theorem conjugatedOppositeCurrent_initial (q : PhysicalResponsePoint) (reader h : Field289) :
    conjugatedOppositeCurrent q reader h 0=
      inner ℂ (historyConjugation (responseRight q))
        ((conjugatedResolvent (-(q.p+q.k)) q.F q.w h*conjugatedOperator (noetherReader reader (-q.p) q.F h)*
          conjugatedResolvent (-q.p) q.F q.z h) (historyConjugation (responseLeft q))) :=by
  simp only [conjugatedOppositeCurrent,conjugatedOppositeKernel,neg_zero,conjugatedTime_initial,one_mul,mul_one]

end LowEnergy.PreparationVacuumOrderedRealSignal
