import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceJointSpectralBudget

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentRegularAnchor
open CanonicalGradedSpatialSource PreparationVacuumCurrentSignalOperator PreparationVacuumPropagationPencil
open PreparationVacuumCurrentConstrainedInverse PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback PreparationVacuumPhysicalTailPrice
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open scoped BigOperators Topology
local instance : NormedAlgebra ℝ SourceOp:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] sourceBaseGenerator jointGenerator jointCurrent jointResolvent rawReader noetherReader
  sourceRead responseLeft responseRight factorialBudget rawInitial sourceMaterialMap sourceContactMap

def sourcePairRadius (q : PhysicalResponsePoint) (extra : ℝ) : ℝ:=
  2*(1+‖sourceBaseGenerator (q.p+q.k) q.F‖+‖sourceBaseGenerator q.p q.F‖+extra)

def sourceMaterialPoint (q : PhysicalResponsePoint) (extra : ℝ) : PhysicalResponsePoint:=
  {q with z:=Complex.I*(sourcePairRadius q extra : ℂ),w:=Complex.I*(sourcePairRadius q extra : ℂ)}

theorem sourcePairRadius_positive (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    0<sourcePairRadius q extra :=by
  unfold sourcePairRadius
  positivity

private theorem pair_radius_left (q : PhysicalResponsePoint) (extra : ℝ) :
    sourcePairRadius q extra=sourceMaterialRadius (q.p+q.k) q.F (‖sourceBaseGenerator q.p q.F‖+extra) :=by
  unfold sourcePairRadius sourceMaterialRadius
  ring

private theorem pair_radius_right (q : PhysicalResponsePoint) (extra : ℝ) :
    sourcePairRadius q extra=sourceMaterialRadius q.p q.F (‖sourceBaseGenerator (q.p+q.k) q.F‖+extra) :=by
  unfold sourcePairRadius sourceMaterialRadius
  ring

theorem sourceMaterialPoint_read (q : PhysicalResponsePoint) (extra : ℝ) :
    sourceRead (sourceMaterialPoint q extra)=sourceRead q :=by
  unfold sourceRead responseLeft responseRight sourceMaterialPoint
  rfl

theorem sourceMaterialPoint_left_price (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    ‖jointResolvent ((sourceMaterialPoint q extra).p+(sourceMaterialPoint q extra).k)
      (sourceMaterialPoint q extra).F (sourceMaterialPoint q extra).z 0‖ ≤ 2/sourcePairRadius q extra :=by
  have paid:=sourceMaterialResolvent_price (q.p+q.k) q.F (‖sourceBaseGenerator q.p q.F‖+extra)
    (add_nonneg (norm_nonneg _) nonnegative)
  have label : sourceMaterialSpectrum (q.p+q.k) q.F (‖sourceBaseGenerator q.p q.F‖+extra)=(sourceMaterialPoint q extra).z:=by
    simp only [sourceMaterialSpectrum,sourceMaterialPoint]
    rw [←pair_radius_left]
  rw [label,←pair_radius_left] at paid
  exact paid

theorem sourceMaterialPoint_right_price (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    ‖jointResolvent (sourceMaterialPoint q extra).p (sourceMaterialPoint q extra).F
      (sourceMaterialPoint q extra).w 0‖ ≤ 2/sourcePairRadius q extra :=by
  have paid:=sourceMaterialResolvent_price q.p q.F (‖sourceBaseGenerator (q.p+q.k) q.F‖+extra)
    (add_nonneg (norm_nonneg _) nonnegative)
  have label : sourceMaterialSpectrum q.p q.F (‖sourceBaseGenerator (q.p+q.k) q.F‖+extra)=(sourceMaterialPoint q extra).w:=by
    simp only [sourceMaterialSpectrum,sourceMaterialPoint]
    rw [←pair_radius_right]
  rw [label,←pair_radius_right] at paid
  exact paid

private theorem source_triple_price {A : Type*} [NormedRing A] (L J R : A) (r : ℝ)
    (nonnegative : 0 ≤ r) (left : ‖L‖ ≤ r) (right : ‖R‖ ≤ r) : ‖L*J*R‖ ≤ r^2*‖J‖ :=by
  have inner : ‖L*J‖ ≤ r*‖J‖:=(norm_mul_le L J).trans (mul_le_mul_of_nonneg_right left (norm_nonneg J))
  exact (norm_mul_le (L*J) R).trans
    ((mul_le_mul inner right (norm_nonneg R) (mul_nonneg nonnegative (norm_nonneg J))).trans_eq (by ring))

private theorem sandwich_norm {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (L R : A) :
    ‖ContinuousLinearMap.mulLeftRight ℝ A L R‖ ≤ ‖L‖*‖R‖ :=by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg L) (norm_nonneg R))
  intro X
  rw [ContinuousLinearMap.mulLeftRight_apply]
  exact (norm_mul_le (L*X) R).trans
    (((mul_le_mul_of_nonneg_right (norm_mul_le L X) (norm_nonneg R))).trans_eq (by ring))

def sourceReaderBudget (q : PhysicalResponsePoint) (reader : Field289) : ℝ:=‖rawReader reader q.p q.F 0‖

def sourceMaterialSlopeBudget (q : PhysicalResponsePoint) : ℝ:=
  ‖jointCurrent (q.p+q.k) q.F 0 0‖+‖jointCurrent q.p q.F 0 0‖

def sourceContactBudget (q : PhysicalResponsePoint) (reader : Field289) : ℝ:=
  ‖fderiv ℝ (noetherReader reader q.p q.F) 0‖

theorem sourceRawInitial_materialPrice (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra)
    (reader : Field289) :
    ‖rawInitial (sourceMaterialPoint q extra) reader‖ ≤
      (4/(sourcePairRadius q extra)^2)*sourceReaderBudget q reader :=by
  have positive:=sourcePairRadius_positive q extra nonnegative
  have generated:=source_triple_price
    (jointResolvent (q.p+q.k) q.F (sourceMaterialPoint q extra).z 0)
    (rawReader reader q.p q.F 0)
    (jointResolvent q.p q.F (sourceMaterialPoint q extra).w 0)
    (2/sourcePairRadius q extra) (by positivity)
    (sourceMaterialPoint_left_price q extra nonnegative) (sourceMaterialPoint_right_price q extra nonnegative)
  unfold rawInitial sourceReaderBudget
  exact generated.trans_eq (by congr 1;ring)

theorem sourceContactMap_materialPrice (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra)
    (reader : Field289) :
    ‖sourceContactMap (sourceMaterialPoint q extra) reader‖ ≤
      (4/(sourcePairRadius q extra)^2)*sourceContactBudget q reader :=by
  have positive:=sourcePairRadius_positive q extra nonnegative
  have left:=sourceMaterialPoint_left_price q extra nonnegative
  have right:=sourceMaterialPoint_right_price q extra nonnegative
  have pair:=sandwich_norm
    (jointResolvent (q.p+q.k) q.F (sourceMaterialPoint q extra).z 0)
    (jointResolvent q.p q.F (sourceMaterialPoint q extra).w 0)
  have bounded : ‖ContinuousLinearMap.mulLeftRight ℝ SourceOp
      (jointResolvent (q.p+q.k) q.F (sourceMaterialPoint q extra).z 0)
      (jointResolvent q.p q.F (sourceMaterialPoint q extra).w 0)‖ ≤ 4/(sourcePairRadius q extra)^2:=
    pair.trans ((mul_le_mul left right (norm_nonneg _) (by positivity)).trans_eq (by ring))
  unfold sourceContactMap
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right bounded (norm_nonneg _))



theorem sourceMaterialMap_materialPrice (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra)
    (reader : Field289) :
    ‖sourceMaterialMap (sourceMaterialPoint q extra) reader‖ ≤
      (8/(sourcePairRadius q extra)^3)*sourceReaderBudget q reader*sourceMaterialSlopeBudget q :=by
  have positive:=sourcePairRadius_positive q extra nonnegative
  let L:=jointResolvent (q.p+q.k) q.F (sourceMaterialPoint q extra).z 0
  let R:=jointResolvent q.p q.F (sourceMaterialPoint q extra).w 0
  let J:=rawReader reader q.p q.F 0
  let r:=2/sourcePairRadius q extra
  have rn : 0 ≤ r:=by dsimp only [r];positivity
  have left : ‖L‖ ≤ r:=sourceMaterialPoint_left_price q extra nonnegative
  have right : ‖R‖ ≤ r:=sourceMaterialPoint_right_price q extra nonnegative
  have triple:=source_triple_price L J R r rn left right
  apply (sourceMaterialMap (sourceMaterialPoint q extra) reader).opNorm_le_bound (by
    unfold sourceReaderBudget sourceMaterialSlopeBudget
    positivity)
  intro force
  have cL : jointCurrent (q.p+q.k) q.F (sourceMaterialPoint q extra).z 0 force=
      jointCurrent (q.p+q.k) q.F 0 0 force:=
    (jointCurrent_source force (q.p+q.k) q.F _).trans (jointCurrent_source force (q.p+q.k) q.F 0).symm
  have cR : jointCurrent q.p q.F (sourceMaterialPoint q extra).w 0 force=jointCurrent q.p q.F 0 0 force:=
    (jointCurrent_source force q.p q.F _).trans (jointCurrent_source force q.p q.F 0).symm
  have value : sourceMaterialMap (sourceMaterialPoint q extra) reader force=
      (-L)*jointCurrent (q.p+q.k) q.F 0 0 force*(L*J*R)+
        (L*J*R)*jointCurrent q.p q.F 0 0 force*(-R) :=by
    simp only [sourceMaterialMap,sourceMaterialPoint,add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mulLeftRight_apply]
    simp only [sourceMaterialPoint] at cL cR
    rw [cL,cR]
    rfl
  have leftTerm : ‖(-L)*jointCurrent (q.p+q.k) q.F 0 0 force*(L*J*R)‖ ≤
      r^3*‖J‖*‖jointCurrent (q.p+q.k) q.F 0 0‖*‖force‖:=by
    have current:=(jointCurrent (q.p+q.k) q.F 0 0).le_opNorm force
    have inner : ‖(-L)*jointCurrent (q.p+q.k) q.F 0 0 force‖ ≤ r*(‖jointCurrent (q.p+q.k) q.F 0 0‖*‖force‖):=
      (norm_mul_le _ _).trans (mul_le_mul (by simpa only [norm_neg] using left) current (norm_nonneg _) rn)
    exact (norm_mul_le _ _).trans
      ((mul_le_mul inner triple (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have rightTerm : ‖(L*J*R)*jointCurrent q.p q.F 0 0 force*(-R)‖ ≤
      r^3*‖J‖*‖jointCurrent q.p q.F 0 0‖*‖force‖:=by
    have current:=(jointCurrent q.p q.F 0 0).le_opNorm force
    have inner : ‖(L*J*R)*jointCurrent q.p q.F 0 0 force‖ ≤ (r^2*‖J‖)*(‖jointCurrent q.p q.F 0 0‖*‖force‖):=
      (norm_mul_le _ _).trans (mul_le_mul triple current (norm_nonneg _) (by positivity))
    exact (norm_mul_le _ _).trans
      ((mul_le_mul inner (by simpa only [norm_neg] using right) (norm_nonneg _) (by positivity)).trans_eq (by ring))
  rw [value]
  exact (norm_add_le _ _).trans ((add_le_add leftTerm rightTerm).trans_eq (by
    unfold sourceReaderBudget sourceMaterialSlopeBudget
    dsimp only [r,J]
    ring))

theorem sourceMiddleCoefficient_materialPrice (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra)
    (reader : Field289) :
    sourceMiddleCoefficient (sourceMaterialPoint q extra) reader ≤
      (8/(sourcePairRadius q extra)^3)*sourceReaderBudget q reader*sourceMaterialSlopeBudget q+
        (4/(sourcePairRadius q extra)^2)*sourceContactBudget q reader :=
  add_le_add (sourceMaterialMap_materialPrice q extra nonnegative reader)
    (sourceContactMap_materialPrice q extra nonnegative reader)


theorem sourcePairRadius_one (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    1 ≤ sourcePairRadius q extra :=by
  unfold sourcePairRadius
  have left:=norm_nonneg (sourceBaseGenerator (q.p+q.k) q.F)
  have right:=norm_nonneg (sourceBaseGenerator q.p q.F)
  linarith

def sourceLinearBudget (q : PhysicalResponsePoint) (reader : Field289) (eta : ℝ) : ℝ:=
  4*sourceReaderBudget q reader*
    (factorialBudget q.p q.F eta*sourceDualCoefficient q eta+
      factorialBudget (q.p+q.k) q.F eta*sourcePrimalCoefficient q eta)

def sourceConstantBudget (q : PhysicalResponsePoint) (reader : Field289) (eta : ℝ) : ℝ:=
  factorialBudget (q.p+q.k) q.F eta*factorialBudget q.p q.F eta*
    (8*sourceReaderBudget q reader*sourceMaterialSlopeBudget q+4*sourceContactBudget q reader)

private theorem price_radius_reduction (radius A B : ℝ) (positive : 0<radius) (large : 1 ≤ radius)
    (nonnegativeA : 0 ≤ A) (_nonnegativeB : 0 ≤ B) :
    8/radius^3*A+4/radius^2*B ≤ (8*A+4*B)/radius^2 :=by
  have order : radius^2 ≤ radius^3:=by nlinarith [sq_nonneg radius]
  have inverse : 8/radius^3 ≤ 8/radius^2:=div_le_div_of_nonneg_left (by norm_num) (by positivity) order
  have generated:=mul_le_mul_of_nonneg_right inverse nonnegativeA
  calc
    _ ≤ 8/radius^2*A+4/radius^2*B:=add_le_add generated (le_refl (4/radius^2*B))
    _=_:=by ring

theorem sourceHistoryLinearCoefficient_materialPrice (q : PhysicalResponsePoint) (extra : ℝ)
    (nonnegative : 0 ≤ extra) (reader : Field289) (eta : ℝ) (positive : 0<eta) :
    sourceHistoryLinearCoefficient (sourceMaterialPoint q extra) reader eta ≤
      sourceLinearBudget q reader eta/(sourcePairRadius q extra)^2 :=by
  have left:=factorialBudget_nonnegative q.p q.F eta positive
  have right:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have pair : 0 ≤ factorialBudget q.p q.F eta*sourceDualCoefficient q eta+
      factorialBudget (q.p+q.k) q.F eta*sourcePrimalCoefficient q eta:=by
    unfold sourceDualCoefficient sourcePrimalCoefficient
    positivity
  have source:=mul_le_mul_of_nonneg_right (sourceRawInitial_materialPrice q extra nonnegative reader) pair
  exact source.trans_eq (by unfold sourceLinearBudget;ring)

theorem sourceHistoryConstantCoefficient_materialPrice (q : PhysicalResponsePoint) (extra : ℝ)
    (nonnegative : 0 ≤ extra) (reader : Field289) (eta : ℝ) (positive : 0<eta) :
    sourceHistoryConstantCoefficient (sourceMaterialPoint q extra) reader eta ≤
      sourceConstantBudget q reader eta/(sourcePairRadius q extra)^2 :=by
  have left:=factorialBudget_nonnegative q.p q.F eta positive
  have right:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have source:=mul_le_mul_of_nonneg_left (sourceMiddleCoefficient_materialPrice q extra nonnegative reader)
    (mul_nonneg right left)
  have row:=price_radius_reduction (sourcePairRadius q extra)
    (sourceReaderBudget q reader*sourceMaterialSlopeBudget q) (sourceContactBudget q reader)
    (sourcePairRadius_positive q extra nonnegative) (sourcePairRadius_one q extra nonnegative)
    (by unfold sourceReaderBudget sourceMaterialSlopeBudget;positivity) (by unfold sourceContactBudget;positivity)
  have reduced:=mul_le_mul_of_nonneg_left row (mul_nonneg right left)
  have middle : sourceHistoryConstantCoefficient (sourceMaterialPoint q extra) reader eta ≤
      (factorialBudget (q.p+q.k) q.F eta*factorialBudget q.p q.F eta)*
        ((8*(sourceReaderBudget q reader*sourceMaterialSlopeBudget q)+4*sourceContactBudget q reader)/(sourcePairRadius q extra)^2) :=by
    apply source.trans
    convert! reduced using 1
    ring
  exact middle.trans_eq (by unfold sourceConstantBudget;ring)


def sourceWholeLinearBudget (q : PhysicalResponsePoint) (eta : ℝ) : ℝ:=
  ‖sourceRead q‖*(∑row : Fin 289,sourceLinearBudget q (fieldUnit row) eta)

def sourceWholeConstantBudget (q : PhysicalResponsePoint) (eta : ℝ) : ℝ:=
  ‖sourceRead q‖*(∑row : Fin 289,sourceConstantBudget q (fieldUnit row) eta)

theorem sourceWholeLinearBudget_materialPrice (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra)
    (eta : ℝ) (positive : 0<eta) :
    sourceCurrentLinearCoefficient (sourceMaterialPoint q extra) eta ≤
      sourceWholeLinearBudget q eta/(sourcePairRadius q extra)^2 :=by
  have summed:=Finset.sum_le_sum (fun row (_ : row∈Finset.univ)=>
    sourceHistoryLinearCoefficient_materialPrice q extra nonnegative (fieldUnit row) eta positive)
  rw [←Finset.sum_div] at summed
  have actual:=mul_le_mul_of_nonneg_left summed (norm_nonneg (sourceRead q))
  unfold sourceCurrentLinearCoefficient
  rw [sourceMaterialPoint_read]
  exact actual.trans_eq (by unfold sourceWholeLinearBudget;ring)

theorem sourceWholeConstantBudget_materialPrice (q : PhysicalResponsePoint) (extra : ℝ) (nonnegative : 0 ≤ extra)
    (eta : ℝ) (positive : 0<eta) :
    sourceCurrentConstantCoefficient (sourceMaterialPoint q extra) eta ≤
      sourceWholeConstantBudget q eta/(sourcePairRadius q extra)^2 :=by
  have summed:=Finset.sum_le_sum (fun row (_ : row∈Finset.univ)=>
    sourceHistoryConstantCoefficient_materialPrice q extra nonnegative (fieldUnit row) eta positive)
  rw [←Finset.sum_div] at summed
  have actual:=mul_le_mul_of_nonneg_left summed (norm_nonneg (sourceRead q))
  unfold sourceCurrentConstantCoefficient
  rw [sourceMaterialPoint_read]
  exact actual.trans_eq (by unfold sourceWholeConstantBudget;ring)

end LowEnergy.PreparationVacuumCurrentRegularAnchor
