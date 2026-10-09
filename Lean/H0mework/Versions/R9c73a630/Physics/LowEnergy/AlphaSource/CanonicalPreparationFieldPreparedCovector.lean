import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldFormCurrent
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationActionFieldLift

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldCovector
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussFockWeights GaussQuantumMultiplier
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionDecomposition PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceActionJets SourceQuantumScalarChart GaussLiveMomentum
open PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearFieldCurve
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open CanonicalGradedLocalCurrent Filter Set
open GaussUnitaryHistory (Index)
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators Distributions InnerProductSpace Interval
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open GaussCoframeForm GaussDensityCore

open PreparationVacuumFullFieldRiesz PreparationVacuumActionFieldLift
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open MeasureTheory

local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] finiteFull fieldJets sourceProfile

theorem restriction_coordinates (f : Field289) (p : PhysicalMomentum) (F : Index) :
    currentRestriction f p F 0=∑i : Fin 289,(f i:ℂ) • currentRestriction (fieldBasis i) p F 0 :=by
  apply ContinuousLinearMap.ext;intro x
  apply ext_inner_left ℂ;intro y
  simp only [sum_apply,smul_apply,inner_sum,inner_smul_right,currentRestriction_original_pair]
  exact field_first_coordinates f p (sourceTestApprox F y) (sourceTestApprox F x)

theorem vertex_coordinates (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ) :
    currentVertex f p k F n z w=∑i : Fin 289,(f i:ℂ) • currentVertex (fieldBasis i) p k F n z w :=by
  rw [currentVertex,restriction_coordinates]
  simp only [currentVertex,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]

def preparedCovector (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : Fin 289→ℂ :=
  fun i=>preparedCurrent epsilon precision (fieldBasis i) p k F n z w left right a s b t

theorem prepared_covector_source (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    preparedCovector epsilon precision p k F n z w left right a s b t=
      sourceCovector p
        (sourceTestApprox F ((finiteFull (p+k) F n z).adjoint (completedLeg left a s (sourceProfile epsilon precision))))
        (sourceTestApprox F (finiteFull p F n w (completedLeg right b t (sourceProfile epsilon precision)))) :=by
  funext i
  exact preparedCurrent_source epsilon precision (fieldBasis i) p k F n z w left right a s b t

theorem prepared_covector_coordinates (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    preparedCurrent epsilon precision f p k F n z w left right a s b t=
      ∑i : Fin 289,(f i:ℂ)*preparedCovector epsilon precision p k F n z w left right a s b t i :=by
  rw [prepared_covector_source,preparedCurrent_source]
  exact field_first_coordinates f p _ _

theorem prepared_covector_price (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (a s b t : Fin 2) (i : Fin 289) :
    ‖preparedCovector epsilon precision p k F n z w left right a s b t i‖≤
      ‖completedLeg left a s (sourceProfile epsilon precision)‖*
      (normBound n z*currentPrice (fieldBasis i) p F*normBound n w)*
      ‖completedLeg right b t (sourceProfile epsilon precision)‖ :=
  preparedCurrent_price epsilon precision (fieldBasis i) p k F n z w hz hw left right a s b t

theorem curvature_covector (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    curvatureCurrent epsilon precision sourceMomentum row p k F n z w left right a s b t=
      ∑i : Fin 289,((readerReal sourceMomentum row i:ℂ)+Complex.I*(readerImag sourceMomentum row i:ℂ))*
        preparedCovector epsilon precision p k F n z w left right a s b t i :=by
  rw [curvatureCurrent,prepared_covector_coordinates,prepared_covector_coordinates]
  simp only [Finset.mul_sum,add_mul,Finset.sum_add_distrib,mul_assoc]

theorem curvature_covector_derivative (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (curvatureFormCurve epsilon precision sourceMomentum row p k F n z w left right a s b t)
      (∑i : Fin 289,((readerReal sourceMomentum row i:ℂ)+Complex.I*(readerImag sourceMomentum row i:ℂ))*
        preparedCovector epsilon precision p k F n z w left right a s b t i) 0 :=by
  rw [←curvature_covector]
  exact curvatureCurrent_actual_derivative epsilon precision sourceMomentum row p k F n z w left right a s b t

theorem actualFiber_slice (p : PhysicalMomentum) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (actualFiber p) z.val h=quantizer (symbolFirst p (sourceState z.val) (sliceState h)) :=by
  let Q:=quantizer.toContinuousLinearMap.restrictScalars ℝ
  have hs:=((sourceSymbol_smooth p (sourceState z.val) (sourceState_valid z)).comp z.val sourceState_smooth.contDiffAt).differentiableAt (by simp)
  have derivative:=Q.hasFDerivAt.comp z.val hs.hasFDerivAt
  have eq:=congrArg (fun D : SourceCoordinateSlice→L[ℝ] FiberMap=>D h) derivative.fderiv
  change fderiv ℝ (actualFiber p) z.val h=quantizer (fderiv ℝ (fun x=>sourceSymbol p (sourceState x)) z.val h) at eq
  exact eq.trans (congrArg quantizer (coordinate_symbol_first p z h))

theorem mother_current_slice (f : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    fderiv ℝ (actualFiber p) z.val (fieldVector f z.val)+
      quantizer (symbolFirst p (sourceState z.val) (complement f z.val))= -fiberFamily f p z.val :=by
  rw [actualFiber_slice,←map_add,←first_state_split]
  exact symbolFirst_actual f p z

def densityCurrent (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ:=
  ∑word : Occupation,fderiv ℝ (complexDensity word.card) z (fieldVector f z)*star (a z word)*(actualFiber p z (b z)) word

attribute [local irreducible] actualFiber fieldVector sourceState symbolFirst sliceState quantizer complexDensity

lemma weighted_fiber_deriv (D : ℝ→Occupation→ℂ) (A : ℝ→FockFiber) (u : FockFiber)
    (dD : Occupation→ℂ) (dA : FockFiber) (hD : ∀word,HasDerivAt (fun r=>D r word) (dD word) 0)
    (hA : HasDerivAt A dA 0) :
    HasDerivAt (fun r=>∑word : Occupation,D r word*star (u word)*A r word)
      (∑word : Occupation,(dD word*star (u word)*A 0 word+D 0 word*star (u word)*dA word)) 0 :=by
  apply HasDerivAt.fun_sum;intro word _
  let P : FockFiber→L[ℝ] ℂ:=(PiLp.proj (𝕜:=ℂ) 2 (fun _ : Occupation=>ℂ) word).restrictScalars ℝ
  have hp:=P.hasFDerivAt.comp_hasDerivAt 0 hA
  exact ((hD word).mul_const (star (u word))).mul hp

lemma actualFiber_curve_deriv (p : PhysicalMomentum) (z : physicalChart) (h : SourceCoordinateSlice) :
    HasDerivAt (fun r : ℝ=>actualFiber p (z.val+r • h))
      (quantizer (symbolFirst p (sourceState z.val) (sliceState h))) 0 :=by
  have line : HasDerivAt (fun r : ℝ=>z.val+r • h) h 0 :=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const h).const_add z.val using 1
    simp
  have hh:=(actualFiber_smooth p z).differentiableAt (by simp) |>.hasFDerivAt
  have hc : HasFDerivAt (actualFiber p) (fderiv ℝ (actualFiber p) z.val) (z.val+(0:ℝ) • h) :=by
    simpa only [zero_smul,add_zero] using hh
  have generated:=hc.comp_hasDerivAt 0 line
  rw [actualFiber_slice] at generated
  exact generated

lemma fiber_curve_deriv (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>fiberSample (actualFiber p) a b z.val (z.val+r • fieldVector f z.val))
      (densityCurrent f p a b z.val+
        pairSample z.val (a z.val) (quantizer (symbolFirst p (sourceState z.val) (sliceState (fieldVector f z.val))) (b z.val))) 0 :=by
  let h:=fieldVector f z.val
  have line : HasDerivAt (fun r : ℝ=>z.val+r • h) h 0 :=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const h).const_add z.val using 1
    simp
  let E : FiberMap→L[ℝ] FockFiber:=(ContinuousLinearMap.apply ℂ FockFiber (b z.val)).restrictScalars ℝ
  have hv:=E.hasFDerivAt.comp_hasDerivAt 0 (actualFiber_curve_deriv p z h)
  have hd (word : Occupation) : HasDerivAt (fun r : ℝ=>complexDensity word.card (z.val+r • h))
      (fderiv ℝ (complexDensity word.card) z.val h) 0 :=by
    have hc : HasFDerivAt (complexDensity word.card) (fderiv ℝ (complexDensity word.card) z.val) (z.val+(0:ℝ) • h) :=by
      simpa only [zero_smul,add_zero] using (complexDensity_smooth word.card z).differentiableAt (by simp) |>.hasFDerivAt
    exact hc.comp_hasDerivAt 0 line
  have value:=weighted_fiber_deriv (fun r word=>complexDensity word.card (z.val+r • h))
    (fun r=>actualFiber p (z.val+r • h) (b z.val)) (a z.val)
    (fun word=>fderiv ℝ (complexDensity word.card) z.val h)
    (quantizer (symbolFirst p (sourceState z.val) (sliceState h)) (b z.val)) hd hv
  simpa only [fiberSample,pairSample,densityCurrent,zero_smul,add_zero,Finset.sum_add_distrib] using value

theorem fiber_sample_slice (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (z : physicalChart) :
    sampleCurrent (fiberSample (actualFiber p) a b) f z.val=
      densityCurrent f p a b z.val+
        pairSample z.val (a z.val) (quantizer (symbolFirst p (sourceState z.val) (sliceState (fieldVector f z.val))) (b z.val)) :=by
  let h:=fieldVector f z.val
  have line : HasDerivAt (fun r : ℝ=>z.val+r • h) h 0 :=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const h).const_add z.val using 1
    simp
  have slot:=(fiberSample_param (actualFiber p) (actualFiber_smooth p) a b id (fun _=>z.val)
    z.val z.property contDiffAt_id contDiffAt_const).differentiableAt (by simp)
  have hs : HasFDerivAt (fiberSample (actualFiber p) a b z.val)
      (fderiv ℝ (fiberSample (actualFiber p) a b z.val) z.val) (z.val+(0:ℝ) • h) :=by
    simpa only [Function.comp_apply,id_eq,zero_smul,add_zero] using slot.hasFDerivAt
  have dh:=hs.comp_hasDerivAt 0 line
  have eq:=dh.unique (fiber_curve_deriv f p a b z)
  exact eq

theorem fiber_sample_mother_balance (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (z : physicalChart) :
    sampleCurrent (fiberSample (actualFiber p) a b) f z.val+
      pairSample z.val (a z.val) (quantizer (symbolFirst p (sourceState z.val) (complement f z.val)) (b z.val))=
      densityCurrent f p a b z.val-pairSample z.val (a z.val) (fiberFamily f p z.val (b z.val)) :=by
  have read:=congrArg (fun A : FiberMap=>pairSample z.val (a z.val) (A (b z.val))) (mother_current_slice f p z)
  rw [actualFiber_slice] at read
  simp only [add_apply,pairSample_add_right,neg_apply] at read
  have negPair : pairSample z.val (a z.val) (-(fiberFamily f p z.val (b z.val)))=
      -pairSample z.val (a z.val) (fiberFamily f p z.val (b z.val)) :=by
    simp only [pairSample,PiLp.neg_apply,mul_neg,Finset.sum_neg_distrib]
  rw [negPair] at read
  rw [fiber_sample_slice,add_assoc,read,sub_eq_add_neg]

end LowEnergy.PreparationVacuumFieldCovector
