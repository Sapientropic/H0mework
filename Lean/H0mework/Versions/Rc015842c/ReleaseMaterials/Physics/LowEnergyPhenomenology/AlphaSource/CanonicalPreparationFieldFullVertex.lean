import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldSourcePairing
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumFullFieldRiesz
open GaussCoreHilbert CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalPhysicalYResolvent
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse PreparationVacuumSourceActionJets
open PreparationVacuumSourcePreparedResponse GaussComposite GaussComposite.SourceGraph
open FullYSourceCutoffVolterra (cutoff)
open scoped Topology InnerProductSpace BigOperators
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

abbrev Operator := H →L[ℂ] H
attribute [local irreducible] finiteFull fieldJets sourceProfile
local instance : NormedAlgebra ℝ Operator := NormedAlgebra.restrictScalars ℝ ℂ Operator

def currentPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  finitePrice F (fun i j=>(fieldJets f p (frameTest F i) (frameTest F j)).first 0)

def contactPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  finitePrice F (fun i j=>(fieldJets f p (frameTest F i) (frameTest F j)).second)

theorem currentPrice_nonnegative (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : 0≤currentPrice f p F :=
  finitePrice_nonnegative F _

theorem contactPrice_nonnegative (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : 0≤contactPrice f p F :=
  finitePrice_nonnegative F _

def currentVertex (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) : Operator :=
  finiteFull (p+k) F cut z*currentRestriction f p F 0*finiteFull p F cut w

def contactVertex (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) : Operator :=
  finiteFull (p+k) F cut z*contactRestriction f p F*finiteFull p F cut w

theorem currentVertex_original_pair (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (x y : H) :
    inner ℂ x (currentVertex f p k F cut z w y)=
      (fieldJets f p (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
        (sourceTestApprox F (finiteFull p F cut w y))).first 0 := by
  unfold currentVertex
  simp only [mul_apply_eq_comp]
  rw [←(finiteFull (p+k) F cut z).adjoint_inner_left]
  exact currentRestriction_original_pair f p F _ _

theorem contactVertex_original_pair (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (x y : H) :
    inner ℂ x (contactVertex f p k F cut z w y)=
      (fieldJets f p (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
        (sourceTestApprox F (finiteFull p F cut w y))).second := by
  unfold contactVertex
  simp only [mul_apply_eq_comp]
  rw [←(finiteFull (p+k) F cut z).adjoint_inner_left]
  exact contactRestriction_original_pair f p F _ _

theorem triple_price (A B C : Operator) (a b c : ℝ)
    (ha : ‖A‖≤a) (hb : ‖B‖≤b) (hc : ‖C‖≤c) : ‖A*B*C‖≤a*b*c := by
  exact (norm_mul_le _ _).trans (mul_le_mul
    ((norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha))) hc
    (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans ha) ((norm_nonneg _).trans hb)))

theorem currentVertex_price (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    ‖currentVertex f p k F cut z w‖≤normBound cut z*currentPrice f p F*normBound cut w :=
  triple_price _ _ _ _ _ _ (finiteFull_bound (p+k) F cut z hz) (finiteRiesz_price F _) (finiteFull_bound p F cut w hw)

theorem contactVertex_price (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    ‖contactVertex f p k F cut z w‖≤normBound cut z*contactPrice f p F*normBound cut w :=
  triple_price _ _ _ _ _ _ (finiteFull_bound (p+k) F cut z hz) (finiteRiesz_price F _) (finiteFull_bound p F cut w hw)

attribute [local irreducible] formRestriction currentRestriction contactRestriction

-- This is the original full-Y base plus its actual finite form variation.
-- Identification with a field-varying graded compression is a distinct transport mouth.
def insertedFamily (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z : ℂ) (r : ℝ) : Operator :=
  compression p F+cutoff cut-z • 1+(formRestriction f p F r-formRestriction f p F 0)

def insertedResolvent (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z : ℂ) (r : ℝ) : Operator :=
  Ring.inverse (insertedFamily f p F cut z r)

def originalFullUnit (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) : Operatorˣ where
  val:=compression p F+cutoff cut-z • 1
  inv:=finiteFull p F cut z
  val_inv:=finiteFull_right p F cut z hz
  inv_val:=finiteFull_left p F cut z hz

theorem insertedResolvent_zero (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (hz : z.im≠0) : insertedResolvent f p F cut z 0=finiteFull p F cut z := by
  unfold insertedResolvent insertedFamily
  rw [sub_self,add_zero]
  exact Ring.inverse_unit (originalFullUnit p F cut z hz)

theorem insertedResolvent_first (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    HasDerivAt (insertedResolvent f p F cut z)
      (-(finiteFull p F cut z*currentRestriction f p F 0*finiteFull p F cut z)) 0 := by
  have family : HasDerivAt (insertedFamily f p F cut z) (currentRestriction f p F 0) 0 := by
    exact ((formRestriction_first f p F).sub_const (formRestriction f p F 0)).const_add
      (compression p F+cutoff cut-z • 1)
  have inverse := hasFDerivAt_ringInverse (𝕜:=ℝ) (originalFullUnit p F cut z hz)
  have same : insertedFamily f p F cut z 0=(originalFullUnit p F cut z hz : Operator) := by
    simp only [insertedFamily,sub_self,add_zero,originalFullUnit]
  have generated:=inverse.comp_hasDerivAt_of_eq 0 family same.symm
  convert! generated using 1

def insertedCurrent (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (r : ℝ) : Operator :=
  insertedResolvent f p F cut z r*currentRestriction f p F r*insertedResolvent f p F cut z r

theorem inverse_insertion_algebra {A : Type*} [Ring A] (R J K : A) :
    R*K*R-(R*J*R*J*R)-(R*J*R*J*R)=
      (-(R*J*R)*J+R*K)*R+(R*J)*(-(R*J*R)) := by
  simp only [mul_add,add_mul,neg_mul,mul_neg,mul_assoc,sub_eq_add_neg]
  abel

theorem insertedCurrent_derivative (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    HasDerivAt (insertedCurrent f p F cut z)
      (finiteFull p F cut z*contactRestriction f p F*finiteFull p F cut z-
        (finiteFull p F cut z*currentRestriction f p F 0*finiteFull p F cut z*
          currentRestriction f p F 0*finiteFull p F cut z)-
        (finiteFull p F cut z*currentRestriction f p F 0*finiteFull p F cut z*
          currentRestriction f p F 0*finiteFull p F cut z)) 0 := by
  have R:=insertedResolvent_first f p F cut z hz
  have J : HasDerivAt (currentRestriction f p F) (contactRestriction f p F) 0 := by
    convert! currentRestriction_second f p F using 1
  have product:=(R.mul J).mul R
  simp only [Pi.mul_apply,insertedResolvent_zero f p F cut z hz] at product
  have algebra:=inverse_insertion_algebra (finiteFull p F cut z) (currentRestriction f p F 0) (contactRestriction f p F)
  convert! product.congr_deriv algebra.symm using 1

def preparedCurrent (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : ℂ :=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (currentVertex f p k F cut z w (completedLeg right b t (sourceProfile epsilon precision)))

theorem preparedCurrent_source (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    preparedCurrent epsilon precision f p k F cut z w left right a s b t=
      (fieldJets f p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (completedLeg left a s (sourceProfile epsilon precision))))
        (sourceTestApprox F (finiteFull p F cut w (completedLeg right b t (sourceProfile epsilon precision))))).first 0 :=
  currentVertex_original_pair f p k F cut z w _ _

def preparedContact (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : ℂ :=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (contactVertex f p k F cut z w (completedLeg right b t (sourceProfile epsilon precision)))

theorem preparedContact_source (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    preparedContact epsilon precision f p k F cut z w left right a s b t=
      (fieldJets f p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (completedLeg left a s (sourceProfile epsilon precision))))
        (sourceTestApprox F (finiteFull p F cut w (completedLeg right b t (sourceProfile epsilon precision))))).second :=
  contactVertex_original_pair f p k F cut z w _ _

theorem vertex_pair_price (T : Operator) (P : ℝ) (bound : ‖T‖≤P) (x y : H) :
    ‖inner ℂ x (T y)‖≤‖x‖*P*‖y‖ := by
  calc
    ‖inner ℂ x (T y)‖≤‖x‖*‖T y‖:=norm_inner_le_norm _ _
    _≤‖x‖*(P*‖y‖):=mul_le_mul_of_nonneg_left
      ((T.le_opNorm y).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))) (norm_nonneg _)
    _=‖x‖*P*‖y‖:= (mul_assoc _ _ _).symm

theorem preparedCurrent_price (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (a s b t : Fin 2) :
    ‖preparedCurrent epsilon precision f p k F cut z w left right a s b t‖≤
      ‖completedLeg left a s (sourceProfile epsilon precision)‖*
      (normBound cut z*currentPrice f p F*normBound cut w)*
      ‖completedLeg right b t (sourceProfile epsilon precision)‖ :=
  vertex_pair_price _ _ (currentVertex_price f p k F cut z w hz hw) _ _

def curvatureCurrent (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) : ℂ :=
  preparedCurrent epsilon precision (readerReal sourceMomentum row) p k F cut z w left right a s b t+
    Complex.I*preparedCurrent epsilon precision (readerImag sourceMomentum row) p k F cut z w left right a s b t

def curvatureFormCurve (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) (r : ℝ) : ℂ :=
  let X:=sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (completedLeg left a s (sourceProfile epsilon precision)))
  let Y:=sourceTestApprox F (finiteFull p F cut w (completedLeg right b t (sourceProfile epsilon precision)))
  fieldForm (readerReal sourceMomentum row) p X Y r+
    Complex.I*(fieldForm (readerImag sourceMomentum row) p X Y r-fieldForm (readerImag sourceMomentum row) p X Y 0)

theorem curvatureCurrent_actual_derivative (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (curvatureFormCurve epsilon precision sourceMomentum row p k F cut z w left right a s b t)
      (curvatureCurrent epsilon precision sourceMomentum row p k F cut z w left right a s b t) 0 := by
  unfold curvatureFormCurve curvatureCurrent
  rw [preparedCurrent_source,preparedCurrent_source]
  exact (fieldJets _ _ _ _).actual.1.add (((fieldJets _ _ _ _).actual.1.sub_const _).const_mul Complex.I)

def constantPairJets (c : ℂ) : TwoJets (fun _ : ℝ=>c) where
  first _:=0
  second:=0
  derivative_near:=Filter.Eventually.of_forall (fun r=>hasDerivAt_const r c)
  second_derivative:=hasDerivAt_const 0 0

theorem curvatureContact_actual_derivative (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
    (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (deriv (curvatureFormCurve epsilon precision sourceMomentum row p k F cut z w left right a s b t))
      (preparedContact epsilon precision (readerReal sourceMomentum row) p k F cut z w left right a s b t+
        Complex.I*preparedContact epsilon precision (readerImag sourceMomentum row) p k F cut z w left right a s b t) 0 := by
  rw [preparedContact_source,preparedContact_source]
  let X:=sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (completedLeg left a s (sourceProfile epsilon precision)))
  let Y:=sourceTestApprox F (finiteFull p F cut w (completedLeg right b t (sourceProfile epsilon precision)))
  let jets:=(fieldJets (readerReal sourceMomentum row) p X Y).add (TwoJets.scale Complex.I
    ((fieldJets (readerImag sourceMomentum row) p X Y).sub (constantPairJets (fieldForm (readerImag sourceMomentum row) p X Y 0))))
  convert! jets.actual.2 using 1
  simp only [jets,TwoJets.add,TwoJets.scale,TwoJets.sub,constantPairJets,sub_zero]
  rfl

theorem curvatureCurrent_remaining_primal (sourceMomentum : Fin 4 → ℂ)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    (remainingChannels (readerReal sourceMomentum 33) z).primal 1 0 0=1/2 :=
  curvature_primal_retained sourceMomentum z

end LowEnergy.PreparationVacuumFullFieldRiesz
