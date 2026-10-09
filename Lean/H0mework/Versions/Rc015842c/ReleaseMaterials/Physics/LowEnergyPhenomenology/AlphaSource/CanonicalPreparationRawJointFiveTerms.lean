import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRawJointReaderCompression
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalJacobi

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumRawJointFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumSourcePreparedResponse
open PreparationVacuumActionFieldLift PreparationVacuumFullFieldRiesz
open CanonicalPreparationCore.Completed
open GaussComposite GaussComposite.SourceGraph
open PreparationVacuumFieldConstraintResponse PreparationVacuumSourceActionJets
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] physicalTime timeSlope jointResolvent jointCurrent rawReader rawReaderContact sourceProfile

/-- The independent left source stays before the reader and uses inverse time. -/
def fiveKernel (reader : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (age : ℝ) (h : Field289) : Op:=
  physicalTime (p+k) F (-age) h*jointResolvent (p+k) F z h*rawReader reader p F h*
    jointResolvent p F w h*physicalTime p F age h

def fiveDerivative (reader force : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (age : ℝ) : Op:=
  timeSlope force (p+k) F (-age)*jointResolvent (p+k) F z 0*rawReader reader p F 0*
    jointResolvent p F w 0*physicalTime p F age 0+
  physicalTime (p+k) F (-age) 0*(-(jointResolvent (p+k) F z 0*jointCurrent (p+k) F z 0 force*jointResolvent (p+k) F z 0))*
    rawReader reader p F 0*jointResolvent p F w 0*physicalTime p F age 0+
  physicalTime (p+k) F (-age) 0*jointResolvent (p+k) F z 0*rawReaderContact reader force p F*
    jointResolvent p F w 0*physicalTime p F age 0+
  physicalTime (p+k) F (-age) 0*jointResolvent (p+k) F z 0*rawReader reader p F 0*
    (-(jointResolvent p F w 0*jointCurrent p F w 0 force*jointResolvent p F w 0))*physicalTime p F age 0+
  physicalTime (p+k) F (-age) 0*jointResolvent (p+k) F z 0*rawReader reader p F 0*
    jointResolvent p F w 0*timeSlope force p F age

private theorem product_five {A : Type*} [Ring A] (a b c d e da db dc dd de : A) :
    (((da*b+a*db)*c+(a*b)*dc)*d+((a*b)*c)*dd)*e+(((a*b)*c)*d)*de=
      da*b*c*d*e+a*db*c*d*e+a*b*dc*d*e+a*b*c*dd*e+a*b*c*d*de :=by
  simp only [add_mul,mul_add]

theorem fiveKernel_generated (reader force : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>fiveKernel reader p k F z w age (r • force))
      (fiveDerivative reader force p k F z w age) 0 :=by
  have tl:=physicalTime_direction force (p+k) F (-age)
  have rl:=inverse_direction (p+k) F z hz force
  have jr:=rawReader_direction reader force p F
  have rr:=inverse_direction p F w hw force
  have tr:=physicalTime_direction force p F age
  have h:=(((tl.mul rl).mul jr).mul rr).mul tr
  simp only [Pi.mul_apply,zero_smul] at h
  have algebra:=product_five (physicalTime (p+k) F (-age) 0) (jointResolvent (p+k) F z 0)
    (rawReader reader p F 0) (jointResolvent p F w 0) (physicalTime p F age 0)
    (timeSlope force (p+k) F (-age)) (-(jointResolvent (p+k) F z 0*jointCurrent (p+k) F z 0 force*jointResolvent (p+k) F z 0))
    (rawReaderContact reader force p F) (-(jointResolvent p F w 0*jointCurrent p F w 0 force*jointResolvent p F w 0))
    (timeSlope force p F age)
  exact h.congr_deriv algebra

def rawPrepared (epsilon : ℝ) (precision : 0<epsilon) (reader : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (age : ℝ) (left right : Bool) (a s b t : Fin 2) (h : Field289) : ℂ:=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (fiveKernel reader p k F z w age h (completedLeg right b t (sourceProfile epsilon precision)))

def rawPreparedSlope (epsilon : ℝ) (precision : 0<epsilon) (reader force : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (age : ℝ) (left right : Bool) (a s b t : Fin 2) : ℂ:=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (fiveDerivative reader force p k F z w age (completedLeg right b t (sourceProfile epsilon precision)))

theorem rawPrepared_generated (epsilon : ℝ) (precision : 0<epsilon) (reader force : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (age : ℝ)
    (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (fun r : ℝ=>rawPrepared epsilon precision reader p k F z w age left right a s b t (r • force))
      (rawPreparedSlope epsilon precision reader force p k F z w age left right a s b t) 0 :=
  paired_derivative (fiveKernel_generated reader force p k F z w hz hw age) _ _

/-- Euler forcing takes the negative of the original raw action current. -/
def eulerCovector (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (age : ℝ) (left right : Bool) (a s b t : Fin 2) (h : Field289) : Fin 289→ℂ:=
  fun i=> -rawPrepared epsilon precision (fieldUnit i) p k F z w age left right a s b t h

def eulerCovectorSlope (epsilon : ℝ) (precision : 0<epsilon) (force : Field289) (p k : PhysicalMomentum) (F : Index)
    (z w : ℂ) (age : ℝ) (left right : Bool) (a s b t : Fin 2) : Fin 289→ℂ:=
  fun i=> -rawPreparedSlope epsilon precision (fieldUnit i) force p k F z w age left right a s b t

theorem eulerCovector_generated (epsilon : ℝ) (precision : 0<epsilon) (force : Field289) (p k : PhysicalMomentum)
    (F : Index) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (age : ℝ)
    (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (fun r : ℝ=>eulerCovector epsilon precision p k F z w age left right a s b t (r • force))
      (eulerCovectorSlope epsilon precision force p k F z w age left right a s b t) 0 :=
  hasDerivAt_pi.mpr fun i=>(rawPrepared_generated epsilon precision (fieldUnit i) force p k F z w hz hw age left right a s b t).neg

/-- Literal original F(-P)^T readback; all 289 rows, including the nine null rows, remain. -/
def originalCoSource (frequency : Fin 4→ℂ) (current : Fin 289→ℂ) : Fin 289→ℂ:=
  (PreparationVacuumOriginalGreenFeedback.originalChange (-frequency)).transpose*ᵥcurrent

theorem originalCoSource_generated (epsilon : ℝ) (precision : 0<epsilon) (force : Field289) (frequency : Fin 4→ℂ)
    (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (age : ℝ)
    (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (fun r : ℝ=>originalCoSource frequency
      (eulerCovector epsilon precision p k F z w age left right a s b t (r • force)))
      (originalCoSource frequency (eulerCovectorSlope epsilon precision force p k F z w age left right a s b t)) 0 :=by
  apply hasDerivAt_pi.mpr;intro i
  simp only [originalCoSource,Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum;intro j _
  exact ((rawPrepared_generated epsilon precision (fieldUnit j) force p k F z w hz hw age left right a s b t).neg).const_mul _


def rawCurvatureSlope (epsilon : ℝ) (precision : 0<epsilon) (qReader qForce : Fin 4→ℂ)
    (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (age : ℝ)
    (left right : Bool) (a s b t : Fin 2) : Matrix (Fin 36) (Fin 36) ℂ:=
  fun i j=>rawPreparedSlope epsilon precision (readerReal qReader i) (readerReal qForce j) p k F z w age left right a s b t+
    Complex.I*rawPreparedSlope epsilon precision (readerImag qReader i) (readerReal qForce j) p k F z w age left right a s b t+
    Complex.I*rawPreparedSlope epsilon precision (readerReal qReader i) (readerImag qForce j) p k F z w age left right a s b t-
    rawPreparedSlope epsilon precision (readerImag qReader i) (readerImag qForce j) p k F z w age left right a s b t

def rawCurvatureCurve (epsilon : ℝ) (precision : 0<epsilon) (qReader qForce : Fin 4→ℂ)
    (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (age : ℝ)
    (left right : Bool) (a s b t : Fin 2) (i j : Fin 36) (r : ℝ) : ℂ:=
  rawPrepared epsilon precision (readerReal qReader i) p k F z w age left right a s b t (r • readerReal qForce j)+
    Complex.I*rawPrepared epsilon precision (readerImag qReader i) p k F z w age left right a s b t (r • readerReal qForce j)+
    Complex.I*rawPrepared epsilon precision (readerReal qReader i) p k F z w age left right a s b t (r • readerImag qForce j)-
    rawPrepared epsilon precision (readerImag qReader i) p k F z w age left right a s b t (r • readerImag qForce j)

theorem rawCurvature_generated (epsilon : ℝ) (precision : 0<epsilon) (qReader qForce : Fin 4→ℂ)
    (p k : PhysicalMomentum) (F : Index) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (age : ℝ)
    (left right : Bool) (a s b t : Fin 2) (i j : Fin 36) :
    HasDerivAt (rawCurvatureCurve epsilon precision qReader qForce p k F z w age left right a s b t i j)
      (rawCurvatureSlope epsilon precision qReader qForce p k F z w age left right a s b t i j) 0 :=by
  have rr:=rawPrepared_generated epsilon precision (readerReal qReader i) (readerReal qForce j) p k F z w hz hw age left right a s b t
  have ir:=rawPrepared_generated epsilon precision (readerImag qReader i) (readerReal qForce j) p k F z w hz hw age left right a s b t
  have ri:=rawPrepared_generated epsilon precision (readerReal qReader i) (readerImag qForce j) p k F z w hz hw age left right a s b t
  have ii:=rawPrepared_generated epsilon precision (readerImag qReader i) (readerImag qForce j) p k F z w hz hw age left right a s b t
  exact ((rr.add (ir.const_mul Complex.I)).add (ri.const_mul Complex.I)).sub ii

end LowEnergy.PreparationVacuumRawJointFeedback
