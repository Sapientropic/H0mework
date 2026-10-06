import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalControlledFieldTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPropagationPencil
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalTailPrice
open SourceFiniteUnitary CanonicalGradedVariation
open scoped Topology BigOperators InnerProductSpace Matrix
abbrev Op:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent rawReader rawReaderContact
  physicalTime timeSlope factorialBudget variationBudget

section LocalAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E→L[ℂ] E):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (E→L[ℂ] E):=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem variation_commutator (C B : E→L[ℂ] E) (t : ℝ) :
    ((-Complex.I) • B)*time C t+((-Complex.I) • C)*variation C B t=
      variation C B t*((-Complex.I) • C)+time C t*((-Complex.I) • B) :=by
  have generator : HasDerivAt (fun r : ℝ=>(-Complex.I) • (C+r • B)) ((-Complex.I) • B) 0:=by
    have h:=((hasDerivAt_id (0:ℝ)).smul_const B).const_add C
    convert! h.const_smul (-Complex.I) using 1; first | rfl | simp only [one_smul]
  have evolution:=PreparationVacuumCausalFieldResponse.parameter_derivative_full C B t
  have left:=generator.mul evolution
  have right:=evolution.mul generator
  have same : (fun r : ℝ=>((-Complex.I) • (C+r • B))*time (C+r • B) t)=
      (fun r : ℝ=>time (C+r • B) t*((-Complex.I) • (C+r • B))):=by
    funext r
    exact ((time_commutes (C+r • B) (C+r • B) (Commute.refl _) t).smul_left (-Complex.I)).eq
  change HasDerivAt (fun r : ℝ=>((-Complex.I) • (C+r • B))*time (C+r • B) t) _ 0 at left
  change HasDerivAt (fun r : ℝ=>time (C+r • B) t*((-Complex.I) • (C+r • B))) _ 0 at right
  rw [←same] at right
  simpa only [zero_smul,add_zero] using left.unique right

private theorem variation_left_ode (C B : E→L[ℂ] E) (t : ℝ) :
    HasDerivAt (variation C B)
      (((-Complex.I) • C)*variation C B t+((-Complex.I) • B)*time C t) t :=by
  have same : PreparationVacuumFieldPerturbation.Blocks.crossTime C C B=variation C B:=by
    funext r
    rw [PreparationVacuumFieldPerturbation.Blocks.crossTime_integral]
    simp only [variation,variationBetween,zero_smul,add_zero]
  have h:=PreparationVacuumFieldPerturbation.Blocks.crossTime_derivative C C B t
  rw [same] at h
  rw [←variation_commutator C B t,add_comm] at h
  exact h

private theorem time_left_ode (C : E→L[ℂ] E) (t : ℝ) :
    HasDerivAt (time C) (((-Complex.I) • C)*time C t) t :=by
  have h:=PreparationVacuumFieldPerturbation.time_operator_derivative C t
  rw [←((time_commutes C C (Commute.refl C) t).smul_left (-Complex.I)).eq] at h
  exact h

end LocalAlgebra

/-- Both legs use their actual physical-time generators, without material spectral subtraction. -/
def leftGenerator (q : PhysicalResponsePoint) : Op:=(-Complex.I) • jointGenerator (q.p+q.k) q.F 0 0

def rightGenerator (q : PhysicalResponsePoint) : Op:=(-Complex.I) • jointGenerator q.p q.F 0 0

def leftCurrent (q : PhysicalResponsePoint) (force : Field289) : Op:=
  (-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0 force

def rightCurrent (q : PhysicalResponsePoint) (force : Field289) : Op:=
  (-Complex.I) • jointCurrent q.p q.F 0 0 force

def rawInitial (q : PhysicalResponsePoint) (reader : Field289) : Op:=
  jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0

def slopeInitial (q : PhysicalResponsePoint) (reader force : Field289) : Op:=
  (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*jointResolvent (q.p+q.k) q.F q.z 0))*
    rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0+
  jointResolvent (q.p+q.k) q.F q.z 0*rawReaderContact reader force q.p q.F*jointResolvent q.p q.F q.w 0+
  jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
    (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))

section Products
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E→L[ℂ] E):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (E→L[ℂ] E):=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem rawProduct_ode (CL CR A : E→L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>time CL (-r)*A*time CR r)
      (-((-Complex.I) • CL)*(time CL (-t)*A*time CR t)+
        (time CL (-t)*A*time CR t)*((-Complex.I) • CR)) t :=by
  have L:=(time_left_ode CL (-t)).scomp t ((hasDerivAt_id t).neg)
  have R:=PreparationVacuumFieldPerturbation.time_operator_derivative CR t
  have h:=(L.mul_const A).mul R
  convert! h using 1; first | rfl | simp only [Function.comp_def,Pi.mul_apply,neg_one_smul,mul_assoc,neg_mul]

private theorem slopeProduct_ode (CL CR BL BR A D : E→L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>variation CL BL (-r)*A*time CR r+
      time CL (-r)*D*time CR r+time CL (-r)*A*variation CR BR r)
      (-((-Complex.I) • CL)*(variation CL BL (-t)*A*time CR t+
          time CL (-t)*D*time CR t+time CL (-t)*A*variation CR BR t)+
        (variation CL BL (-t)*A*time CR t+time CL (-t)*D*time CR t+
          time CL (-t)*A*variation CR BR t)*((-Complex.I) • CR)-
        ((-Complex.I) • BL)*(time CL (-t)*A*time CR t)+
        (time CL (-t)*A*time CR t)*((-Complex.I) • BR)) t :=by
  have TL:=(time_left_ode CL (-t)).scomp t ((hasDerivAt_id t).neg)
  have TR:=PreparationVacuumFieldPerturbation.time_operator_derivative CR t
  have VL:=(variation_left_ode CL BL (-t)).scomp t ((hasDerivAt_id t).neg)
  have VR:=variation_left_ode CR BR t
  rw [add_comm,variation_commutator CR BR t] at VR
  have h:=(((VL.mul_const A).mul TR).add ((TL.mul_const D).mul TR)).add ((TL.mul_const A).mul VR)
  convert! h using 1; first | rfl | (simp only [Function.comp_def,Pi.mul_apply,Pi.add_apply,neg_one_smul,mul_add,add_mul,mul_assoc,neg_mul,mul_neg,neg_add_rev,sub_eq_add_neg]; abel)

end Products

theorem rawKernel_initial (q : PhysicalResponsePoint) (reader : Field289) :
    fiveKernel reader q.p q.k q.F q.z q.w 0 0=rawInitial q reader :=by
  simp only [fiveKernel,neg_zero,physicalTime_initial,one_mul,mul_one,rawInitial]

theorem slopeKernel_initial (q : PhysicalResponsePoint) (reader force : Field289) :
    fiveDerivative reader force q.p q.k q.F q.z q.w 0=slopeInitial q reader force :=by
  simp only [fiveDerivative,neg_zero,timeSlope_initial,physicalTime_initial,zero_mul,mul_zero,
    one_mul,mul_one,zero_add,add_zero,slopeInitial]

theorem rawKernel_ode (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>fiveKernel reader q.p q.k q.F q.z q.w r 0)
      (-leftGenerator q*fiveKernel reader q.p q.k q.F q.z q.w t 0+
        fiveKernel reader q.p q.k q.F q.z q.w t 0*rightGenerator q) t :=by
  simpa only [fiveKernel,physicalTime,rawInitial,leftGenerator,rightGenerator,mul_assoc] using
    rawProduct_ode (jointGenerator (q.p+q.k) q.F 0 0) (jointGenerator q.p q.F 0 0) (rawInitial q reader) t

theorem slopeKernel_ode (q : PhysicalResponsePoint) (reader force : Field289) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>fiveDerivative reader force q.p q.k q.F q.z q.w r)
      (-leftGenerator q*fiveDerivative reader force q.p q.k q.F q.z q.w t+
        fiveDerivative reader force q.p q.k q.F q.z q.w t*rightGenerator q-
        leftCurrent q force*fiveKernel reader q.p q.k q.F q.z q.w t 0+
        fiveKernel reader q.p q.k q.F q.z q.w t 0*rightCurrent q force) t :=by
  have h:=slopeProduct_ode (jointGenerator (q.p+q.k) q.F 0 0) (jointGenerator q.p q.F 0 0)
    (jointCurrent (q.p+q.k) q.F 0 0 force) (jointCurrent q.p q.F 0 0 force)
    (rawInitial q reader) (slopeInitial q reader force) t
  unfold rawInitial slopeInitial at h
  simp only [jointCurrent_source] at h
  simpa only [fiveDerivative,fiveKernel,physicalTime,timeSlope,leftGenerator,rightGenerator,leftCurrent,
    rightCurrent,jointCurrent_source,mul_assoc,mul_add,add_mul,add_assoc] using h

end LowEnergy.PreparationVacuumPropagationPencil
