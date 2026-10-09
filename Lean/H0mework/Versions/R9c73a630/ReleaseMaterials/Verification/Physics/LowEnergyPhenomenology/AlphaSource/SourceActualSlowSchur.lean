import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.SourceSlowNeumann

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumQuantumSlowResponse
open GaussCoreHilbert PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumGaugeSlowFrequency PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalPoleHalfResponse CanonicalGradedSpatialSource CanonicalGradedCurrent
open PreparationVacuumPhysicalHalfAxis
open scoped Topology
attribute [local irreducible] actualC actualA sourceVelocityLinear sourceOffgapInverse
  sourceEqualProjection sourceOffProjection sourceStaticLiouvillian sourceSlowReturn sourceSlowTransport
  sourceFullHalfBase sourceFullHalfUpper sourceFullInitialBase sourceFullInitialUpper sourceProjection

def sourceSlowEffective (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) : SourceSuperOp :=
  sourceEqualProjection F*sourceSlowTransport F n zeta*sourceSlowReturn F n zeta delta*sourceEqualProjection F

def sourceSlowForcing (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ) : SourceSuperOp :=
  sourceEqualProjection F-(delta : ℂ) • (sourceEqualProjection F*sourceSlowTransport F n zeta*
    sourceSlowReturn F n zeta delta*sourceOffgapInverse F)

def sourceRetainerReturn (F : GaussUnitaryHistory.Index) : SourceSuperOp :=
  Complex.I • (ContinuousLinearMap.mul ℂ SourceOp).flip (actualA 0 F*sourceProjection)

theorem sourceRetainerReturn_apply (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    sourceRetainerReturn F X=Complex.I • (X*(actualA 0 F*sourceProjection)) := rfl

private theorem slow_eliminate (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) (X B : SourceOp)
    (equation : (delta : ℂ) • sourceSlowTransport F n zeta X+sourceStaticLiouvillian F X=B) :
    X=sourceSlowReturn F n zeta delta (sourceEqualProjection F X+sourceOffgapInverse F B) := by
  have generated:=congrArg (sourceOffgapInverse F) equation
  have inverse:=congrArg (fun T : SourceSuperOp=>T X) (sourceOffgapInverse_right F)
  change sourceOffgapInverse F (sourceStaticLiouvillian F X)=sourceOffProjection F X at inverse
  simp only [map_add,map_smul,inverse] at generated
  have off : sourceOffProjection F X=X-sourceEqualProjection F X := by
    simp only [sourceOffProjection,sub_apply,one_apply_eq_self]
  rw [off] at generated
  have factored : (1+sourceSlowPerturbation F n zeta delta) X=sourceEqualProjection F X+sourceOffgapInverse F B := by
    simp only [add_apply,one_apply_eq_self,sourceSlowPerturbation,smul_apply,mul_apply_eq_comp]
    rw [←generated]
    module
  have returned:=congrArg (sourceSlowReturn F n zeta delta) factored
  have cancel:=congrArg (fun T : SourceSuperOp=>T X) (sourceSlowReturn_left F n zeta delta small)
  change sourceSlowReturn F n zeta delta ((1+sourceSlowPerturbation F n zeta delta) X)=X at cancel
  rw [cancel] at returned
  exact returned

private theorem slow_effective (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (delta : ℝ)
    (small : (abs delta) ≤ sourceSlowRadius F n zeta) (X B : SourceOp)
    (equation : (delta : ℂ) • sourceSlowTransport F n zeta X+sourceStaticLiouvillian F X=B) :
    sourceSlowEffective F n zeta delta ((delta : ℂ) • sourceEqualProjection F X)=sourceSlowForcing F n zeta delta B := by
  have generated:=congrArg (sourceEqualProjection F) equation
  have vanish:=congrArg (fun T : SourceSuperOp=>T X) (sourceEqual_static_zero F)
  change sourceEqualProjection F (sourceStaticLiouvillian F X)=0 at vanish
  simp only [map_add,map_smul,vanish,add_zero] at generated
  rw [slow_eliminate F n zeta delta small X B equation] at generated
  simp only [map_add] at generated
  have idempotent:=congrArg (fun T : SourceSuperOp=>T X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at idempotent
  simp only [sourceSlowEffective,sourceSlowForcing,mul_apply_eq_comp,sub_apply,smul_apply,map_smul,idempotent]
  rw [←generated]
  module

private theorem source_neg_i (X : SourceOp) : (-Complex.I) • X= -(Complex.I • X) := by
  apply ContinuousLinearMap.ext
  intro x
  change (-Complex.I) • (X x)= -(Complex.I • (X x))
  exact neg_smul Complex.I (X x)

private theorem actual_slow_system (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289) :
    (delta : ℂ) • sourceSlowTransport q.F n zeta (sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta))+
      sourceStaticLiouvillian q.F (sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta))=
      sourceFullInitialUpper q (-(delta • n)) 0 i ∧
    (delta : ℂ) • sourceSlowTransport q.F n zeta (sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta))+
      sourceStaticLiouvillian q.F (sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta))=
      sourceFullInitialBase q (-(delta • n)) 0 i-
        sourceRetainerReturn q.F (sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)) := by
  have h:=sourceFullHalf_slow_system q n delta positiveDelta zeta positiveZeta i
  simpa only [sourceSlowTransport_apply,sourceStaticLiouvillian_apply,sub_eq_add_neg,source_neg_i,
    sourceRetainerReturn_apply] using h

/-- Exact elimination of the actual upper response using the generated off-gap inverse. -/
theorem sourceActualUpper_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    X1=sourceSlowReturn q.F n zeta delta (sourceEqualProjection q.F X1+
      sourceOffgapInverse q.F (sourceFullInitialUpper q (-(delta • n)) 0 i)) :=
  slow_eliminate q.F n zeta delta small _ _ (actual_slow_system q n delta positiveDelta zeta positiveZeta i).1

/-- The base response keeps the exact original N1 retainer forcing. -/
theorem sourceActualBase_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    let X0:=sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    X0=sourceSlowReturn q.F n zeta delta (sourceEqualProjection q.F X0+
      sourceOffgapInverse q.F (sourceFullInitialBase q (-(delta • n)) 0 i-sourceRetainerReturn q.F X1)) :=
  slow_eliminate q.F n zeta delta small _ _ (actual_slow_system q n delta positiveDelta zeta positiveZeta i).2

/-- Full actual two-sector effective equation; no equal-energy coherence is removed. -/
theorem sourceActualSlow_effective (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    let X0:=sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    sourceSlowEffective q.F n zeta delta ((delta:ℂ) • sourceEqualProjection q.F X1)=
      sourceSlowForcing q.F n zeta delta (sourceFullInitialUpper q (-(delta • n)) 0 i) ∧
    sourceSlowEffective q.F n zeta delta ((delta:ℂ) • sourceEqualProjection q.F X0)=
      sourceSlowForcing q.F n zeta delta (sourceFullInitialBase q (-(delta • n)) 0 i-sourceRetainerReturn q.F X1) :=
  ⟨slow_effective q.F n zeta delta small _ _ (actual_slow_system q n delta positiveDelta zeta positiveZeta i).1,
   slow_effective q.F n zeta delta small _ _ (actual_slow_system q n delta positiveDelta zeta positiveZeta i).2⟩

theorem sourceActualUpper_normalized_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    (delta:ℂ) • X1=sourceSlowReturn q.F n zeta delta
      ((delta:ℂ) • sourceEqualProjection q.F X1+
        (delta:ℂ) • sourceOffgapInverse q.F (sourceFullInitialUpper q (-(delta • n)) 0 i)) := by
  simpa only [map_add,map_smul,smul_add] using congrArg (fun X : SourceOp=>(delta:ℂ) • X)
    (sourceActualUpper_return q n delta positiveDelta zeta positiveZeta i small)

/-- The triangular normalization retains the possible second-order source response. -/
theorem sourceActualSlow_triangular (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289)
    (small : (abs delta) ≤ sourceSlowRadius q.F n zeta) :
    let X0:=sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    let B0:=sourceFullInitialBase q (-(delta • n)) 0 i
    let B1:=sourceFullInitialUpper q (-(delta • n)) 0 i
    let U1:=(delta:ℂ) • sourceEqualProjection q.F X1
    sourceSlowEffective q.F n zeta delta (((delta:ℂ)^2) • sourceEqualProjection q.F X0)=
      (delta:ℂ) • sourceSlowForcing q.F n zeta delta B0-
      sourceSlowForcing q.F n zeta delta (sourceRetainerReturn q.F
        (sourceSlowReturn q.F n zeta delta (U1+(delta:ℂ) • sourceOffgapInverse q.F B1))) := by
  dsimp only
  have system:=(sourceActualSlow_effective q n delta positiveDelta zeta positiveZeta i small).2
  have scaled:=congrArg (fun X : SourceOp=>(delta:ℂ) • X) system
  have upperScaled:=sourceActualUpper_normalized_return q n delta positiveDelta zeta positiveZeta i small
  simp only [map_sub,smul_sub,←map_smul,smul_smul,←pow_two] at scaled
  rw [upperScaled] at scaled
  simpa only [map_smul] using scaled

end LowEnergy.PreparationVacuumQuantumSlowResponse
