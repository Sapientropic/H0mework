import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberBackground

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberZero
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumNoetherChart
open ActualDressedSourcePreparation ActualDressedFullCoulomb ActualDressedNoether
open GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open FullYSourceCutoffVolterra
open scoped InnerProductSpace
attribute [local irreducible] dressedNoetherKernel dressedEulerObserver sourceDressedUnit
  physicalTime jointResolvent noetherReader

def actualN2GreenWords (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) : Op :=
  let U:=CanonicalPhysicalResolvent.finiteResolvent p F z
  U-U*actualA p F*U+U*actualA p F*U*actualA p F*U

def actualN1GreenWords (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) : Op :=
  let U:=CanonicalPhysicalResolvent.finiteResolvent p F z
  U-U*actualA p F*U

theorem actual_left_material_word_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (t : ℝ) :
    gradeZeroProjection*physicalTime p F t 0*jointResolvent p F z 0=
      gradeZeroProjection*SourceFiniteUnitary.time (actualC p F) t*CanonicalPhysicalResolvent.finiteResolvent p F z := by
  calc
    _=gradeZeroProjection*SourceFiniteUnitary.time (actualC p F) t*jointResolvent p F z 0 := by
      rw [actual_time_grade_zero_left]
    _=SourceFiniteUnitary.time (actualC p F) t*(gradeZeroProjection*jointResolvent p F z 0) := by
      rw [(actual_C_time_grade_zero p F t).eq,mul_assoc]
    _=SourceFiniteUnitary.time (actualC p F) t*(gradeZeroProjection*CanonicalPhysicalResolvent.finiteResolvent p F z) := by
      rw [actual_resolvent_grade_zero_left p F z nonreal]
    _=SourceFiniteUnitary.time (actualC p F) t*gradeZeroProjection*CanonicalPhysicalResolvent.finiteResolvent p F z := by
      rw [mul_assoc]
    _=_ := by rw [(actual_C_time_grade_zero p F t).symm.eq]

private theorem actual_left_material_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (t : ℝ) (x y : H) (fixed : gradeZeroProjection x=x) :
    inner ℂ x (physicalTime p F t 0 (jointResolvent p F z 0 y))=
      inner ℂ x (SourceFiniteUnitary.time (actualC p F) t (CanonicalPhysicalResolvent.finiteResolvent p F z y)) := by
  have original:=congrArg (fun A : Op=>inner ℂ x (A y)) (actual_left_material_word_return p F z nonreal t)
  simpa only [mul_apply_eq_comp,←grade_zero_projection_pair,fixed] using original

/-- Both original material Green legs and both times now consume the actual N2 created unit; the full Noether reader is retained. -/
theorem actual_noether_created_finite_read (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    inner ℂ (sourceDressedUnit event.epsilon event.precision)
      (dressedNoetherKernel event transfer reader age 0 (sourceDressedUnit event.epsilon event.precision))=
    inner ℂ (sourceDressedUnit event.epsilon event.precision)
      (SourceFiniteUnitary.time (actualC (event.momentum-transfer) event.frame) (-age)
        (CanonicalPhysicalResolvent.finiteResolvent (event.momentum-transfer) event.frame event.energy
          (noetherReader reader event.momentum event.frame 0
            (actualN2GreenWords event.momentum event.frame event.energy
              (partialEvolution (actualC event.momentum event.frame) (actualA event.momentum event.frame) 2 age
                (sourceDressedUnit event.epsilon event.precision)))))) := by
  unfold dressedNoetherKernel actualN2GreenWords
  simp only [mul_apply_eq_comp]
  rw [actual_created_resolvent_time_return _ _ _ event.nonreal]
  exact actual_left_material_pair _ _ _ event.nonreal _ _ _
    (actual_created_unit_grade_zero_fixed event.epsilon event.precision)

/-- The unchanged original N1 background receives its own two-word Green and two-prefix time return. -/
theorem actual_noether_background_finite_read (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    inner ℂ (prepared (sourceProfile event.epsilon event.precision))
      (dressedNoetherKernel event transfer reader age 0 (prepared (sourceProfile event.epsilon event.precision)))=
    inner ℂ (prepared (sourceProfile event.epsilon event.precision))
      (SourceFiniteUnitary.time (actualC (event.momentum-transfer) event.frame) (-age)
        (CanonicalPhysicalResolvent.finiteResolvent (event.momentum-transfer) event.frame event.energy
          (noetherReader reader event.momentum event.frame 0
            (actualN1GreenWords event.momentum event.frame event.energy
              (partialEvolution (actualC event.momentum event.frame) (actualA event.momentum event.frame) 1 age
                (prepared (sourceProfile event.epsilon event.precision))))))) := by
  unfold dressedNoetherKernel actualN1GreenWords
  simp only [mul_apply_eq_comp]
  rw [actual_background_resolvent_time_return _ _ _ event.nonreal]
  exact actual_left_material_pair _ _ _ event.nonreal _ _ _ (actual_background_grade_zero_fixed _)

/-- The original unit-minus-background observation is exactly a finite original Yukawa-word expression, with independent momenta and full reader. -/
theorem actual_noether_observer_finite_read (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0)=
      -inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (SourceFiniteUnitary.time (actualC (event.momentum-transfer) event.frame) (-age)
          (CanonicalPhysicalResolvent.finiteResolvent (event.momentum-transfer) event.frame event.energy
            (noetherReader reader event.momentum event.frame 0
              (actualN2GreenWords event.momentum event.frame event.energy
                (partialEvolution (actualC event.momentum event.frame) (actualA event.momentum event.frame) 2 age
                  (sourceDressedUnit event.epsilon event.precision))))))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (SourceFiniteUnitary.time (actualC (event.momentum-transfer) event.frame) (-age)
          (CanonicalPhysicalResolvent.finiteResolvent (event.momentum-transfer) event.frame event.energy
            (noetherReader reader event.momentum event.frame 0
              (actualN1GreenWords event.momentum event.frame event.energy
                (partialEvolution (actualC event.momentum event.frame) (actualA event.momentum event.frame) 1 age
                  (prepared (sourceProfile event.epsilon event.precision))))))) := by
  rw [dressed_euler_observer_original,actual_noether_created_finite_read,actual_noether_background_finite_read]

end LowEnergy.GaussComposite.ActualDressedNumberZero
