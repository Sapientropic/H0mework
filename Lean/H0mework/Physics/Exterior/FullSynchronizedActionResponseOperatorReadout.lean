import H0mework.Physics.Exterior.FullSynchronizedActionResponseOperator

/-!
# Full synchronized action matter-field readouts

Small projection lemmas for consumers of the action-generated matter overlay.
They live outside the producer module so downstream proof work does not
invalidate and rebuild that high-fan-out producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFullSynchronizedActionResponseOperator

open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false

@[simp] theorem fullSynchronizedActionMatterActual_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem fullSynchronizedActionMatterActual_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).gaugeConnection =
      current.gaugeConnection :=
  rfl

@[simp] theorem fullSynchronizedActionMatterActual_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).gaugeAuxiliary =
      current.gaugeAuxiliary :=
  rfl

@[simp] theorem fullSynchronizedActionMatterActual_gravityConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).gravityConnection =
      (fullSynchronizedActionLorentzActual source current).gravityConnection :=
  rfl

@[simp] theorem fullSynchronizedActionMatterActual_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).matter =
      actionGeneratedMatterLocalField
        (fullSynchronizedActionMatterCauchyState source current) 0 :=
  rfl

@[simp] theorem fullSynchronizedActionMatterActual_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).conjugateMatter =
      actionGeneratedConjugateMatterLocalField
        (fullSynchronizedActionMatterCauchyState source current) 0 :=
  rfl

theorem fullSynchronizedActionMatterActual_gravityConnection_origin_eq_cauchy
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).gravityConnection 0 =
      (fullSynchronizedActionMatterCauchyState source current).gravityConnection
        0 := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [fullSynchronizedActionMatterActual_gravityConnection]
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual source current).gravityConnection 0 =
      (fullSynchronizedActionLorentzActual source current).gravityConnection
        (canonicalCauchySlicePoint 0 0)
  rw [contactZero]

theorem fullSynchronizedActionMatterActual_gaugeConnection_origin_eq_cauchy
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterActual source current).gaugeConnection 0 =
      (fullSynchronizedActionMatterCauchyState source current).gaugeConnection
        0 := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [fullSynchronizedActionMatterActual_gaugeConnection]
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    current.gaugeConnection 0 =
      current.gaugeConnection (canonicalCauchySlicePoint 0 0)
  rw [contactZero]

@[simp] theorem fullSynchronizedActionMatterOriginField_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterOriginField source current).coframe =
      current.coframe 0 :=
  rfl

@[simp] theorem fullSynchronizedActionMatterOriginField_gaugeCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterOriginField source current).gaugeCurvature =
      holonomicGaugeCurvature current 0 := by
  unfold fullSynchronizedActionMatterOriginField toContinuumPointField
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [fullSynchronizedActionMatterActual_gaugeConnection]

@[simp] theorem fullSynchronizedActionMatterOriginField_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterOriginField source current).gaugeAuxiliary =
      current.gaugeAuxiliary 0 :=
  rfl

@[simp] theorem fullSynchronizedActionMatterOriginField_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterOriginField source current).matter =
      (fullSynchronizedActionMatterCauchyState source current).matter 0 := by
  unfold fullSynchronizedActionMatterOriginField toContinuumPointField
  rw [fullSynchronizedActionMatterActual_matter,
    actionGeneratedMatterLocalField_origin]

@[simp] theorem fullSynchronizedActionMatterOriginField_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionMatterOriginField source current).conjugateMatter =
      (fullSynchronizedActionMatterCauchyState source current).conjugateMatter
        0 := by
  unfold fullSynchronizedActionMatterOriginField toContinuumPointField
  rw [fullSynchronizedActionMatterActual_conjugateMatter,
    actionGeneratedConjugateMatterLocalField_origin]

end

end
  SaturationMonoid.PhysicsCore.StageNineFullSynchronizedActionResponseOperator
