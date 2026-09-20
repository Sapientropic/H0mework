/-
  Proposition 463: reinsert the unified one-loop carrier receipt into the
  concrete Standard-Model holy-grail front door.

  P420 expands the remaining concrete holy-grail front door into raw producer
  fields.  P462 proves that the Standard-Model one-loop `b0` carrier is no
  longer a separate producer debt: the `3+2+1+1` incidence carrier and the
  three Poincare generation slots determine all three one-loop coefficients and
  their residual self-bump laws.

  This file ties the two facts together.  The front door equipped with the
  unified one-loop carrier receipt is existence-equivalent to P420's front door,
  because P462 supplies the receipt unconditionally at the formal carrier
  level.  Thus the remaining physical debt is not "compute the one-loop
  representation coefficients"; it is the stronger RG/threshold/scale and
  physical-geometry faithfulness producer.
-/

import H0mework.Physics.RepresentationSources.P462

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Concrete front door with the one-loop carrier receipt attached -/

/-- P420's expanded concrete Standard-Model kernel, explicitly carrying the
P462 unified one-loop carrier receipt.

This is not a stronger physics assumption than P420: the extra field is
constructed by `RunningSigmaBeta.standardModelOneLoopCarrierFinalReceipt`. -/
structure ConcreteHolyGrailKernelWithOneLoopCarrier
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  kernel : ConcreteStandardModelHolyGrailProducerKernel Index A CKMCarrier
  oneLoop :
    RunningSigmaBeta.StandardModelOneLoopCarrierFinalReceipt

namespace ConcreteHolyGrailKernelWithOneLoopCarrier

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- Forgetting the P462 receipt recovers P420's expanded kernel. -/
def toConcreteKernel
    (K : ConcreteHolyGrailKernelWithOneLoopCarrier Index A CKMCarrier) :
    ConcreteStandardModelHolyGrailProducerKernel Index A CKMCarrier :=
  K.kernel

/-- THEOREM 2: the attached receipt exposes the unified three-factor one-loop
carrier formula. -/
theorem oneLoopReceipt
    (K : ConcreteHolyGrailKernelWithOneLoopCarrier Index A CKMCarrier) :
    RunningSigmaBeta.StandardModelOneLoopCarrierFinalReceipt :=
  K.oneLoop

end ConcreteHolyGrailKernelWithOneLoopCarrier

/-! ## Exact equivalence with P420's front door -/

/-- THEOREM 3: attaching the unified one-loop carrier receipt costs no new
existence assumption. -/
theorem concreteKernelWithOneLoop_nonempty_iff_concreteKernel
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (ConcreteHolyGrailKernelWithOneLoopCarrier
        Index A CKMCarrier) ↔
      Nonempty (ConcreteStandardModelHolyGrailProducerKernel
        Index A CKMCarrier) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.kernel⟩
  · rintro ⟨K⟩
    exact
      ⟨{ kernel := K
         oneLoop :=
          RunningSigmaBeta.standardModelOneLoopCarrierFinalReceipt }⟩

/-- THEOREM 4: the concrete Standard-Model holy-grail output exists iff the
expanded kernel with the P462 one-loop carrier receipt exists. -/
theorem standardModelPoincareHolyGrailOutput_nonempty_iff_kernelWithOneLoop
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) ↔
      Nonempty (ConcreteHolyGrailKernelWithOneLoopCarrier
        Index A CKMCarrier) := by
  exact
    standardModelPoincareHolyGrailOutput_nonempty_iff_concreteKernel.trans
      concreteKernelWithOneLoop_nonempty_iff_concreteKernel.symm

/-- THEOREM 5: the concrete Poincare-resolved surface can equivalently be read
as the raw P420 kernel plus the already-proved P462 one-loop carrier receipt. -/
theorem standardModelPoincareResolved_nonempty_iff_kernelWithOneLoop
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      Nonempty (ConcreteHolyGrailKernelWithOneLoopCarrier
        Index A CKMCarrier) := by
  exact
    standardModelPoincareResolved_nonempty_iff_concreteKernel.trans
      concreteKernelWithOneLoop_nonempty_iff_concreteKernel.symm

/-- THEOREM 6: compact citation form.  Any P420 kernel supplies both the P419
holy-grail output and the P462 unified one-loop carrier receipt. -/
theorem concreteKernel_outputs_holyGrail_and_oneLoopCarrier
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (ConcreteStandardModelHolyGrailProducerKernel
        Index A CKMCarrier) ->
      Nonempty (StandardModelPoincareHolyGrailOutput
        Index A CKMCarrier) ∧
        RunningSigmaBeta.StandardModelOneLoopCarrierFinalReceipt := by
  intro h
  exact
    ⟨output_of_concreteHolyGrailKernel h,
      RunningSigmaBeta.standardModelOneLoopCarrierFinalReceipt⟩

end StandardModelConstraint
end SaturationMonoid
