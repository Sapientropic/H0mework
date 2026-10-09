import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVelocity
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceResolventGraphSplice

/-! The actual native-charge insertion between the original two resolvents.
The finite-compression charge torque is retained through the unchanged
source filter; no completion-level charge conservation is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ChargeResolvent
open GaussCoreHilbert SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart
open FullYSourceResolventGraphSplice
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem compression_resolvent (C : E →L[ℂ] E) (self : IsSelfAdjoint C)
    (z : ℂ) (hz : z.im≠0) : C*FullYSourceResolventGraphSplice.resolvent C z=1+z • FullYSourceResolventGraphSplice.resolvent C z := by
  have h := resolvent_right C self z hz
  rw [sub_mul,smul_mul_assoc,one_mul] at h
  exact sub_eq_iff_eq_add.mp h

theorem finite_torque_identity (C Q : E →L[ℂ] E) (self : IsSelfAdjoint C)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    FullYSourceResolventGraphSplice.resolvent C z*(C*Q-Q*C)*FullYSourceResolventGraphSplice.resolvent C w =
      Q*FullYSourceResolventGraphSplice.resolvent C w-FullYSourceResolventGraphSplice.resolvent C z*Q+(z-w) • (FullYSourceResolventGraphSplice.resolvent C z*Q*FullYSourceResolventGraphSplice.resolvent C w) := by
  calc
    _ = (FullYSourceResolventGraphSplice.resolvent C z*C)*Q*FullYSourceResolventGraphSplice.resolvent C w-(FullYSourceResolventGraphSplice.resolvent C z*Q)*(C*FullYSourceResolventGraphSplice.resolvent C w) := by noncomm_ring
    _ = _ := by
      rw [resolvent_compression C self z hz,compression_resolvent C self w hw]
      simp only [add_mul,one_mul,mul_add,mul_one,mul_smul_comm,smul_mul_assoc,sub_smul]
      abel

end Finite

def finiteVertex (a : NativeLie) (z w : ℂ) (F : Index) : H →L[ℂ] H :=
  finiteResolvent F z*chargeReader a*finiteResolvent F w

def finiteTorque (a : NativeLie) (z w : ℂ) (F : Index) : H →L[ℂ] H :=
  finiteResolvent F z*(GaussGradedCompression.compression F*chargeReader a-
    chargeReader a*GaussGradedCompression.compression F)*finiteResolvent F w

theorem finite_torque_return (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    finiteTorque a z w F=chargeReader a*finiteResolvent F w-finiteResolvent F z*chargeReader a+
      (z-w) • finiteVertex a z w F :=
  finite_torque_identity _ _ (GaussGradedCompression.compression_selfAdjoint F) z w hz hw

def vertexFamily (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) : Operator Index H :=
  comp (comp (resolventFamily z hz) (constant (chargeReader a))) (resolventFamily w hw)

private def torqueExpression (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) : Operator Index H :=
  add (add (comp (constant (chargeReader a)) (resolventFamily w hw))
    (comp (resolventFamily z hz) (constant (-chargeReader a))))
    (comp (constant ((z-w) • (1 : H →L[ℂ] H))) (vertexFamily a z w hz hw))

private theorem torque_expression_component (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (F : Index) : (torqueExpression a z w hz hw).component F=finiteTorque a z w F := by
  rw [finite_torque_return a z w hz hw F]
  change chargeReader a*finiteResolvent F w+finiteResolvent F z*(-chargeReader a)+
    ((z-w) • (1 : H →L[ℂ] H))*(finiteResolvent F z*chargeReader a*finiteResolvent F w)=_
  apply ContinuousLinearMap.ext
  intro x
  change chargeReader a (finiteResolvent F w x)+finiteResolvent F z (-(chargeReader a x))+
    (z-w) • (finiteResolvent F z (chargeReader a (finiteResolvent F w x))) = _
  rw [map_neg]
  simp only [finiteVertex,add_apply,smul_apply,mul_apply_eq_comp,sub_eq_add_neg,neg_apply]

def torqueFamily (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) : Operator Index H where
  component := finiteTorque a z w
  bounded := ⟨bound (torqueExpression a z w hz hw),bound_nonneg _,fun F x => by
    rw [←torque_expression_component a z w hz hw F]
    exact bound_apply (torqueExpression a z w hz hw) F x⟩

def vertex (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (vertexFamily a z w hz hw)

def torque (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (torqueFamily a z w hz hw)

theorem vertex_return (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    vertex a z w hz hw=sameResolvent z hz*reader (chargeReader a)*sameResolvent w hw := by
  simp only [vertex,vertexFamily,lift_comp]
  rfl

theorem torque_return (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    torque a z w hz hw=reader (chargeReader a)*sameResolvent w hw-
      sameResolvent z hz*reader (chargeReader a)+(z-w) • vertex a z w hz hw := by
  have h := lift_congr sourceFilter (torqueFamily a z w hz hw) (torqueExpression a z w hz hw)
    (fun F => (torque_expression_component a z w hz hw F).symm)
  simp only [torqueExpression,lift_add,lift_comp] at h
  have negQ : lift sourceFilter (constant (-chargeReader a)) = -reader (chargeReader a) := by
    simpa only [GaussUnitaryHistory.reader,neg_one_smul] using
      (SourceFamilyOperator.constant_smul sourceFilter (-1 : ℂ) (chargeReader a))
  have scalar : lift sourceFilter (constant ((z-w) • (1 : H →L[ℂ] H))) =
      (z-w) • (1 : HistorySpace →L[ℂ] HistorySpace) := by
    rw [SourceFamilyOperator.constant_smul,lift_identity]
  simp only [negQ,scalar] at h
  change torque a z w hz hw=reader (chargeReader a)*sameResolvent w hw+
    sameResolvent z hz*(-reader (chargeReader a))+
    ((z-w) • (1 : HistorySpace →L[ℂ] HistorySpace))*vertex a z w hz hw at h
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x) h
  simpa only [add_apply,sub_apply,smul_apply,neg_apply,mul_apply_eq_comp,one_apply_eq_self,
    map_neg,sub_eq_add_neg] using hx

theorem same_source_charge_ward (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    (z-w) • vertex a z w hz hw=sameResolvent z hz*reader (chargeReader a)-
      reader (chargeReader a)*sameResolvent w hw+torque a z w hz hw := by
  rw [torque_return a z w hz hw]
  abel

theorem zero_transfer_torque (a : NativeLie) (z : ℂ) (hz : z.im≠0) :
    torque a z z hz hz=reader (chargeReader a)*sameResolvent z hz-
      sameResolvent z hz*reader (chargeReader a) := by
  have h := torque_return a z z hz hz
  simpa only [sub_self,zero_smul,add_zero] using h

end LowEnergy.GaussComposite.ChargeResolvent
