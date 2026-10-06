import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPhysicalYResolvent
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPhysicalWardCore

/-! The original charge vertex uses both actual physical momenta and every
Yukawa term. Its Ward insertion is the literal full Hamiltonian difference;
the complete configuration torque remains in the original core return. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalWard
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalPhysicalResolvent
open CanonicalPhysicalYResolvent (finiteFull fullFamily fullResolvent)
open CanonicalGradedCharge (chargeReader chargeMatrix)
open CanonicalGradedCurrent (sourceProjection sourceLabel historyProjection)
open FullYSourceCutoffVolterra (cutoff)
open SourceQuantumScalarChart (NativeLie)
open SourceFamilyOperator
open GaussUnitaryHistory (Index sourceFilter HistorySpace reader inclusion)
open scoped Topology InnerProductSpace
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem inverse_commutes {R : Type*} [Monoid R] (P D U : R)
    (left : U*D=1) (right : D*U=1) (commutes : P*D=D*P) : P*U=U*P := by
  calc
    P*U = (U*D)*(P*U) := by rw [left, one_mul]
    _ = U*(D*P)*U := by simp only [mul_assoc]
    _ = U*(P*D)*U := by rw [commutes]
    _ = (U*P)*(D*U) := by simp only [mul_assoc]
    _ = U*P := by rw [right, mul_one]

private theorem two_inverse_ward {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Co Ci Ro Ri Q : E →L[ℂ] E) (z w : ℂ)
    (left : Ro*(Co-z • 1)=1) (right : (Ci-w • 1)*Ri=1) :
    Ro*(Co*Q-Q*Ci)*Ri=Q*Ri-Ro*Q+(z-w) • (Ro*Q*Ri) := by
  have first : Ro*Co=1+z • Ro := by
    rw [mul_sub, mul_smul_comm, mul_one] at left
    exact sub_eq_iff_eq_add.mp left
  have second : Ci*Ri=1+w • Ri := by
    rw [sub_mul, smul_mul_assoc, one_mul] at right
    exact sub_eq_iff_eq_add.mp right
  calc
    _ = (Ro*Co)*Q*Ri-(Ro*Q)*(Ci*Ri) := by noncomm_ring
    _ = _ := by
      rw [first, second]
      simp only [add_mul, one_mul, mul_add, mul_one, mul_smul_comm, smul_mul_assoc, sub_smul]
      abel

private theorem left_vertex_return {R : Type*} [Monoid R] (P U V A B Q : R)
    (left : P*U=P*A) (right : P*V=P*B) (pA : Commute P A) (pQ : Commute P Q) :
    P*(U*Q*V)=P*(A*Q*B) := by
  have route (X : R) : P*(A*Q*X)=(A*Q)*(P*X) := by
    calc
      _ = ((P*A)*Q)*X := by simp only [mul_assoc]
      _ = A*(P*Q)*X := by rw [pA.eq]; simp only [mul_assoc]
      _ = (A*Q)*(P*X) := by rw [pQ.eq]; simp only [mul_assoc]
  calc
    _ = P*(A*Q*V) := by simp only [← mul_assoc]; rw [left]
    _ = (A*Q)*(P*V) := route V
    _ = (A*Q)*(P*B) := by rw [right]
    _ = P*(A*Q*B) := (route B).symm

theorem finite_resolvent_blocks (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    Commute sourceProjection (finiteResolvent p F z) := by
  have shifted := (compression_blocks p F sourceLabel).sub_right
    ((Commute.one_right sourceProjection).smul_right z)
  exact inverse_commutes _ _ _
    (FullYSourceResolventGraphSplice.resolvent_left _ (compression_selfAdjoint p F) z hz)
    (FullYSourceResolventGraphSplice.resolvent_right _ (compression_selfAdjoint p F) z hz) shifted.eq

theorem source_resolvent_blocks (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) :
    Commute historyProjection (sourceResolvent p z hz) := by
  change lift sourceFilter (constant sourceProjection)*lift sourceFilter (resolventFamily p z hz) =
    lift sourceFilter (resolventFamily p z hz)*lift sourceFilter (constant sourceProjection)
  calc
    _ = lift sourceFilter (comp (constant sourceProjection) (resolventFamily p z hz)) :=
      (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (resolventFamily p z hz) (constant sourceProjection)) :=
      lift_congr sourceFilter _ _ (fun F => (finite_resolvent_blocks p F z hz).eq)
    _ = _ := lift_comp sourceFilter _ _

theorem charge_blocks (a : NativeLie) : Commute sourceProjection (chargeReader a) :=
  CanonicalGradedCurrent.boundedMatrix_blocks (chargeMatrix a)
    (CanonicalGradedCurrent.gaugeMatrix_preserves 0 .temporal a) sourceLabel

theorem history_charge_blocks (a : NativeLie) : Commute historyProjection (reader (chargeReader a)) := by
  change reader sourceProjection*reader (chargeReader a)=reader (chargeReader a)*reader sourceProjection
  rw [← GaussUnitaryHistory.reader_mul, ← GaussUnitaryHistory.reader_mul]
  exact congrArg reader (charge_blocks a).eq

def finiteVertex (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ) (F : Index) : H →L[ℂ] H :=
  finiteFull (p+k) F cut z*chargeReader a*finiteFull p F cut w

def finiteInsertion (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (F : Index) : H →L[ℂ] H :=
  (compression (p+k) F+cutoff cut)*chargeReader a-chargeReader a*(compression p F+cutoff cut)

def finiteResponse (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ) (F : Index) : H →L[ℂ] H :=
  finiteFull (p+k) F cut z*finiteInsertion p k a cut F*finiteFull p F cut w

theorem finite_ward (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    finiteResponse p k a cut z w F=chargeReader a*finiteFull p F cut w-
      finiteFull (p+k) F cut z*chargeReader a+(z-w) • finiteVertex p k a cut z w F :=
  two_inverse_ward _ _ _ _ _ z w
    (CanonicalPhysicalYResolvent.finiteFull_left (p+k) F cut z hz)
    (CanonicalPhysicalYResolvent.finiteFull_right p F cut w hw)

def vertexFamily (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : Operator Index H :=
  comp (comp (fullFamily (p+k) cut z hz) (constant (chargeReader a))) (fullFamily p cut w hw)

private def responseExpression (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : Operator Index H :=
  add (add (comp (constant (chargeReader a)) (fullFamily p cut w hw))
    (comp (fullFamily (p+k) cut z hz) (constant (-chargeReader a))))
    (comp (constant ((z-w) • (1 : H →L[ℂ] H))) (vertexFamily p k a cut z w hz hw))

private theorem responseExpression_component (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    (responseExpression p k a cut z w hz hw).component F=finiteResponse p k a cut z w F := by
  rw [finite_ward p k a cut z w hz hw F]
  change chargeReader a*finiteFull p F cut w+finiteFull (p+k) F cut z*(-chargeReader a)+
    ((z-w) • (1 : H →L[ℂ] H))*(finiteFull (p+k) F cut z*chargeReader a*finiteFull p F cut w)=_
  apply ContinuousLinearMap.ext
  intro x
  change chargeReader a (finiteFull p F cut w x)+finiteFull (p+k) F cut z (-(chargeReader a x))+
    (z-w) • (finiteFull (p+k) F cut z (chargeReader a (finiteFull p F cut w x))) = _
  rw [map_neg]
  simp only [finiteVertex, add_apply, smul_apply, mul_apply_eq_comp, sub_eq_add_neg, neg_apply]

def responseFamily (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : Operator Index H where
  component := finiteResponse p k a cut z w
  bounded := ⟨bound (responseExpression p k a cut z w hz hw), bound_nonneg _, fun F x => by
    rw [← responseExpression_component p k a cut z w hz hw F]
    exact bound_apply (responseExpression p k a cut z w hz hw) F x⟩

def vertex (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (vertexFamily p k a cut z w hz hw)

def response (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily p k a cut z w hz hw)

theorem vertex_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    vertex p k a cut z w hz hw=fullResolvent (p+k) cut z hz*reader (chargeReader a)*fullResolvent p cut w hw := by
  simp only [vertex, vertexFamily, lift_comp]
  rfl

theorem response_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    response p k a cut z w hz hw=reader (chargeReader a)*fullResolvent p cut w hw-
      fullResolvent (p+k) cut z hz*reader (chargeReader a)+(z-w) • vertex p k a cut z w hz hw := by
  have h := lift_congr sourceFilter (responseFamily p k a cut z w hz hw)
    (responseExpression p k a cut z w hz hw)
    (fun F => (responseExpression_component p k a cut z w hz hw F).symm)
  simp only [responseExpression, lift_add, lift_comp] at h
  have negQ : lift sourceFilter (constant (-chargeReader a)) = -reader (chargeReader a) := by
    simpa only [GaussUnitaryHistory.reader, neg_one_smul] using
      (SourceFamilyOperator.constant_smul sourceFilter (-1 : ℂ) (chargeReader a))
  have scalar : lift sourceFilter (constant ((z-w) • (1 : H →L[ℂ] H))) =
      (z-w) • (1 : HistorySpace →L[ℂ] HistorySpace) := by
    exact (SourceFamilyOperator.constant_smul sourceFilter (z-w) (1 : H →L[ℂ] H)).trans
      (congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => (z-w) • T) (lift_identity sourceFilter))
  simp only [negQ, scalar] at h
  change response p k a cut z w hz hw=reader (chargeReader a)*fullResolvent p cut w hw+
    fullResolvent (p+k) cut z hz*(-reader (chargeReader a))+
    ((z-w) • (1 : HistorySpace →L[ℂ] HistorySpace))*vertex p k a cut z w hz hw at h
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x) h
  simpa only [add_apply, sub_apply, smul_apply, neg_apply, mul_apply_eq_comp, one_apply_eq_self,
    map_neg, sub_eq_add_neg] using hx

private theorem ward_rearrange {R : Type*} [AddCommGroup R] (d x y t : R)
    (h : t=y-x+d) : d=x-y+t := by rw [h]; abel

theorem full_charge_ward (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    (z-w) • vertex p k a cut z w hz hw=fullResolvent (p+k) cut z hz*reader (chargeReader a)-
      reader (chargeReader a)*fullResolvent p cut w hw+response p k a cut z w hz hw := by
  exact ward_rearrange _ _ _ _ (response_return p k a cut z w hz hw)

theorem projected_vertex_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    historyProjection*vertex p k a cut z w hz hw =
      historyProjection*(sourceResolvent (p+k) z hz*reader (chargeReader a)*sourceResolvent p w hw) := by
  rw [vertex_return]
  exact left_vertex_return _ _ _ _ _ _
    (CanonicalPhysicalYResolvent.completed_left_return (p+k) cut z hz)
    (CanonicalPhysicalYResolvent.completed_left_return p cut w hw)
    (source_resolvent_blocks (p+k) z hz) (history_charge_blocks a)

theorem charge_bound (a : NativeLie) (x : HistorySpace) :
    ‖reader (chargeReader a) x‖ ≤ ‖chargeReader a‖*‖x‖ := by
  exact SourceBoundaryGram.lift_bound_explicit sourceFilter (constant (chargeReader a))
    ‖chargeReader a‖ (norm_nonneg _) (fun _ => (chargeReader a).le_opNorm) x

theorem projected_vertex_bound (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (x : HistorySpace) :
    ‖historyProjection (vertex p k a cut z w hz hw x)‖ ≤
      ((1/|z.im|)*‖chargeReader a‖*(1/|w.im|))*‖x‖ := by
  have returned := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x)
    (projected_vertex_return p k a cut z w hz hw)
  change historyProjection (vertex p k a cut z w hz hw x)=
    historyProjection (sourceResolvent (p+k) z hz (reader (chargeReader a) (sourceResolvent p w hw x))) at returned
  rw [returned]
  calc
    _ ≤ ‖sourceResolvent (p+k) z hz (reader (chargeReader a) (sourceResolvent p w hw x))‖ :=
      CanonicalPhysicalYResolvent.projection_bound _
    _ ≤ (1/|z.im|)*‖reader (chargeReader a) (sourceResolvent p w hw x)‖ := resolvent_bound _ _ _ _
    _ ≤ (1/|z.im|)*(‖chargeReader a‖*‖sourceResolvent p w hw x‖) :=
      mul_le_mul_of_nonneg_left (charge_bound a _) (by positivity)
    _ ≤ (1/|z.im|)*(‖chargeReader a‖*((1/|w.im|)*‖x‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (resolvent_bound p w hw x) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

private theorem projected_response_identity {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Q U V A B W X : E →L[ℂ] E) (d : ℂ)
    (hW : W=Q*V-U*Q+d • X) (hU : P*U=P*A) (hV : P*V=P*B)
    (hQ : Commute P Q) (hX : P*X=P*(A*Q*B)) :
    P*W=P*(Q*B-A*Q+d • (A*Q*B)) := by
  have qr : P*(Q*V)=P*(Q*B) := by
    calc
      _ = Q*(P*V) := by rw [← mul_assoc, hQ.eq, mul_assoc]
      _ = _ := by rw [hV, ← mul_assoc, ← hQ.eq, mul_assoc]
  have rq : P*(U*Q)=P*(A*Q) := by rw [← mul_assoc, ← mul_assoc, hU]
  rw [hW, mul_add, mul_sub, qr, rq, mul_smul_comm, hX, mul_add, mul_sub, mul_smul_comm]

theorem projected_response_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    historyProjection*response p k a cut z w hz hw = historyProjection*
      (reader (chargeReader a)*sourceResolvent p w hw-sourceResolvent (p+k) z hz*reader (chargeReader a)+
        (z-w) • (sourceResolvent (p+k) z hz*reader (chargeReader a)*sourceResolvent p w hw)) :=
  projected_response_identity _ _ _ _ _ _ _ _ (z-w)
    (response_return p k a cut z w hz hw)
    (CanonicalPhysicalYResolvent.completed_left_return (p+k) cut z hz)
    (CanonicalPhysicalYResolvent.completed_left_return p cut w hw)
    (history_charge_blocks a) (projected_vertex_return p k a cut z w hz hw)

theorem projected_vertex_cutoff_independent (p k : PhysicalMomentum) (a : NativeLie) (cut other : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    historyProjection*vertex p k a cut z w hz hw=historyProjection*vertex p k a other z w hz hw :=
  (projected_vertex_return p k a cut z w hz hw).trans (projected_vertex_return p k a other z w hz hw).symm

theorem projected_response_cutoff_independent (p k : PhysicalMomentum) (a : NativeLie) (cut other : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    historyProjection*response p k a cut z w hz hw=historyProjection*response p k a other z w hz hw :=
  (projected_response_return p k a cut z w hz hw).trans (projected_response_return p k a other z w hz hw).symm

private theorem insertion_projection {R : Type*} [Ring R] (P Co Ci Y Q : R)
    (hY : P*Y=0) (hQ : Commute P Q) :
    P*((Co+Y)*Q-Q*(Ci+Y))=P*(Co*Q-Q*Ci) := by
  calc
    _ = P*(Co*Q-Q*Ci)+(P*Y)*Q-(P*Q)*Y := by noncomm_ring
    _ = _ := by rw [hY, zero_mul, add_zero, hQ.eq, mul_assoc, hY, mul_zero, sub_zero]

theorem insertion_projected (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (F : Index) :
    sourceProjection*finiteInsertion p k a cut F =
      sourceProjection*(compression (p+k) F*chargeReader a-chargeReader a*compression p F) := by
  have py : sourceProjection*cutoff cut=0 :=
    CanonicalGradedCurrent.positive_grade_left_zero _ 1
      (by simpa only [Nat.cast_one, one_smul] using FullYSourceCutoffVolterra.cutoff_raises cut) (by norm_num)
  exact insertion_projection _ _ _ _ _ py (charge_blocks a)

theorem full_insertion_source_eventually (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (f : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),
      (sourceProjection*finiteInsertion p k a cut F) (sourceProjection (embed f)) =
        sourceProjection (embed (CanonicalPhysicalWardCore.configurationTorque a (GaussCoreLabel.project sourceLabel f)+
          CanonicalPhysicalWardCore.currentAction k a (GaussCoreLabel.project sourceLabel f))) := by
  filter_upwards [CanonicalPhysicalWardCore.finite_charge_ward_eventually p k a f] with F source
  rw [insertion_projected]
  exact congrArg sourceProjection source

end LowEnergy.CanonicalPhysicalWard
