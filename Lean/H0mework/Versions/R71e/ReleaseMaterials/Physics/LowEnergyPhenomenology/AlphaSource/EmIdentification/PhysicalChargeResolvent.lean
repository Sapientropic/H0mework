import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ChargeResolvent
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalResolvent

/-! The charge vertex between two actual physical resolvents. The two legs
propagate at independent unlocalized momenta p and p+k; the complete
compression Ward difference is retained as the torque term and is not set
to zero or declared a boundary contribution. At p=k=0 the construction
returns the signed same-source charge Ward identity. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalCharge
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open GaussDiagonalHistory (diagonalAction)
open CanonicalPhysicalSpatial CanonicalPhysicalResolvent
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem two_resolvent_ward (A B Q : E →L[ℂ] E) (selfA : IsSelfAdjoint A) (selfB : IsSelfAdjoint B)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    FullYSourceResolventGraphSplice.resolvent A z*(A*Q-Q*B)*FullYSourceResolventGraphSplice.resolvent B w =
      Q*FullYSourceResolventGraphSplice.resolvent B w-FullYSourceResolventGraphSplice.resolvent A z*Q+
        (z-w) • (FullYSourceResolventGraphSplice.resolvent A z*Q*
          FullYSourceResolventGraphSplice.resolvent B w) := by
  calc
    _ = (FullYSourceResolventGraphSplice.resolvent A z*A)*Q*
          FullYSourceResolventGraphSplice.resolvent B w-
        (FullYSourceResolventGraphSplice.resolvent A z*Q)*
          (B*FullYSourceResolventGraphSplice.resolvent B w) := by noncomm_ring
    _ = _ := by
      rw [FullYSourceResolventGraphSplice.resolvent_compression A selfA z hz,
        ChargeResolvent.compression_resolvent B selfB w hw]
      simp only [add_mul,one_mul,mul_add,mul_one,mul_smul_comm,smul_mul_assoc,sub_smul]
      abel

end Finite

def finiteVertex (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (F : Index) : H →L[ℂ] H :=
  finiteResolvent (p+k) F z*Q*finiteResolvent p F w

def finiteTorque (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (F : Index) : H →L[ℂ] H :=
  finiteResolvent (p+k) F z*(compression (p+k) F*Q-Q*compression p F)*finiteResolvent p F w

theorem finite_torque_return (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    finiteTorque Q p k z w F=Q*finiteResolvent p F w-finiteResolvent (p+k) F z*Q+
      (z-w) • finiteVertex Q p k z w F :=
  two_resolvent_ward _ _ _ (compression_selfAdjoint (p+k) F) (compression_selfAdjoint p F) z w hz hw

theorem finite_vertex_add (Q S : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (F : Index) :
    finiteVertex (Q+S) p k z w F=finiteVertex Q p k z w F+finiteVertex S p k z w F := by
  simp only [finiteVertex]
  noncomm_ring

theorem finite_torque_add (Q S : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (F : Index) :
    finiteTorque (Q+S) p k z w F=finiteTorque Q p k z w F+finiteTorque S p k z w F := by
  simp only [finiteTorque]
  rw [show compression (p+k) F*(Q+S)-(Q+S)*compression p F=
    (compression (p+k) F*Q-Q*compression p F)+(compression (p+k) F*S-S*compression p F) by noncomm_ring]
  noncomm_ring

def vertexFamily (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    Operator Index H :=
  comp (comp (resolventFamily (p+k) z hz) (constant Q)) (resolventFamily p w hw)

private def torqueExpression (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : Operator Index H :=
  add (add (comp (constant Q) (resolventFamily p w hw))
    (comp (resolventFamily (p+k) z hz) (constant (-Q))))
    (comp (constant ((z-w) • (1 : H →L[ℂ] H))) (vertexFamily Q p k z w hz hw))

private theorem torque_expression_component (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (F : Index) :
    (torqueExpression Q p k z w hz hw).component F=finiteTorque Q p k z w F := by
  rw [finite_torque_return Q p k z w hz hw F]
  change Q*finiteResolvent p F w+finiteResolvent (p+k) F z*(-Q)+
    ((z-w) • (1 : H →L[ℂ] H))*(finiteResolvent (p+k) F z*Q*finiteResolvent p F w)=_
  apply ContinuousLinearMap.ext
  intro x
  change Q (finiteResolvent p F w x)+finiteResolvent (p+k) F z (-(Q x))+
    (z-w) • (finiteResolvent (p+k) F z (Q (finiteResolvent p F w x))) = _
  rw [map_neg]
  simp only [finiteVertex,add_apply,smul_apply,mul_apply_eq_comp,sub_eq_add_neg,neg_apply]

def torqueFamily (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    Operator Index H where
  component := finiteTorque Q p k z w
  bounded := ⟨bound (torqueExpression Q p k z w hz hw),bound_nonneg _,fun F x => by
    rw [←torque_expression_component Q p k z w hz hw F]
    exact bound_apply (torqueExpression Q p k z w hz hw) F x⟩

def vertex (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (vertexFamily Q p k z w hz hw)

def torque (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (torqueFamily Q p k z w hz hw)

theorem vertex_return (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    vertex Q p k z w hz hw=sourceResolvent (p+k) z hz*reader Q*sourceResolvent p w hw := by
  simp only [vertex,vertexFamily,lift_comp]
  rfl

theorem torque_return (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    torque Q p k z w hz hw=reader Q*sourceResolvent p w hw-sourceResolvent (p+k) z hz*reader Q+
      (z-w) • vertex Q p k z w hz hw := by
  have h := lift_congr sourceFilter (torqueFamily Q p k z w hz hw) (torqueExpression Q p k z w hz hw)
    (fun F => (torque_expression_component Q p k z w hz hw F).symm)
  simp only [torqueExpression,lift_add,lift_comp] at h
  have negQ : lift sourceFilter (constant (-Q)) = -reader Q := by
    simpa only [GaussUnitaryHistory.reader,neg_one_smul] using
      (SourceFamilyOperator.constant_smul sourceFilter (-1 : ℂ) Q)
  have scalar : lift sourceFilter (constant ((z-w) • (1 : H →L[ℂ] H))) =
      (z-w) • (1 : HistorySpace →L[ℂ] HistorySpace) := by
    rw [SourceFamilyOperator.constant_smul,lift_identity]
  simp only [negQ,scalar] at h
  change torque Q p k z w hz hw=reader Q*sourceResolvent p w hw+
    sourceResolvent (p+k) z hz*(-reader Q)+
    ((z-w) • (1 : HistorySpace →L[ℂ] HistorySpace))*vertex Q p k z w hz hw at h
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x) h
  simpa only [add_apply,sub_apply,smul_apply,neg_apply,mul_apply_eq_comp,one_apply_eq_self,
    map_neg,sub_eq_add_neg] using hx

/-- The charge vertex between the physical resolvents at momenta p+k and p
obeys the same-source Ward identity; the retained torque is the complete
finite Ward difference and is not decomposed or removed. -/
theorem physical_charge_ward (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    (z-w) • vertex Q p k z w hz hw=sourceResolvent (p+k) z hz*reader Q-
      reader Q*sourceResolvent p w hw+torque Q p k z w hz hw := by
  rw [torque_return Q p k z w hz hw]
  abel

theorem vertex_add (Q S : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    vertex (Q+S) p k z w hz hw=vertex Q p k z w hz hw+vertex S p k z w hz hw :=
  (lift_congr sourceFilter _ _ (fun F => finite_vertex_add Q S p k z w F)).trans
    (lift_add sourceFilter _ _)

theorem torque_add (Q S : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    torque (Q+S) p k z w hz hw=torque Q p k z w hz hw+torque S p k z w hz hw :=
  (lift_congr sourceFilter _ _ (fun F => finite_torque_add Q S p k z w F)).trans
    (lift_add sourceFilter _ _)

/-- The resolvent-pair part of the increment vertex: at unit charge the
Ward identity returns the two physical resolvents' difference plus the
actual momentum-transfer compression difference, retained without
simplification. -/
theorem one_torque (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    (z-w) • vertex (1 : H →L[ℂ] H) p k z w hz hw=sourceResolvent (p+k) z hz-
      sourceResolvent p w hw+torque (1 : H →L[ℂ] H) p k z w hz hw := by
  have h := physical_charge_ward (1 : H →L[ℂ] H) p k z w hz hw
  simpa only [GaussUnitaryHistory.reader_one,mul_one,one_mul] using h

theorem vertex_original (Q : H →L[ℂ] H) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    vertex Q 0 0 z w hz hw=FullYSourceResolventGraphSplice.sameResolvent z hz*reader Q*
      FullYSourceResolventGraphSplice.sameResolvent w hw := by
  rw [vertex_return]
  simp only [add_zero,resolvent_original]

theorem vertex_original_ward (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    vertex (chargeReader a) 0 0 z w hz hw=ChargeResolvent.vertex a z w hz hw := by
  rw [vertex_original,ChargeResolvent.vertex_return]

theorem torque_original (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    torque (chargeReader a) 0 0 z w hz hw=ChargeResolvent.torque a z w hz hw := by
  rw [torque_return]
  simp only [add_zero,resolvent_original,vertex_original_ward a z w hz hw]
  exact (ChargeResolvent.torque_return a z w hz hw).symm

/-- The signed k=0 identity is the literal restriction of the physical
Ward: at zero transfer both legs use the original resolvent. -/
theorem physical_charge_ward_original (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    (z-w) • vertex (chargeReader a) 0 0 z w hz hw=
      FullYSourceResolventGraphSplice.sameResolvent z hz*reader (chargeReader a)-
      reader (chargeReader a)*FullYSourceResolventGraphSplice.sameResolvent w hw+
        ChargeResolvent.torque a z w hz hw := by
  have h := physical_charge_ward (chargeReader a) 0 0 z w hz hw
  simp only [add_zero,resolvent_original] at h
  rwa [←torque_original a z w hz hw]

private theorem physical_embed (q : PhysicalMomentum) (g : QuantumTest) :
    physical q (coreEquiv g)=embed (physicalAction q g) := by
  rw [physical_core]
  change embed (diagonalAction g)+embed (momentumAction q g)=
    embed (diagonalAction g+momentumAction q g)
  rw [←map_add]

/-- On an embedded test leg the finite Ward difference is eventually the
unlocalized physical action difference: no localizer and no charge
conservation assumption, and both physical principals act on the same
source core. -/
theorem finite_ward_eventually (a : NativeLie) (p k : PhysicalMomentum) (f : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),
      (compression (p+k) F*chargeReader a-chargeReader a*compression p F) (embed f)=
        embed (physicalAction (p+k) (chargeAction a f)-chargeAction a (physicalAction p f)) := by
  have left (g : QuantumTest) (q : PhysicalMomentum) :
      ∀ᶠ F in (sourceFilter : Filter Index),
        compression q F (chargeReader a (embed g))=embed (physicalAction q (chargeAction a g)) := by
    filter_upwards [eventually_exact q (coreEquiv (chargeAction a g))] with F hF
    rw [chargeReader_core]
    change compression q F ↑(coreEquiv (chargeAction a g))=_
    rw [hF,physical_embed]
  have right : ∀ᶠ F in (sourceFilter : Filter Index),
      chargeReader a (compression p F (embed f))=embed (chargeAction a (physicalAction p f)) := by
    filter_upwards [eventually_exact p (coreEquiv f)] with F hF
    change chargeReader a (compression p F ↑(coreEquiv f))=_
    rw [hF,physical_embed,chargeReader_core]
  filter_upwards [left f (p+k),right] with F hout hin
  simp only [mul_apply_eq_comp,sub_apply,hout,hin,←map_sub]

private theorem reader_norm (A : H →L[ℂ] H) : ‖reader A‖≤‖A‖ :=
  CanonicalGradedVariation.lift_bound sourceFilter (constant A) ‖A‖ (norm_nonneg _) (fun _ => le_rfl)

theorem vertex_bound (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (x : HistorySpace) :
    ‖vertex Q p k z w hz hw x‖≤‖Q‖*(1/|z.im|)*(1/|w.im|)*‖x‖ := by
  rw [vertex_return]
  calc
    ‖sourceResolvent (p+k) z hz (reader Q (sourceResolvent p w hw x))‖≤
        (1/|z.im|)*‖reader Q (sourceResolvent p w hw x)‖ := resolvent_bound (p+k) z hz _
    _ ≤ (1/|z.im|)*(‖Q‖*‖sourceResolvent p w hw x‖) :=
      mul_le_mul_of_nonneg_left (((reader Q).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (reader_norm Q) (norm_nonneg _))) (by positivity)
    _ ≤ (1/|z.im|)*(‖Q‖*((1/|w.im|)*‖x‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (resolvent_bound p w hw x) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

end LowEnergy.GaussComposite.PhysicalCharge
