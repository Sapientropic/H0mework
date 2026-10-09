import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalWard

/-! Source core endpoints remove both complete resolvents without postulating
an unbounded current sandwich on the completed carrier. The original weighted
Hilbert pairing keeps the cutoff-Y adjoint in its actual left endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalWardEndpoints
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussFockPair
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open CanonicalPhysicalYResolvent CanonicalPhysicalWard
open CanonicalGradedCharge (chargeReader chargeAction)
open CanonicalGradedCurrent (sourceProjection sourceLabel historyProjection)
open SourceQuantumScalarChart (NativeLie)
open FullYSourceCutoffVolterra (cutoff)
open SourceFamilyOperator SourceFamilyHilbert Filter
open GaussUnitaryHistory (Index sourceFilter HistorySpace reader inclusion)
open scoped Topology InnerProductSpace

def shifted (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (f : diagonal.domain) : H :=
  physical p f+cutoff cut (f : H)-z • (f : H)

def adjointShifted (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (f : diagonal.domain) : H :=
  physical p f+(cutoff cut).adjoint (f : H)-star z • (f : H)

private theorem inverse_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (C Y R : E →L[ℂ] E) (z : ℂ) (symmetric : ∀ x y, inner ℂ (C x) y=inner ℂ x (C y))
    (inverse : (C+Y-z • 1)*R=1) (x y : E) :
    inner ℂ (C x+Y.adjoint x-star z • x) (R y)=inner ℂ x y := by
  have returns := congrArg (fun A : E →L[ℂ] E => A y) inverse
  change C (R y)+Y (R y)-z • R y=y at returns
  rw [inner_sub_left, inner_add_left, inner_smul_left, starRingEnd_apply, star_star,
    symmetric, Y.adjoint_inner_left]
  rw [← inner_add_right, ← inner_smul_right, ← inner_sub_right, returns]

theorem finite_source_pair (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (f : diagonal.domain) (exactCore : compression p F (f : H)=physical p f) (y : H) :
    inner ℂ (adjointShifted p cut z f) (finiteFull p F cut z y)=inner ℂ (f : H) y := by
  simpa only [exactCore, adjointShifted] using inverse_pair _ _ _ z (compression_pair p F)
    (finiteFull_right p F cut z hz) (f : H) y

theorem whole_source_pair (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (f : diagonal.domain) (y : HistorySpace) :
    inner ℂ (inclusion (adjointShifted p cut z f)) (fullResolvent p cut z hz y) =
      inner ℂ (inclusion (f : H)) y := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  change inner ℂ ((SourceFamilyHilbert.constant sourceFilter (adjointShifted p cut z f)) : HistorySpace)
      (lift sourceFilter (fullFamily p cut z hz) (g : HistorySpace)) =
    inner ℂ ((SourceFamilyHilbert.constant sourceFilter (f : H)) : HistorySpace) (g : HistorySpace)
  rw [lift_coe, inner_coe, inner_coe]
  apply tendsto_nhds_unique
    (pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter (adjointShifted p cut z f))
      (act sourceFilter (fullFamily p cut z hz) g))
  apply (pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter (f : H)) g).congr'
  filter_upwards [eventually_exact p f] with F exactCore
  exact (finite_source_pair p F cut z hz f exactCore (value g F)).symm

private theorem vertex_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ro Ri Q : E →L[ℂ] E) (left f input g : E)
    (left_pair : ∀ y, inner ℂ left (Ro y)=inner ℂ f y) (right : Ri input=g) :
    inner ℂ left ((Ro*Q*Ri) input)=inner ℂ f (Q g) := by
  simp only [mul_apply_eq_comp, right, left_pair]

theorem vertex_endpoints (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (f g : QuantumTest) :
    inner ℂ (inclusion (adjointShifted (p+k) cut z (coreEquiv f)))
      (vertex p k a cut z w hz hw (inclusion (shifted p cut w (coreEquiv g)))) =
        sourcePair f (chargeAction a g) := by
  have right : fullResolvent p cut w hw (inclusion (shifted p cut w (coreEquiv g)))=inclusion (embed g) :=
    CanonicalPhysicalYResolvent.full_shifted_core_return p cut w hw (coreEquiv g)
  have first := congrArg (fun A : HistorySpace →L[ℂ] HistorySpace =>
    inner ℂ (inclusion (adjointShifted (p+k) cut z (coreEquiv f)))
      (A (inclusion (shifted p cut w (coreEquiv g))))) (vertex_return p k a cut z w hz hw)
  have middle := vertex_pair (fullResolvent (p+k) cut z hz) (fullResolvent p cut w hw)
    (reader (chargeReader a)) (inclusion (adjointShifted (p+k) cut z (coreEquiv f)))
    (inclusion (embed f)) (inclusion (shifted p cut w (coreEquiv g))) (inclusion (embed g))
    (whole_source_pair (p+k) cut z hz (coreEquiv f)) right
  apply first.trans (middle.trans ?_)
  rw [GaussUnitaryHistory.reader_inclusion, CanonicalGradedCharge.chargeReader_core, inclusion.inner_map_map]
  rfl

def sourceInsertion (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (g : QuantumTest) : H :=
  embed (physicalAction (p+k) (chargeAction a g)-chargeAction a (physicalAction p g))+
    cutoff cut (embed (chargeAction a g))-chargeReader a (cutoff cut (embed g))

theorem action_core (p : PhysicalMomentum) (f : QuantumTest) :
    physical p (coreEquiv f)=embed (physicalAction p f) := by
  change embed (physicalAction p (coreEquiv.symm (coreEquiv f)))=_
  rw [coreEquiv.symm_apply_apply]

theorem sourceInsertion_core (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (g : QuantumTest) :
    sourceInsertion p k a cut g=
      physical (p+k) (coreEquiv (chargeAction a g))+cutoff cut (chargeReader a (embed g))-
        chargeReader a (physical p (coreEquiv g)+cutoff cut (embed g)) := by
  simp only [sourceInsertion, map_sub, map_add, CanonicalGradedCharge.chargeReader_core, action_core]
  abel


private theorem response_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ro Ri Q W X : E →L[ℂ] E) (d : ℂ) (left f input g : E)
    (left_pair : ∀ y, inner ℂ left (Ro y)=inner ℂ f y) (right : Ri input=g)
    (hW : W=Q*Ri-Ro*Q+d • X) (hX : X=Ro*Q*Ri) :
    inner ℂ left (W input)=inner ℂ left (Q g)-inner ℂ f (Q input)+d*inner ℂ f (Q g) := by
  rw [hW, hX]
  simp only [add_apply, sub_apply, smul_apply, mul_apply_eq_comp, inner_add_right,
    inner_sub_right, inner_smul_right, right, left_pair]

private theorem endpoint_source_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (Q Y : E →L[ℂ] E) (cf cg incoming x y : E) (z w : ℂ)
    (paired : inner ℂ cf (Q y)=inner ℂ x cg) :
    inner ℂ (cf+Y.adjoint x-star z • x) (Q y)-
        inner ℂ x (Q (incoming+Y y-w • y))+(z-w)*inner ℂ x (Q y) =
      inner ℂ x (cg+Y (Q y)-Q (incoming+Y y)) := by
  rw [inner_sub_left, inner_add_left, inner_smul_left, starRingEnd_apply, star_star,
    paired, Y.adjoint_inner_left]
  simp only [map_sub, map_add, map_smul, inner_add_right, inner_sub_right, inner_smul_right]
  ring

private theorem reader_pair (a : NativeLie) (x y : H) :
    inner ℂ (inclusion x) (reader (chargeReader a) (inclusion y))=inner ℂ x (chargeReader a y) := by
  rw [GaussUnitaryHistory.reader_inclusion, inclusion.inner_map_map]

theorem response_endpoints (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (f g : QuantumTest) :
    inner ℂ (inclusion (adjointShifted (p+k) cut z (coreEquiv f)))
      (response p k a cut z w hz hw (inclusion (shifted p cut w (coreEquiv g)))) =
        inner ℂ (embed f) (sourceInsertion p k a cut g) := by
  have right : fullResolvent p cut w hw (inclusion (shifted p cut w (coreEquiv g)))=inclusion (embed g) :=
    CanonicalPhysicalYResolvent.full_shifted_core_return p cut w hw (coreEquiv g)
  have generated := response_pair (fullResolvent (p+k) cut z hz) (fullResolvent p cut w hw)
    (reader (chargeReader a)) (response p k a cut z w hz hw) (vertex p k a cut z w hz hw) (z-w)
    (inclusion (adjointShifted (p+k) cut z (coreEquiv f))) (inclusion (embed f))
    (inclusion (shifted p cut w (coreEquiv g))) (inclusion (embed g))
    (whole_source_pair (p+k) cut z hz (coreEquiv f)) right
    (response_return p k a cut z w hz hw) (vertex_return p k a cut z w hz hw)
  have scalar : inner ℂ (inclusion (adjointShifted (p+k) cut z (coreEquiv f)))
      (response p k a cut z w hz hw (inclusion (shifted p cut w (coreEquiv g)))) =
    inner ℂ (adjointShifted (p+k) cut z (coreEquiv f)) (chargeReader a (embed g))-
      inner ℂ (embed f) (chargeReader a (shifted p cut w (coreEquiv g)))+
        (z-w)*inner ℂ (embed f) (chargeReader a (embed g)) := by
    simpa only [reader_pair] using! generated
  have paired : inner ℂ (physical (p+k) (coreEquiv f)) (chargeReader a (embed g)) =
      inner ℂ (embed f) (physical (p+k) (coreEquiv (chargeAction a g))) := by
    rw [CanonicalGradedCharge.chargeReader_core]
    exact physical_pair (p+k) (coreEquiv f) (coreEquiv (chargeAction a g))
  have algebra := endpoint_source_pair (chargeReader a) (cutoff cut)
    (physical (p+k) (coreEquiv f)) (physical (p+k) (coreEquiv (chargeAction a g)))
    (physical p (coreEquiv g)) (embed f) (embed g) z w paired
  apply scalar.trans
  exact algebra.trans (congrArg (inner ℂ (embed f)) (sourceInsertion_core p k a cut g).symm)


private theorem projected_insertion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Y Q : E →L[ℂ] E) (b y : E) (kill : P*Y=0) (commutes : Commute P Q) :
    P (b+Y (Q y)-Q (Y y))=P b := by
  have zero (x : E) : P (Y x)=0 := congrArg (fun A : E →L[ℂ] E => A x) kill
  have commute (x : E) : P (Q x)=Q (P x) := congrArg (fun A : E →L[ℂ] E => A x) commutes.eq
  simp only [map_sub, map_add, zero, commute, map_zero, add_zero, sub_zero]

theorem projected_sourceInsertion (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (g : QuantumTest) :
    sourceProjection (sourceInsertion p k a cut (GaussCoreLabel.project sourceLabel g)) =
      sourceProjection (embed (CanonicalPhysicalWardCore.configurationTorque a (GaussCoreLabel.project sourceLabel g)+
        CanonicalPhysicalWardCore.currentAction k a (GaussCoreLabel.project sourceLabel g))) := by
  have base := congrArg embed (CanonicalPhysicalWardCore.physical_charge_ward p k a g)
  have generated := congrArg (fun b : H =>
    b+cutoff cut (embed (chargeAction a (GaussCoreLabel.project sourceLabel g)))-
      chargeReader a (cutoff cut (embed (GaussCoreLabel.project sourceLabel g)))) base
  have identity : sourceInsertion p k a cut (GaussCoreLabel.project sourceLabel g) =
      embed (CanonicalPhysicalWardCore.configurationTorque a (GaussCoreLabel.project sourceLabel g)+
        CanonicalPhysicalWardCore.currentAction k a (GaussCoreLabel.project sourceLabel g))+
      cutoff cut (chargeReader a (embed (GaussCoreLabel.project sourceLabel g)))-
        chargeReader a (cutoff cut (embed (GaussCoreLabel.project sourceLabel g))) := by
    simpa only [sourceInsertion, CanonicalGradedCharge.chargeReader_core] using generated
  exact (congrArg sourceProjection identity).trans
    (projected_insertion _ _ _ _ _ (CanonicalGradedGaugeReturn.cutoff_projection cut) (charge_blocks a))

theorem paired_current_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (f g : QuantumTest) :
    inner ℂ (embed (GaussCoreLabel.project sourceLabel f))
      (sourceInsertion p k a cut (GaussCoreLabel.project sourceLabel g)) =
    sourcePair (GaussCoreLabel.project sourceLabel f)
      (CanonicalPhysicalWardCore.configurationTorque a (GaussCoreLabel.project sourceLabel g)+
        CanonicalPhysicalWardCore.currentAction k a (GaussCoreLabel.project sourceLabel g)) := by
  have first := NativeHistoryGrade.projection_symmetric sourceLabel (embed f)
    (sourceInsertion p k a cut (GaussCoreLabel.project sourceLabel g))
  have last := NativeHistoryGrade.projection_symmetric sourceLabel (embed f)
    (embed (CanonicalPhysicalWardCore.configurationTorque a (GaussCoreLabel.project sourceLabel g)+
      CanonicalPhysicalWardCore.currentAction k a (GaussCoreLabel.project sourceLabel g)))
  have middle := congrArg (inner ℂ (embed f)) (projected_sourceInsertion p k a cut g)
  exact (congrArg (fun x : H => inner ℂ x (sourceInsertion p k a cut (GaussCoreLabel.project sourceLabel g)))
    (GaussCoreLabel.embed_project sourceLabel f)).trans
      (first.trans (middle.trans (last.symm.trans (congrArg (fun x : H =>
        inner ℂ x (embed (CanonicalPhysicalWardCore.configurationTorque a (GaussCoreLabel.project sourceLabel g)+
          CanonicalPhysicalWardCore.currentAction k a (GaussCoreLabel.project sourceLabel g))))
            (GaussCoreLabel.embed_project sourceLabel f).symm))))

theorem response_current_endpoints (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (f g : QuantumTest) :
    inner ℂ (inclusion (adjointShifted (p+k) cut z (coreEquiv (GaussCoreLabel.project sourceLabel f))))
      (response p k a cut z w hz hw
        (inclusion (shifted p cut w (coreEquiv (GaussCoreLabel.project sourceLabel g))))) =
    sourcePair (GaussCoreLabel.project sourceLabel f)
      (CanonicalPhysicalWardCore.configurationTorque a (GaussCoreLabel.project sourceLabel g)+
        CanonicalPhysicalWardCore.currentAction k a (GaussCoreLabel.project sourceLabel g)) :=
  (response_endpoints p k a cut z w hz hw (GaussCoreLabel.project sourceLabel f)
    (GaussCoreLabel.project sourceLabel g)).trans (paired_current_return p k a cut f g)

end LowEnergy.CanonicalPhysicalWardEndpoints
