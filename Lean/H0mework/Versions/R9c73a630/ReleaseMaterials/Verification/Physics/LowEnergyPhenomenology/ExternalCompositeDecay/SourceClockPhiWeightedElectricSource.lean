import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeLieWedgeSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentGeometricPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare SourceCoframeVolume
open SourceScalarDoubleCurrent SourceClockPhiMatchedElectricSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusAcceleration SourceClockPhiRadiusSourceCurrent SourceClockAcceleration
open FirstCurrentPayerNext ClockPhiHeatCorrectedCovarianceSource JointElectricSource
open scoped InnerProductSpace ContDiff
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev CE : End := fullElectricCurrent
private abbrev E : End := electricAction
private abbrev P : End := electricPrimitive
private abbrev L : End := electricLyapunov
private abbrev H0 : End := diagonalAction
attribute [local irreducible] sourcePair embed diagonalAction correctedCompleteCore normalizedState normalizedForcing updatedForcing
private theorem weight_smooth(z:physicalChart):ContDiffAt ℝ ∞ (fun x=>volume x^3) z.val:=volume_smooth.contDiffAt.pow 3
/-- The required physical contact weight is V cubed, not a caller's volume cap. -/
def magneticVolumeWeight : End := multiply (fun z=>volume z^3) weight_smooth
private abbrev W := magneticVolumeWeight
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(a:ℂ)(f g:QuantumTest):sourcePair (a • f) g=star a*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(a:ℂ)(f g:QuantumTest):sourcePair f (a • g)=a*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem W_pair(f g:QuantumTest):sourcePair f (W g)=sourcePair (W f) g:=multiply_pair _ _ _ _
private theorem E_pair(f g:QuantumTest):sourcePair f (E g)=sourcePair (E f) g:=multiply_pair _ _ _ _
private theorem CE_pair(f g:QuantumTest):sourcePair f (CE g)= -sourcePair (CE f) g:=by
  have h1:sourcePair f (H0 (E g))=sourcePair (E (H0 f)) g:=by rw [diagonalAction_pair,E_pair]
  have h2:sourcePair f (E (H0 g))=sourcePair (H0 (E f)) g:=by rw [E_pair,diagonalAction_pair]
  change sourcePair f ((1/2:ℂ) • (H0 (E g)-E (H0 g)))=
    -sourcePair ((1/2:ℂ) • (H0 (E f)-E (H0 f))) g
  simp only[pair_smul_r,pair_smul_l,sourcePair,map_sub,inner_sub_left,inner_sub_right] at h1 h2 ⊢
  norm_num
  rw [h1,h2]
  ring
private theorem real_weight(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute W (multiply b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm ((volume z^3:ℝ):ℂ) (b z:ℂ) (f z)
private theorem comm_add(A B:End)(hA:Commute W A)(hB:Commute W B):Commute W (A+B):=by
  change W*(A+B)=(A+B)*W
  rw [mul_add,add_mul,hA.eq,hB.eq]
private theorem comm_smul(A:End)(c:ℂ)(hA:Commute W A):Commute W (c • A):=by
  change W*(c • A)=(c • A)*W
  rw [mul_smul_comm,smul_mul_assoc,hA.eq]
private theorem E_weight:Commute W E:=real_weight _ _
private theorem L_weight:Commute W L:=by
  unfold L electricLyapunov
  rw [original_clock]
  exact comm_add _ _ E_weight (comm_smul _ _ (real_weight _ _))
private theorem P_weight:Commute W P:=by
  have hphi:Commute W phiSquare:=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change ((volume z^3:ℝ):ℂ) • ((phiRadius z:ℂ) • ((phiRadius z:ℂ) • f z))=
      (phiRadius z:ℂ) • ((phiRadius z:ℂ) • (((volume z^3:ℝ):ℂ) • f z))
    simp only[smul_smul]
    congr 1
    ring
  have hp:P=(2/(n:ℂ)) • phiSquare+(5/2:ℂ) • E-(2:ℂ) • L:=actual_electric_primitive_normal_form
  rw [hp]
  have hL:=comm_smul L (-2:ℂ) L_weight
  have hA:=comm_add _ _ (comm_smul phiSquare (2/(n:ℂ)) hphi) (comm_smul E (5/2:ℂ) E_weight)
  change Commute W ((2/(n:ℂ)) • phiSquare+(5/2:ℂ) • E-(2:ℂ) • L)
  simpa only[sub_eq_add_neg,neg_smul] using comm_add _ _ hA hL

/-- Original electric current symmetrized with its actual magnetic volume weight. -/
def weightedElectricCurrent : End := (1/2:ℂ) • (W*CE+CE*W)
private abbrev X := weightedElectricCurrent
private theorem X_pair(f g:QuantumTest):sourcePair f (X g)= -sourcePair (X f) g:=by
  have h1:sourcePair f (W (CE g))= -sourcePair (CE (W f)) g:=(W_pair _ _).trans (CE_pair _ _)
  have h2:sourcePair f (CE (W g))= -sourcePair (W (CE f)) g:=by rw [CE_pair,←W_pair]
  change sourcePair f ((1/2:ℂ) • (W (CE g)+CE (W g)))=
    -sourcePair ((1/2:ℂ) • (W (CE f)+CE (W f))) g
  simp only[pair_smul_r,pair_smul_l,pair_add_r,pair_add_l]
  rw [h1,h2]
  norm_num
  ring
private theorem weighted_current(T:End)(hT:Commute W T)(hC:Commute W (bracket CE T)):
    bracket X T=W*bracket CE T:=by
  have h:bracket X T=(1/2:ℂ) • (W*bracket CE T+bracket CE T*W):=by
    unfold X weightedElectricCurrent bracket
    linear_combination (norm:=(noncomm_ring;module)) (1/2:ℂ) • (CE*hT.eq+hT.eq*CE)
  rw [h,←hC.eq]
  module
private theorem bracket_weight_commute(F:Index)(g:diagonal.domain):Commute W (bracket CE P):=by
  rw [actual_matched_primitive_electric_current F g]
  have hUE:Commute W (U*E):=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change ((volume z^3:ℝ):ℂ) • ((reciprocalVolume z:ℂ) • ((electricWeight z:ℂ) • f z))=
      (reciprocalVolume z:ℂ) • ((electricWeight z:ℂ) • (((volume z^3:ℝ):ℂ) • f z))
    simp only[smul_smul]
    congr 1
    ring
  have hWedge:Commute W wedgeAction:=real_weight _ _
  have h1:=comm_smul (U*E) (-5:ℂ) hUE
  have h2:=comm_smul wedgeAction (-1/4:ℂ) hWedge
  simpa only[sub_eq_add_neg,neg_smul,neg_div] using comm_add _ _ h1 h2

/-- The weighted source spends its full P primitive in the exact metric needed by the magnetic contact. -/
theorem actual_weighted_primitive_current(F:Index)(g:diagonal.domain):
    bracket X P=(-5:ℂ) • (W*U*E)-(1/4:ℂ) • (W*wedgeAction):=by
  rw [weighted_current P P_weight (bracket_weight_commute F g),actual_matched_primitive_electric_current F g]
  simp only[mul_sub,mul_smul_comm,mul_assoc]

def weightedElectricEndpoint(h:ℝ)(forward:Bool):End:=
  (1:End)+(if forward then -(h:ℂ) else (h:ℂ)) • X
private theorem midpoint_word(h:ℝ)(T:End)(w:QuantumTest):
    sourcePair (weightedElectricEndpoint h true w) (T (weightedElectricEndpoint h true w))-
      sourcePair (weightedElectricEndpoint h false w) (T (weightedElectricEndpoint h false w))=
      (2*(h:ℂ))*sourcePair w (bracket X T w):=by
  change sourcePair (w+(-(h:ℂ)) • X w) (T (w+(-(h:ℂ)) • X w))-
    sourcePair (w+(h:ℂ) • X w) (T (w+(h:ℂ) • X w))=_
  have hX:sourcePair w (X (T w))= -sourcePair (X w) (T w):=X_pair _ _
  change _=(2*(h:ℂ))*sourcePair w (X (T w)-T (X w))
  simp only[sourcePair,map_sub,map_add,map_smul,inner_sub_right,inner_add_left,
    inner_add_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal,map_neg] at hX ⊢
  rw [hX]
  ring

/-- Exact finite endpoints of the same source pay the weighted primitive, with no endpoint budget premise. -/
theorem actual_weighted_electric_midpoint(F:Index)(g:diagonal.domain)(h:ℝ)(w:QuantumTest):
    ‖embed (weightedElectricEndpoint h true w)‖^2=‖embed (weightedElectricEndpoint h false w)‖^2 ∧
    (sourcePair (weightedElectricEndpoint h true w) (P (weightedElectricEndpoint h true w))).re-
      (sourcePair (weightedElectricEndpoint h false w) (P (weightedElectricEndpoint h false w))).re=
      -10*h*(sourcePair w ((W*U*E) w)).re-(h/2)*(sourcePair w ((W*wedgeAction) w)).re:=by
  have h0:=congrArg Complex.re (midpoint_word h 1 w)
  have hp:=congrArg Complex.re (midpoint_word h P w)
  rw [show bracket X (1:End)=0 by unfold bracket;simp] at h0
  simp only[Module.End.one_apply,LinearMap.zero_apply,sourcePair,map_zero,inner_zero_right,
    mul_zero,Complex.zero_re,Complex.sub_re] at h0
  have hself(q:QuantumTest):(inner ℂ (embed q) (embed q)).re=‖embed q‖^2:=by
    simpa only using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed q)
  simp only[hself] at h0
  rw [actual_weighted_primitive_current F g] at hp
  simp only[LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_r,pair_smul_r,
    Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im] at hp
  norm_num at hp
  refine ⟨by linarith only[h0],?_⟩
  simp only[Module.End.mul_apply]
  nlinarith only[hp]
end LowEnergy.FirstCurrentGeometricPayer
