import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScaleJetFactor
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCornerPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceScaleJetWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory
open SourceCoframeVolumeCurrent SourceCoframeDilation SourceScaleJetFactor SourceHamiltonianScaleJet
open SourceEscapeCurrent SourceMinimalGraphParticular FullYSourceResolventGraphSplice
open GaussUnitaryHistory (Index)
open scoped InnerProductSpace

private theorem pair_add (f g h : QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub (f g h : QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul (c : ℂ) (f g : QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_add_left (f g h : QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_left (f g h : QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_smul_left (c : ℂ) (f g : QuantumTest) : sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]

def scaleConstant : ℂ := 3*Complex.I/2

private theorem scale_pair (A : CoreEnd) (p q : QuantumTest) :
    sourcePair p (scaleDerivative A q)=scaleConstant*
      (sourcePair (dilation p) (A q)-sourcePair p (A (dilation q))) := by
  change sourcePair p ((3*Complex.I/2) • (dilation (A q)-A (dilation q)))=_
  rw [pair_smul,pair_sub,dilation_pair p (A q)]
  rfl

private theorem scale_pair_two (A : CoreEnd) (p q : QuantumTest) :
    sourcePair p (scaleDerivative (scaleDerivative A) q)=scaleConstant^2*
      (sourcePair (dilation (dilation p)) (A q)-
        2*sourcePair (dilation p) (A (dilation q))+sourcePair p (A (dilation (dilation q)))) := by
  rw [scale_pair,scale_pair,scale_pair]
  ring

private theorem scale_pair_three (A : CoreEnd) (p q : QuantumTest) :
    sourcePair p (scaleDerivative (scaleDerivative (scaleDerivative A)) q)=scaleConstant^3*
      (sourcePair (dilation (dilation (dilation p))) (A q)-
        3*sourcePair (dilation (dilation p)) (A (dilation q))+
        3*sourcePair (dilation p) (A (dilation (dilation q)))-
        sourcePair p (A (dilation (dilation (dilation q))))) := by
  rw [scale_pair,scale_pair_two,scale_pair_two]
  ring

def defectZero (z : ℂ) (g q : QuantumTest) : QuantumTest :=
  diagonalAction q-z • q-g
def defectOne (z : ℂ) (g q : QuantumTest) : QuantumTest :=
  diagonalAction (dilation q)-z • dilation q-dilation g

def fluxOne (z : ℂ) (k g p q : QuantumTest) : ℂ :=
  sourcePair (dilation p) (defectZero z g q)-
    sourcePair (defectZero (star z) k p) (dilation q)

def fluxTwo (z : ℂ) (k g p q : QuantumTest) : ℂ :=
  sourcePair (dilation (dilation p)) (defectZero z g q)-
    sourcePair (dilation p) (defectOne z g q)-
    sourcePair (defectOne (star z) k p) (dilation q)+
    sourcePair (defectZero (star z) k p) (dilation (dilation q))

def fluxThree (z : ℂ) (k g p q : QuantumTest) : ℂ :=
  sourcePair (dilation (dilation (dilation p))) (defectZero z g q)-
    3*sourcePair (dilation (dilation p)) (defectOne z g q)+
    3*sourcePair (defectOne (star z) k p) (dilation (dilation q))-
    sourcePair (defectZero (star z) k p) (dilation (dilation (dilation q)))

theorem third_scale_ward (z : ℂ) (k g p q : QuantumTest) :
    sourcePair p (scaleDerivative (scaleDerivative (scaleDerivative diagonalAction)) q)=
      scaleConstant^3*(2*(sourcePair (dilation (dilation (dilation k))) q-
        sourcePair p (dilation (dilation (dilation g))))+fluxThree z k g p q) := by
  rw [scale_pair_three]
  simp only [fluxThree,defectZero,defectOne,pair_sub,pair_smul,pair_sub_left,pair_smul_left,star_star]
  simp_rw [←dilation_pair,←diagonalAction_pair]
  simp_rw [←dilation_pair]
  ring

theorem second_scale_ward (z : ℂ) (k g p q : QuantumTest) :
    sourcePair p (scaleDerivative (scaleDerivative diagonalAction) q)=
      scaleConstant^2*fluxTwo z k g p q := by
  rw [scale_pair_two]
  simp only [fluxTwo,defectZero,defectOne,pair_sub,pair_smul,pair_sub_left,pair_smul_left,star_star]
  simp_rw [←dilation_pair,←diagonalAction_pair]
  simp_rw [←dilation_pair]
  ring

theorem first_scale_ward (z : ℂ) (k g p q : QuantumTest) :
    sourcePair p (scaleDerivative diagonalAction q)=scaleConstant*
      (sourcePair p (dilation g)-sourcePair (dilation k) q+fluxOne z k g p q) := by
  rw [scale_pair]
  simp only [fluxOne,defectZero,pair_sub,pair_smul,pair_sub_left,pair_smul_left,star_star]
  simp_rw [←dilation_pair,←diagonalAction_pair]
  ring

def sourceBody (z : ℂ) (k g p q : QuantumTest) : ℂ :=
  2*scaleConstant^3*(sourcePair (dilation (dilation (dilation k))) q-
    sourcePair p (dilation (dilation (dilation g))))-
  scaleConstant*(sourcePair p (dilation g)-sourcePair (dilation k) q)-
  3*(sourcePair p g+z*sourcePair p q)

def doubleFlux (z : ℂ) (k g p q : QuantumTest) : ℂ :=
  scaleConstant^3*fluxThree z k g p q+3*scaleConstant^2*fluxTwo z k g p q-
    scaleConstant*fluxOne z k g p q-3*sourcePair p (defectZero z g q)

set_option maxRecDepth 2048 in
theorem full_scale_ward (z : ℂ) (k g p q : QuantumTest) :
    sourcePair p (scaleJet q)=sourceBody z k g p q+doubleFlux z k g p q := by
  change sourcePair p ((scaleDerivative (scaleDerivative (scaleDerivative diagonalAction))) q+
    (3 : ℂ) • (scaleDerivative (scaleDerivative diagonalAction) q)-
    scaleDerivative diagonalAction q-(3 : ℂ) • diagonalAction q)=_
  rw [pair_sub,pair_sub,pair_add,pair_smul,pair_smul,
    third_scale_ward z k g p q,second_scale_ward z k g p q,first_scale_ward z k g p q]
  simp only [sourceBody,doubleFlux,defectZero,pair_sub,pair_smul]
  ring

private theorem core_embed (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply x)

theorem actual_defect_zero (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (defectZero z (coreEquiv.symm g) (coreEquiv.symm (sourceCore F z hz g)))=
      finiteProjectionDefect F z hz g := by
  simp only [defectZero,map_sub,map_smul,core_embed]
  change diagonal (sourceCore F z hz g)-z • (sourceCore F z hz g : H)-(g : H)=_
  rw [SourcePhysicalHamiltonianSquare.source_core_action]
  change ((g : H)+z • finiteResolvent F z (g : H)+finiteProjectionDefect F z hz g)-
    z • finiteResolvent F z (g : H)-(g : H)=_
  abel

theorem defect_one_source (z : ℂ) (g q : QuantumTest) :
    defectOne z g q=dilation (defectZero z g q)+
      (diagonalAction*dilation-dilation*diagonalAction) q := by
  simp only [defectOne,defectZero,map_sub,map_smul,LinearMap.sub_apply,Module.End.mul_apply]
  abel

theorem actual_full_scale_ward (F : Index) (z : ℂ) (hz : z.im≠0) (k g : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    let p := coreEquiv.symm (sourceCore F (star z) hs k)
    let q := coreEquiv.symm (sourceCore F z hz g)
    sourcePair p (scaleJet q)=sourceBody z (coreEquiv.symm k) (coreEquiv.symm g) p q+
      doubleFlux z (coreEquiv.symm k) (coreEquiv.symm g) p q := by
  exact full_scale_ward _ _ _ _ _

private theorem adjoint_action_sub (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    adjointFactorAction sharp m ell (f-g)=
      adjointFactorAction sharp m ell f-adjointFactorAction sharp m ell g := by
  apply embed_injective
  rw [map_sub,←adjoint_factor_core,←adjoint_factor_core,←adjoint_factor_core,map_sub,map_sub]

private theorem adjoint_action_smul (sharp : Bool) (m ell : ℕ) (c : ℂ) (f : QuantumTest) :
    adjointFactorAction sharp m ell (c • f)=c • adjointFactorAction sharp m ell f := by
  apply embed_injective
  rw [map_smul,←adjoint_factor_core,←adjoint_factor_core,map_smul,map_smul]

private theorem left_sub (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    leftTest sharp m ell (f-g)=leftTest sharp m ell f-leftTest sharp m ell g := by
  simp only [leftTest,adjoint_action_sub,map_sub]

private theorem left_smul (sharp : Bool) (m ell : ℕ) (c : ℂ) (f : QuantumTest) :
    leftTest sharp m ell (c • f)=c • leftTest sharp m ell f := by
  simp only [leftTest,adjoint_action_smul,map_smul]

/-- The transformed defect includes the literal source commutator, not a chosen boundary condition. -/
theorem transformed_defect_zero (sharp : Bool) (m ell : ℕ) (z : ℂ) (k p : QuantumTest) :
    defectZero z (leftTest sharp m ell k) (leftTest sharp m ell p)=
      leftTest sharp m ell (defectZero z k p)+
        (diagonalAction (leftTest sharp m ell p)-leftTest sharp m ell (diagonalAction p)) := by
  simp only [defectZero,left_sub,left_smul]
  abel

private theorem resolvent_pair (F : Index) (z : ℂ) (hz : z.im≠0) (k y : H) :
    inner ℂ k (finiteResolvent F z y)=inner ℂ (finiteResolvent F (star z) k) y := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hk := congrArg (fun A : H →L[ℂ] H => A k)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) (star z) hs)
  have hy := congrArg (fun A : H →L[ℂ] H => A y)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F (star z) k)-
    star z • finiteResolvent F (star z) k=k at hk
  change GaussGradedCompression.compression F (finiteResolvent F z y)-
    z • finiteResolvent F z y=y at hy
  have hpair : inner ℂ (GaussGradedCompression.compression F (finiteResolvent F (star z) k))
      (finiteResolvent F z y)=inner ℂ (finiteResolvent F (star z) k)
        (GaussGradedCompression.compression F (finiteResolvent F z y)) := by
    simpa only using! GaussGradedCompression.compression_pair F (finiteResolvent F (star z) k)
      (finiteResolvent F z y)
  calc
    _ = inner ℂ (GaussGradedCompression.compression F (finiteResolvent F (star z) k)-
        star z • finiteResolvent F (star z) k) (finiteResolvent F z y) :=
      congrArg (fun v => inner ℂ v _) hk.symm
    _ = inner ℂ (finiteResolvent F (star z) k)
        (GaussGradedCompression.compression F (finiteResolvent F z y)-z • finiteResolvent F z y) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,
        hpair,starRingEnd_apply,star_star]
    _ = _ := congrArg (fun v => inner ℂ _ v) hy

def factoredBody (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (k g : diagonal.domain) : ℂ :=
  let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  sourceBody z (leftTest sharp m ell (coreEquiv.symm k)) (coreEquiv.symm g)
    (leftTest sharp m ell (coreEquiv.symm (sourceCore F (star z) hs k)))
    (coreEquiv.symm (sourceCore F z hz g))

def factoredFlux (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (k g : diagonal.domain) : ℂ :=
  let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  doubleFlux z (leftTest sharp m ell (coreEquiv.symm k)) (coreEquiv.symm g)
    (leftTest sharp m ell (coreEquiv.symm (sourceCore F (star z) hs k)))
    (coreEquiv.symm (sourceCore F z hz g))

theorem actual_response_scale_ward (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (k g : diagonal.domain) :
    inner ℂ (k : H) (finiteResolvent F z (SourceEscapeSeedTail.actualIncrement sharp m ell
      (finiteResolvent F z (g : H))))=
      (1/48 : ℂ)*(factoredBody sharp m ell F z hz k g+factoredFlux sharp m ell F z hz k g) := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  rw [resolvent_pair F z hz]
  have hp := core_embed (sourceCore F (star z) hs k)
  have hq := core_embed (sourceCore F z hz g)
  change embed (coreEquiv.symm (sourceCore F (star z) hs k))=finiteResolvent F (star z) (k : H) at hp
  change embed (coreEquiv.symm (sourceCore F z hz g))=finiteResolvent F z (g : H) at hq
  rw [←hp,←hq,full_pair_factor,full_scale_ward z
    (leftTest sharp m ell (coreEquiv.symm k)) (coreEquiv.symm g)]
  rfl

/-- The original two summands of J return together; both source and transformed projection flux remain. -/
theorem actual_joint_scale_ward (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (k g : diagonal.domain) :
    inner ℂ (SourceKineticTranspose.outerResidual F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (SourceHardyRetardedTail.particular sharp m ell F z (g : H))+
    inner ℂ (k : H) (finiteResolvent F z (SourceCornerPartition.complement
      (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H)))))=
    (1/48 : ℂ)*(factoredBody sharp m ell F z hz k g+factoredFlux sharp m ell F z hz k g)-
      inner ℂ (k : H) (SourceHardyRetardedTail.particular sharp m ell F z (g : H)+
        z • finiteResolvent F z (SourceHardyRetardedTail.particular sharp m ell F z (g : H))) := by
  have h := SourceCornerPartition.actual_full_increment_splice sharp m ell F z hz g k
  rw [actual_response_scale_ward sharp m ell F z hz k g] at h
  linear_combination -h

end LowEnergy.SourceScaleJetWard
