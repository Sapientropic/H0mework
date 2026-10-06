import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScaleJetFactor
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCornerPartition

/-! Literal native and independent-adjoint cutoffs commute with the full source dilation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceCutoffDilationWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussCoframeForm GaussNativeForm
open GaussHistoryHilbert GaussYukawaCoefficient GaussRadialDomain GaussDiagonalHistory
open SourceCoframeVolumeCurrent SourceCoframeDilation SourceEulerCore SourceDilationAlgebra
open SourceEscapeCurrent SourceMinimalGraphParticular FullYSourceResolventGraphSplice
open FullYSourceCutoffVolterra FullYSourceCutoffSharp SourceScaleJetFactor SourceHamiltonianScaleJet
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussUnitaryHistory (Index)
open scoped ContDiff InnerProductSpace

private theorem pair_sub (f g h : QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul (c : ℂ) (f g : QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

theorem native_euler : Commute eulerAction GaussYukawaCoefficient.action :=
  euler_invariant_multiplier _ _ (fun _ _ => rfl)

theorem native_number : Commute number GaussYukawaCoefficient.action :=
  number_multiplier _ _ (fun z => by
    rw [normalized,source_map_return]
    exact GaussQuantumMultiplier.number_commute _)

private theorem affine_commute (A : CoreEnd) (hE : Commute eulerAction A)
    (hN : Commute number A) : Commute dilation A := by
  have he : eulerAction*A-A*eulerAction=(0 : ℂ) • A := by
    rw [hE.eq,sub_self,zero_smul]
  change dilation*A=A*dilation
  apply sub_eq_zero.mp
  rw [dilation_operator]
  simpa only [mul_zero,zero_smul,Module.End.one_eq_id] using!
    affine_dilation _ _ _ 0 he hN

theorem native_dilation : Commute dilation GaussYukawaCoefficient.action :=
  affine_commute _ native_euler native_number

theorem inverse_euler : Commute eulerAction inverseAction := by
  change Commute eulerAction (localMultiplier inverseFiber (fun _ => inverse_smooth.contDiffAt))
  exact euler_invariant_multiplier _ _ (fun _ _ => rfl)

theorem inverse_number : Commute number inverseAction := by
  change Commute number (localMultiplier inverseFiber (fun _ => inverse_smooth.contDiffAt))
  exact number_multiplier _ _ (fun z => (Commute.one_right _).smul_right _)

theorem inverse_dilation : Commute dilation inverseAction :=
  affine_commute _ inverse_euler inverse_number

/-- This is the actual core law of bounded.adjoint, in its original order. -/
def sharpVertexAction : CoreEnd := GaussFullHamiltonian.adjointAction*inverseAction

theorem sharp_vertex_core (f : QuantumTest) :
    GaussYukawaOperator.bounded.adjoint (embed f)=embed (sharpVertexAction f) :=
  bounded_sharp_core f

theorem vertex_pair (f g : QuantumTest) :
    sourcePair f (sharpVertexAction g)=sourcePair (GaussYukawaCoefficient.action f) g := by
  change inner ℂ (embed f) (embed (sharpVertexAction g))=
    inner ℂ (embed (GaussYukawaCoefficient.action f)) (embed g)
  rw [←sharp_vertex_core,←GaussYukawaOperator.bounded_core,
    ContinuousLinearMap.adjoint_inner_right]

private theorem adjoint_commute (A : CoreEnd)
    (hPair : ∀ f g, sourcePair f (A g)=sourcePair (A f) g)
    (hNative : Commute A GaussYukawaCoefficient.action) : Commute A sharpVertexAction := by
  apply LinearMap.ext
  intro f
  apply embed_injective
  apply ext_inner_left ℂ
  intro y
  refine GaussBoundedMultiplier.core_dense.induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  obtain ⟨g,rfl⟩ := coreEquiv.surjective a
  change sourcePair g (A (sharpVertexAction f))=sourcePair g (sharpVertexAction (A f))
  rw [hPair,vertex_pair,vertex_pair]
  have hc := LinearMap.congr_fun hNative.eq g
  change A (GaussYukawaCoefficient.action g)=GaussYukawaCoefficient.action (A g) at hc
  rw [←hc,←hPair]

theorem sharp_number : Commute number sharpVertexAction :=
  adjoint_commute _ number_pair native_number

private theorem core_commute_product (D A B : CoreEnd) (hA : Commute D A)
    (hB : Commute D B) : Commute D (A*B) := by
  change D*(A*B)=(A*B)*D
  calc
    _ = (D*A)*B := by noncomm_ring
    _ = (A*D)*B := by rw [hA.eq]
    _ = A*(D*B) := by noncomm_ring
    _ = A*(B*D) := by rw [hB.eq]
    _ = _ := by noncomm_ring

private theorem core_commute_add (D A B : CoreEnd) (hA : Commute D A)
    (hB : Commute D B) : Commute D (A+B) := by
  change D*(A+B)=(A+B)*D
  simp only [mul_add,add_mul,hA.eq,hB.eq]

private theorem core_commute_sub (D A B : CoreEnd) (hA : Commute D A)
    (hB : Commute D B) : Commute D (A-B) := by
  change D*(A-B)=(A-B)*D
  simp only [mul_sub,sub_mul,hA.eq,hB.eq]

private theorem one_inverse_dilation : Commute dilation (1-inverseAction) := by
  change dilation*(1-inverseAction)=(1-inverseAction)*dilation
  simp only [mul_sub,sub_mul,mul_one,one_mul,inverse_dilation.eq]

theorem sharp_euler : Commute eulerAction sharpVertexAction := by
  have he : Commute eulerAction GaussFullHamiltonian.adjointAction :=
    euler_invariant_multiplier _ _ (fun _ _ => rfl)
  exact core_commute_product _ _ _ he inverse_euler

theorem sharp_dilation : Commute dilation sharpVertexAction :=
  affine_commute _ sharp_euler sharp_number

def nativeCutoffAction : ℕ → CoreEnd
  | 0 => GaussYukawaCoefficient.action
  | n+1 => GaussYukawaCoefficient.action+(1-inverseAction)*nativeCutoffAction n

def sharpCutoffAction : ℕ → CoreEnd
  | 0 => sharpVertexAction
  | n+1 => sharpVertexAction+sharpCutoffAction n*(1-inverseAction)

theorem native_cutoff_core (n : ℕ) (f : QuantumTest) :
    cutoff n (embed f)=embed (nativeCutoffAction n f) := by
  induction n generalizing f with
  | zero => exact GaussYukawaOperator.bounded_core f
  | succ n ih =>
    change GaussYukawaOperator.bounded (embed f)+
      (cutoff n (embed f)-inverseRadius (cutoff n (embed f)))=_
    rw [GaussYukawaOperator.bounded_core,ih,inverse_core,←map_sub,←map_add]
    rfl

theorem sharp_cutoff_core (n : ℕ) (f : QuantumTest) :
    (cutoff n).adjoint (embed f)=embed (sharpCutoffAction n f) := by
  induction n generalizing f with
  | zero => exact sharp_vertex_core f
  | succ n ih =>
    rw [cutoff_sharp_recursion]
    change GaussYukawaOperator.bounded.adjoint (embed f)+
      (cutoff n).adjoint (embed f-inverseRadius (embed f))=_
    rw [sharp_vertex_core,inverse_core,←map_sub,ih,←map_add]
    rfl

theorem native_cutoff_dilation (n : ℕ) : Commute dilation (nativeCutoffAction n) := by
  induction n with
  | zero => exact native_dilation
  | succ n ih =>
    change Commute dilation (GaussYukawaCoefficient.action+(1-inverseAction)*nativeCutoffAction n)
    exact core_commute_add _ _ _ native_dilation
      (core_commute_product _ _ _ one_inverse_dilation ih)

theorem sharp_cutoff_dilation (n : ℕ) : Commute dilation (sharpCutoffAction n) := by
  induction n with
  | zero => exact sharp_dilation
  | succ n ih =>
    change Commute dilation (sharpVertexAction+sharpCutoffAction n*(1-inverseAction))
    exact core_commute_add _ _ _ sharp_dilation
      (core_commute_product _ _ _ ih one_inverse_dilation)

def literalIncrementAction (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  if sharp then sharpCutoffAction ell-sharpCutoffAction m
  else nativeCutoffAction ell-nativeCutoffAction m

theorem literal_increment_core (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    SourceEscapeSeedTail.actualIncrement sharp m ell (embed f)=
      embed (literalIncrementAction sharp m ell f) := by
  cases sharp
  · change cutoff ell (embed f)-cutoff m (embed f)=_
    rw [native_cutoff_core,native_cutoff_core,←map_sub]
    rfl
  · change (cutoff ell).adjoint (embed f)-(cutoff m).adjoint (embed f)=_
    rw [sharp_cutoff_core,sharp_cutoff_core,←map_sub]
    rfl

theorem literal_increment_dilation (sharp : Bool) (m ell : ℕ) :
    Commute dilation (literalIncrementAction sharp m ell) := by
  cases sharp
  · change Commute dilation (nativeCutoffAction ell-nativeCutoffAction m)
    exact core_commute_sub _ _ _ (native_cutoff_dilation ell) (native_cutoff_dilation m)
  · change Commute dilation (sharpCutoffAction ell-sharpCutoffAction m)
    exact core_commute_sub _ _ _ (sharp_cutoff_dilation ell) (sharp_cutoff_dilation m)

theorem same_increment_action (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    incrementAction sharp m ell f=literalIncrementAction sharp m ell f := by
  apply embed_injective
  rw [increment_action_embed,literal_increment_core]

theorem actual_increment_dilation (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    dilation (incrementAction sharp m ell f)=incrementAction sharp m ell (dilation f) := by
  simp only [same_increment_action]
  exact LinearMap.congr_fun (literal_increment_dilation sharp m ell).eq f

/-- All three scale derivatives can reuse the same literal insertion. -/
theorem inserted_scale_derivative (B A : CoreEnd) (hB : Commute dilation B) :
    scaleDerivative (B*A)=B*scaleDerivative A := by
  change (3*Complex.I/2) • (dilation*(B*A)-(B*A)*dilation)=
    B*((3*Complex.I/2) • (dilation*A-A*dilation))
  have hr : dilation*(B*A)-(B*A)*dilation=B*(dilation*A-A*dilation) := by
    calc
      _ = (dilation*B)*A-B*A*dilation := by noncomm_ring
      _ = _ := by rw [hB.eq]; noncomm_ring
  rw [hr,mul_smul_comm]

def insertedDefect (B : CoreEnd) : CoreEnd := diagonalAction*B-B*diagonalAction

theorem inserted_scale_pair (B : CoreEnd) (hB : Commute dilation B) (p q : QuantumTest) :
    sourcePair p (B (scaleDerivative diagonalAction q))=
      (3*Complex.I/2)*(sourcePair (dilation p) (B (diagonalAction q))-
        sourcePair (diagonalAction p) (B (dilation q))+
        sourcePair p (insertedDefect B (dilation q))) := by
  change sourcePair p (B ((3*Complex.I/2) •
    (dilation (diagonalAction q)-diagonalAction (dilation q))))=_
  rw [map_smul,map_sub,pair_smul,pair_sub]
  have hd := LinearMap.congr_fun hB.eq (diagonalAction q)
  change dilation (B (diagonalAction q))=B (dilation (diagonalAction q)) at hd
  rw [←hd,dilation_pair]
  have hh : B (diagonalAction (dilation q))=
      diagonalAction (B (dilation q))-insertedDefect B (dilation q) := by
    change _=diagonalAction (B (dilation q))-
      (diagonalAction (B (dilation q))-B (diagonalAction (dilation q)))
    abel
  rw [hh,pair_sub,diagonalAction_pair]
  ring

private theorem core_embed (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply x)

def actualDefectTest (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  diagonalAction (coreEquiv.symm (sourceCore F z hz g))-
    z • coreEquiv.symm (sourceCore F z hz g)-coreEquiv.symm g

theorem actual_defect_test (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (actualDefectTest F z hz g)=finiteProjectionDefect F z hz g := by
  simp only [actualDefectTest,map_sub,map_smul,core_embed]
  change diagonal (sourceCore F z hz g)-z • (sourceCore F z hz g : H)-(g : H)=_
  rw [SourcePhysicalHamiltonianSquare.source_core_action]
  change ((g : H)+z • finiteResolvent F z (g : H)+finiteProjectionDefect F z hz g)-
    z • finiteResolvent F z (g : H)-(g : H)=_
  abel

theorem inserted_source_ward (B : CoreEnd) (hB : Commute dilation B)
    (z : ℂ) (k g p q : QuantumTest) :
    sourcePair p (B (scaleDerivative diagonalAction q))=
      (3*Complex.I/2)*(sourcePair (dilation p) (B g)-sourcePair k (B (dilation q))+
        sourcePair (dilation p) (B (diagonalAction q-z • q-g))-
        sourcePair (diagonalAction p-star z • p-k) (B (dilation q))+
        sourcePair p (insertedDefect B (dilation q))) := by
  rw [inserted_scale_pair B hB]
  simp only [map_sub,map_smul,sourcePair,inner_sub_right,inner_sub_left,
    inner_smul_right,inner_smul_left,starRingEnd_apply,star_star]
  have hd := dilation_pair p (B q)
  have hc := LinearMap.congr_fun hB.eq q
  change dilation (B q)=B (dilation q) at hc
  rw [hc] at hd
  simp only [sourcePair] at hd
  rw [hd]
  ring

/-- The inserted current keeps [H₀,B] and both actual varying-F projection defects. -/
theorem actual_inserted_scale_ward (sharp : Bool) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (k g : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    let p := coreEquiv.symm (sourceCore F (star z) hs k)
    let q := coreEquiv.symm (sourceCore F z hz g)
    let B := literalIncrementAction sharp m ell
    sourcePair p (B (scaleDerivative diagonalAction q))=
      (3*Complex.I/2)*(sourcePair (dilation p) (B (coreEquiv.symm g))-
        sourcePair (coreEquiv.symm k) (B (dilation q))+
        sourcePair (dilation p) (B (actualDefectTest F z hz g))-
        sourcePair (actualDefectTest F (star z) hs k) (B (dilation q))+
        sourcePair p (insertedDefect B (dilation q))) := by
  exact inserted_source_ward _ (literal_increment_dilation sharp m ell) z _ _ _ _

end LowEnergy.SourceCutoffDilationWard
