import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralSpinCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaHamiltonianCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarGaugeForce
open SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent SourceScalarPairedTransport
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction matterAction
  defectAction compressionCore

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceMixedNativeReturn.fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  cases sharp <;> rfl


private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 0) (hz : γ 0=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 0 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem coframe_derivative_full (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let e := GaussCoframeCore.coframeDirection i
  let A := (branchMap sharp (scalarField z)).restrictScalars ℝ
  have hg : HasDerivAt (fun r : ℝ => z+r • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have he := invariant_derivative A f (SourceMixedNativeReturn.fullAction sharp f) (fun r : ℝ => z+r • e) z e hg
    (by simp) ((f.contDiff.differentiable (by simp)) z)
    (((SourceMixedNativeReturn.fullAction sharp f).contDiff.differentiable (by simp)) z) (fun r => by
      rw [full_at]
      simp only [A,e,GaussCoframeCore.coframeDirection,scalarField,Prod.smul_mk,Prod.snd_add,
        smul_zero,add_zero,ContinuousLinearMap.coe_restrictScalars'])
  change GaussCoframeCore.derivative e (SourceMixedNativeReturn.fullAction sharp f) z=
    SourceMixedNativeReturn.fullAction sharp (GaussCoframeCore.derivative e f) z
  rw [GaussCoframeCore.derivative_apply,full_at,GaussCoframeCore.derivative_apply]
  exact he

private theorem coframe_full (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.momentum i) (SourceMixedNativeReturn.fullAction sharp) :=
  (coframe_derivative_full i sharp).smul_left (-Complex.I)

private theorem coframe_full_adjoint (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.adjoint i) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have he := LinearMap.congr_fun (coframe_full i (!sharp)).eq f
  change sourcePair f (GaussCoframeCore.adjoint i (SourceMixedNativeReturn.fullAction sharp g))=
    sourcePair f (SourceMixedNativeReturn.fullAction sharp (GaussCoframeCore.adjoint i g))
  rw [GaussCoframeKinetic.adjoint_pair,full_pair,full_pair,GaussCoframeKinetic.adjoint_pair]
  exact congrArg (fun q => sourcePair q g) he.symm


private theorem coframe_kinetic_full (sharp : Bool) : Commute GaussCoframeKinetic.kinetic (SourceMixedNativeReturn.fullAction sharp) := by
  unfold GaussCoframeKinetic.kinetic
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  unfold GaussCoframeKinetic.term
  exact (coframe_full_adjoint i sharp).mul_left ((real_full _ _ sharp).mul_left (coframe_full j sharp))

private theorem bracket_add {R : Type*} [Ring R] (A B C : R) :
    bracket (A+B) C=bracket A C+bracket B C := by unfold bracket;noncomm_ring

private theorem bracket_commute {R : Type*} [Ring R] {A B : R} (h : Commute A B) : bracket A B=0 :=
  sub_eq_zero.mpr h.eq

private theorem coframe_full_return (sharp : Bool) :
    bracket GaussCoframeForm.coframeAction (SourceMixedNativeReturn.fullAction sharp)=spinCurrent sharp := by
  have hcf : GaussCoframeForm.coframeAction=GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+
      spinPotential+multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth := by
    unfold GaussCoframeForm.coframeAction spinPotential
    abel
  rw [hcf]
  simp only [bracket_add,bracket_commute (coframe_kinetic_full sharp),
    bracket_commute (original_coframe_current_full sharp),bracket_commute (real_full _ _ sharp),zero_add,add_zero]
  rfl

/-- The original full source current retains matter and the four signed spin rows. -/
def originalCurrent (sharp : Bool) : End :=
  bracket matterAction (SourceMixedNativeReturn.fullAction sharp)+scalarCurrent sharp+reducedSpinCurrent sharp

/-- This is the full source current corrected by the actual compression defect. -/
def correctedCurrent (sharp : Bool) (F : Index) : End :=
  originalCurrent sharp-bracket (defectAction F) (SourceMixedNativeReturn.fullAction sharp)

theorem original_hamiltonian_yukawa_current (sharp : Bool) :
    bracket diagonalAction (SourceMixedNativeReturn.fullAction sharp)=originalCurrent sharp := by
  unfold diagonalAction nativeAction
  simp only [bracket_add,bracket_commute (original_electric_full sharp),
    bracket_commute (real_full potential potential_smooth sharp),original_scalar_first_current,
    coframe_full_return,original_spin_ladder_return]
  unfold originalCurrent
  abel

theorem original_compression_yukawa_current (sharp : Bool) (F : Index) :
    bracket (compressionCore F) (SourceMixedNativeReturn.fullAction sharp)=correctedCurrent sharp F := by
  have h := original_hamiltonian_yukawa_current sharp
  unfold correctedCurrent
  rw [←h]
  unfold defectAction bracket
  noncomm_ring

end LowEnergy.SourceClockYukawaHamiltonianCurrent
