import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceEscapeCurrent

/-! The full original remainder is retained when a weak kinetic solution meets the actual resolvent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceKineticTranspose
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory
open GaussNativeForm GaussNativePotential GaussCoframeForm GaussMatterCore
open SourceMinimalGraphParticular SourceEscapeCurrent
open FullYSourceResolventGraphSplice
open GaussUnitaryHistory (Index sourceFilter)
open scoped Topology InnerProductSpace

def kineticAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  scalarKinetic + gaugeKinetic + coframeAction - multiply volumePotential volumePotential_smooth

def remainderAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  matterAction + multiply potential potential_smooth + multiply volumePotential volumePotential_smooth

theorem action_split : diagonalAction = kineticAction + remainderAction := by
  unfold diagonalAction nativeAction kineticAction remainderAction
  abel

def kinetic : diagonal.domain →ₗ[ℂ] H :=
  embed.comp (kineticAction.comp coreEquiv.symm.toLinearMap)

def remainder : diagonal.domain →ₗ[ℂ] H :=
  embed.comp (remainderAction.comp coreEquiv.symm.toLinearMap)

theorem original_split (x : diagonal.domain) : diagonal x = kinetic x + remainder x := by
  change embed (diagonalAction (coreEquiv.symm x)) = _
  rw [action_split, LinearMap.add_apply, map_add]
  rfl

theorem kinetic_pair (x y : diagonal.domain) :
    inner ℂ (kinetic x) (y : H) = inner ℂ (x : H) (kinetic y) := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective x
  obtain ⟨g,rfl⟩ := coreEquiv.surjective y
  change inner ℂ (embed (kineticAction (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed (kineticAction (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply]
  change sourcePair (kineticAction f) g = sourcePair f (kineticAction g)
  unfold kineticAction
  simp only [LinearMap.add_apply, LinearMap.sub_apply, sourcePair, map_add, map_sub,
    inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
  exact congrArg₂ (· - ·)
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) (scalarKinetic_pair f g).symm
      (gaugeKinetic_pair f g).symm) (coframeAction_pair f g).symm)
    (multiply_pair _ _ f g).symm

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f) = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) hs)
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k) - star z • FullYSourceResolventGraphSplice.resolvent C (star z) k = k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f) - z • FullYSourceResolventGraphSplice.resolvent C z f = f at hf
  have hsym : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f) =
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := by
    exact hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k) - star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun v => inner ℂ v _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f) - z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left, inner_smul_left, inner_sub_right, inner_smul_right,
        hsym, starRingEnd_apply, star_star]
    _ = _ := congrArg (fun v => inner ℂ _ v) hf

def outerResidual (F : Index) (z : ℂ) (hz : z.im≠0) (k : diagonal.domain) : H :=
  finiteProjectionDefect F z hz k - remainder (sourceCore F z hz k)

/-- A transposition identity, with the weak kinetic equation as its explicit input. -/
theorem actual_weak_splice (F : Index) (z : ℂ) (hz : z.im≠0)
    (k : diagonal.domain) (f h : H)
    (weakEquation : ∀ x : diagonal.domain, inner ℂ (kinetic x) h = inner ℂ (x : H) f) :
    inner ℂ (k : H) (finiteResolvent F z f) =
      inner ℂ (k : H) (h+z • finiteResolvent F z h) +
        inner ℂ (outerResidual F (star z)
          (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k) h := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  let p := sourceCore F (star z) hs k
  have hk := congrArg (fun A : H →L[ℂ] H => A (k : H))
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) (star z) hs)
  change GaussGradedCompression.compression F (p : H)-star z • (p : H)=(k : H) at hk
  have hp : kinetic p = (k : H)+star z • (p : H)+outerResidual F (star z) hs k := by
    have hd := original_split p
    change kinetic p = (k : H)+star z • (p : H)+
      (diagonal p-GaussGradedCompression.compression F (p : H)-remainder p)
    rw [←hk]
    rw [hd]
    abel
  have hpair (y : H) : inner ℂ (k : H) (finiteResolvent F z y) = inner ℂ (p : H) y :=
    resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) z hz (k : H) y
  calc
    _ = inner ℂ (p : H) f := hpair f
    _ = inner ℂ (kinetic p) h := (weakEquation p).symm
    _ = _ := by
      rw [hp, inner_add_left, inner_add_left, inner_smul_left, starRingEnd_apply, star_star,
        inner_add_right, inner_smul_right, hpair h]

end LowEnergy.SourceKineticTranspose
