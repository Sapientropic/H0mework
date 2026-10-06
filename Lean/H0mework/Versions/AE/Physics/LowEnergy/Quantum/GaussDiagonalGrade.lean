import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussCoreLabel

/-! The actual source H0 pays the full Number/G time-kernel contract. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussDiagonalGrade
open GaussCoreLabel GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussFockLabel
open GaussHistoryHilbert NativeHistoryGrade GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Distributions

theorem native_connection (g : Label) (v : GaussLiveMomentum.Ambient) :
    Commutes g (localMultiplier (connection v) (connection_smooth v)) := by
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (blockWeight_quantized (fun l => if l = g then 1 else 0)
      (GaussNativeMatter.nativeFull (GaussLiveMomentum.inverseL z v).1) (native_preserves _)).eq

theorem native_momentum (g : Label) (v : GaussLiveMomentum.Ambient) : Commutes g (covariantMomentum v) :=
  commutes_smul g (commutes_add g (commutes_directional g v) (native_connection g v)) (-Complex.I)

theorem native_adjoint (g : Label) (v : GaussLiveMomentum.Ambient) : Commutes g (GaussMomentumAdjoint.adjoint v) :=
  commutes_adjoint g (native_momentum g v) (GaussNativeForm.adjoint_pair v)

theorem native_sandwich (g : Label) (v w : GaussLiveMomentum.Ambient)
    (c : SourceCoordinateSlice → ℝ) (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commutes g (GaussNativeForm.sandwich v w c smooth) :=
  commutes_comp g (native_adjoint g v) (commutes_comp g (commutes_real g c smooth) (native_momentum g w))

theorem native_action (g : Label) : Commutes g GaussNativeForm.nativeAction := by
  have hs : Commutes g GaussNativeForm.scalarKinetic :=
    commutes_smul g (commutes_sum g (fun _ => native_sandwich g _ _ _ _)) (1/2)
  have hg : Commutes g GaussNativeForm.gaugeKinetic :=
    commutes_smul g (commutes_sum g (fun _ => commutes_sum g (fun _ => commutes_sum g
      (fun _ => native_sandwich g _ _ _ _)))) (1/2)
  exact commutes_add g (commutes_add g hs hg) (commutes_real g _ _)

theorem coframe_momentum (g : Label) (i : Fin 6) : Commutes g (GaussCoframeCore.momentum i) :=
  commutes_smul g (commutes_derivative g (GaussCoframeCore.coframeDirection i)) (-Complex.I)

theorem coframe_adjoint (g : Label) (i : Fin 6) : Commutes g (GaussCoframeCore.adjoint i) :=
  commutes_adjoint g (coframe_momentum g i) (GaussCoframeKinetic.adjoint_pair i)

theorem coframe_kinetic (g : Label) : Commutes g GaussCoframeKinetic.kinetic :=
  commutes_sum g (fun i => commutes_sum g (fun j =>
    commutes_comp g (coframe_adjoint g i) (commutes_comp g (commutes_real g _ _) (coframe_momentum g j))))

theorem spin_current (g : Label) (a : Fin 7) : Commutes g (GaussCoframeSpin.current a) :=
  commutes_matrix g _ _ (fun _ => spin_preserves a)

theorem mixed (g : Label) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : Commutes g (GaussCoframeForm.mixed i a c smooth) :=
  commutes_smul g (commutes_add g
    (commutes_comp g (spin_current g a) (commutes_comp g (commutes_real g c smooth) (coframe_momentum g i)))
    (commutes_comp g (coframe_adjoint g i) (commutes_comp g (commutes_real g c smooth) (spin_current g a)))) (1/2)

theorem number (g : Label) : Commutes g GaussCoframeForm.number := by
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  rw [project_apply, fiberPiece_apply, GaussCoframeForm.number_apply,
    GaussCoframeForm.number_apply, project_apply, fiberPiece_apply]
  by_cases h : sourceLabel word = g <;> simp [h]

theorem coframe_action (g : Label) : Commutes g GaussCoframeForm.coframeAction := by
  have hc : Commutes g GaussCoframeForm.currentAction :=
    commutes_add g (commutes_add g (commutes_add g (mixed g _ _ _ _) (mixed g _ _ _ _))
      (mixed g _ _ _ _)) (mixed g _ _ _ _)
  have hs (a : Fin 7) : Commutes g (GaussCoframeForm.spinSquare a) :=
    commutes_smul g (commutes_comp g (spin_current g a)
      (commutes_comp g (commutes_real g _ _) (spin_current g a))) _
  have hn : Commutes g GaussCoframeForm.numberShift :=
    commutes_smul g (commutes_add g (commutes_comp g (number g) (commutes_real g _ _))
      (commutes_comp g (commutes_real g _ _) (number g))) (1/2)
  exact commutes_add g (commutes_add g (commutes_add g (commutes_add g (coframe_kinetic g) hc)
    (commutes_sum g hs)) hn) (commutes_real g _ _)

theorem matter_action (g : Label) : Commutes g GaussMatterCore.matterAction :=
  commutes_sum g (fun i => commutes_sum g (fun b =>
    commutes_matrix g _ _ (matter_preserves i b)))

theorem diagonal_action (g : Label) : Commutes g diagonalAction :=
  commutes_add g (commutes_add g (native_action g) (coframe_action g)) (matter_action g)

theorem stable (g : Label) (f : diagonal.domain) : NativeHistoryGrade.projection g (f : H) ∈ diagonal.domain :=
  NativeHistoryGrade.projection_preserves_core g f f.property

theorem diagonal_commutes (g : Label) (f : diagonal.domain) :
    diagonal ⟨NativeHistoryGrade.projection g (f : H), stable g f⟩ = NativeHistoryGrade.projection g (diagonal f) := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective f
  have hp : (⟨NativeHistoryGrade.projection g (embed f), stable g (coreEquiv f)⟩ : diagonal.domain) =
      coreEquiv (project g f) := Subtype.ext (embed_project g f).symm
  erw [hp]
  change embed (diagonalAction (coreEquiv.symm (coreEquiv (project g f)))) =
    NativeHistoryGrade.projection g (embed (diagonalAction (coreEquiv.symm (coreEquiv f))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply, ← embed_project]
  exact congrArg embed (diagonal_action g f).symm

def history (t : ℝ) : H →L[ℂ] H := NativeHistoryGrade.history diagonal diagonal_pair t

theorem history_blocks (g : Label) (t : ℝ) :
    NativeHistoryGrade.projection g * history t = history t * NativeHistoryGrade.projection g := by
  rw [history, history_left_block, history_right_block]

theorem history_derivative (f : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun u => history u (f : H)) ((-Complex.I) • history t (diagonal f)) t :=
  NativeHistoryGrade.history_core_derivative diagonal diagonal_pair stable diagonal_commutes f (diagonal_invariant f) t

theorem retarded_source (f g : diagonal.domain) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ), eta' t * inner ℂ (history t (f : H)) (g : H) +
      eta t * (Complex.I * inner ℂ (history t (f : H)) (diagonal g))) =
      -eta 0 * inner ℂ (f : H) (g : H) :=
  NativeHistoryGrade.history_retarded_identity diagonal diagonal_pair diagonal_dense stable diagonal_commutes
    f g (diagonal_invariant f) (diagonal_invariant g) eta eta' differentiable derivative_continuous b end_zero

#print axioms diagonal_commutes
#print axioms history_derivative
#print axioms retarded_source
end LowEnergy.GaussDiagonalGrade
