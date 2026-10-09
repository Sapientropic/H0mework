import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualSignedSectorProjection

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSignedSector
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open ActiveMatterSectorCharge
open scoped ContDiff Distributions

abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def Commutes (g : ℝ) (A : End) : Prop := ∀ f, project g (A f) = A (project g f)

theorem commutes_add (g : ℝ) {A B : End} (hA : Commutes g A) (hB : Commutes g B) :
    Commutes g (A+B) := by intro f; change project g (A f+B f) = _; rw [map_add, hA, hB]; rfl

theorem commutes_smul (g : ℝ) {A : End} (hA : Commutes g A) (c : ℂ) :
    Commutes g (c • A) := by intro f; change project g (c • A f) = _; rw [map_smul, hA]; rfl

theorem commutes_comp (g : ℝ) {A B : End} (hA : Commutes g A) (hB : Commutes g B) :
    Commutes g (A.comp B) := fun f => (hA (B f)).trans (congrArg A (hB f))

theorem commutes_sum {ι : Type*} [Fintype ι] (g : ℝ) {A : ι → End}
    (commutes : ∀ i, Commutes g (A i)) : Commutes g (∑ i, A i) := by
  intro f
  simp only [LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => commutes i f)

theorem commutes_adjoint (g : ℝ) {A B : End} (hA : Commutes g A)
    (paired : ∀ f h, sourcePair f (B h) = sourcePair (A f) h) : Commutes g B := by
  intro f
  apply GaussCoreLabel.pair_separates
  intro h
  rw [project_pair, paired, ← hA, ← project_pair, ← paired]

theorem derivative_project (g : ℝ) (f : QuantumTest) (z v : SourceCoordinateSlice) :
    fderiv ℝ (project g f) z v = fiberPiece g (fderiv ℝ f z v) := by
  let P := (fiberPiece g).restrictScalars ℝ
  have h := P.hasFDerivAt.comp z ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change fderiv ℝ (P ∘ f) z v = _
  rw [h.fderiv]
  rfl

theorem commutes_directional (g : ℝ) (v : GaussLiveMomentum.Ambient) : Commutes g (directional v) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply, directional_apply, directional_apply, derivative_project]

theorem commutes_derivative (g : ℝ) (v : SourceCoordinateSlice) : Commutes g (GaussCoframeCore.derivative v) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply, GaussCoframeCore.derivative_apply, GaussCoframeCore.derivative_apply, derivative_project]

theorem commutes_real (g : ℝ) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commutes g (GaussNativeForm.multiply c smooth) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply, GaussNativeForm.multiply_apply, GaussNativeForm.multiply_apply, project_apply, map_smul]

theorem commutes_matrix (g : ℝ) (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val)
    (preserves : ∀ z, ActiveMatterSectorCharge.Preserves (A z)) : Commutes g (GaussQuantumMultiplier.action A smooth) := by
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (fiberWeight_quantized (fun l => if l = g then 1 else 0) (A z) (preserves z)).eq


theorem native_connection (g : ℝ) (v : GaussLiveMomentum.Ambient) :
    Commutes g (localMultiplier (connection v) (connection_smooth v)) := by
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (fiberWeight_quantized (fun l => if l = g then 1 else 0)
      (GaussNativeMatter.nativeFull (GaussLiveMomentum.inverseL z v).1) (native_preserves _)).eq

theorem native_momentum (g : ℝ) (v : GaussLiveMomentum.Ambient) : Commutes g (covariantMomentum v) :=
  commutes_smul g (commutes_add g (commutes_directional g v) (native_connection g v)) (-Complex.I)

theorem native_adjoint (g : ℝ) (v : GaussLiveMomentum.Ambient) : Commutes g (GaussMomentumAdjoint.adjoint v) :=
  commutes_adjoint g (native_momentum g v) (GaussNativeForm.adjoint_pair v)

theorem native_sandwich (g : ℝ) (v w : GaussLiveMomentum.Ambient)
    (c : SourceCoordinateSlice → ℝ) (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commutes g (GaussNativeForm.sandwich v w c smooth) :=
  commutes_comp g (native_adjoint g v) (commutes_comp g (commutes_real g c smooth) (native_momentum g w))

theorem native_action (g : ℝ) : Commutes g GaussNativeForm.nativeAction := by
  have hs : Commutes g GaussNativeForm.scalarKinetic :=
    commutes_smul g (commutes_sum g (fun _ => native_sandwich g _ _ _ _)) (1/2)
  have hg : Commutes g GaussNativeForm.gaugeKinetic :=
    commutes_smul g (commutes_sum g (fun _ => commutes_sum g (fun _ => commutes_sum g
      (fun _ => native_sandwich g _ _ _ _)))) (1/2)
  exact commutes_add g (commutes_add g hs hg) (commutes_real g _ _)

theorem coframe_momentum (g : ℝ) (i : Fin 6) : Commutes g (GaussCoframeCore.momentum i) :=
  commutes_smul g (commutes_derivative g (GaussCoframeCore.coframeDirection i)) (-Complex.I)

theorem coframe_adjoint (g : ℝ) (i : Fin 6) : Commutes g (GaussCoframeCore.adjoint i) :=
  commutes_adjoint g (coframe_momentum g i) (GaussCoframeKinetic.adjoint_pair i)

theorem coframe_kinetic (g : ℝ) : Commutes g GaussCoframeKinetic.kinetic :=
  commutes_sum g (fun i => commutes_sum g (fun j =>
    commutes_comp g (coframe_adjoint g i) (commutes_comp g (commutes_real g _ _) (coframe_momentum g j))))

theorem spin_current (g : ℝ) (a : Fin 7) : Commutes g (GaussCoframeSpin.current a) :=
  commutes_matrix g _ _ (fun _ => spin_preserves a)

theorem mixed (g : ℝ) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : Commutes g (GaussCoframeForm.mixed i a c smooth) :=
  commutes_smul g (commutes_add g
    (commutes_comp g (spin_current g a) (commutes_comp g (commutes_real g c smooth) (coframe_momentum g i)))
    (commutes_comp g (coframe_adjoint g i) (commutes_comp g (commutes_real g c smooth) (spin_current g a)))) (1/2)

theorem number (g : ℝ) : Commutes g GaussCoframeForm.number := by
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  rw [project_apply, fiberPiece_apply, GaussCoframeForm.number_apply,
    GaussCoframeForm.number_apply, project_apply, fiberPiece_apply]
  by_cases h : value word = g <;> simp [h]

theorem coframe_action (g : ℝ) : Commutes g GaussCoframeForm.coframeAction := by
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

theorem matter_action (g : ℝ) : Commutes g GaussMatterCore.matterAction :=
  commutes_sum g (fun i => commutes_sum g (fun b =>
    commutes_matrix g _ _ (matter_preserves i b)))

theorem diagonal_action (g : ℝ) : Commutes g diagonalAction :=
  commutes_add g (commutes_add g (native_action g) (coframe_action g)) (matter_action g)

theorem stable (g : ℝ) (f : diagonal.domain) : ActualSignedSector.projection g (f : H) ∈ diagonal.domain :=
  ActualSignedSector.projection_preserves_core g f f.property

theorem diagonal_commutes (g : ℝ) (f : diagonal.domain) :
    diagonal ⟨ActualSignedSector.projection g (f : H), stable g f⟩ = ActualSignedSector.projection g (diagonal f) := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective f
  have hp : (⟨ActualSignedSector.projection g (embed f), stable g (coreEquiv f)⟩ : diagonal.domain) =
      coreEquiv (project g f) := Subtype.ext (embed_project g f).symm
  erw [hp]
  change embed (diagonalAction (coreEquiv.symm (coreEquiv (project g f)))) =
    ActualSignedSector.projection g (embed (diagonalAction (coreEquiv.symm (coreEquiv f))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply, ← embed_project]
  exact congrArg embed (diagonal_action g f).symm

/-- The original full Yukawa action preserves the signed active matter sector. -/
theorem originalY (s : ℝ) : Commutes s GaussYukawaOperator.originalAction := by
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (fiberWeight_quantized (fun r => if r=s then 1 else 0)
      (GaussYukawaCoefficient.fullMatrix (GaussNativePotential.scalarField z)) (yukawa_preserves _)).eq

theorem independentSharp (s : ℝ) : Commutes s GaussFullHamiltonian.adjointAction :=
  commutes_adjoint s (originalY s) GaussFullHamiltonian.yukawa_pair

end LowEnergy.ActualSignedSector
