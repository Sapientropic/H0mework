import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalCompletedSector

/-! All three literal Gauss100 H0 components preserve the source-generated
canonical carrier, including adjoints, cross terms and Number contacts. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.CanonicalCompletedSector
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussDiagonalHistory
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff Distributions Topology

abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
def Commutes (A : End) : Prop := ∀ f, project (A f) = A (project f)

theorem commutes_add {A B : End} (hA : Commutes A) (hB : Commutes B) :
    Commutes (A+B) := by intro f; change project (A f+B f) = _; rw [map_add,hA,hB]; rfl

theorem commutes_smul {A : End} (hA : Commutes A) (c : ℂ) :
    Commutes (c • A) := by intro f; change project (c • A f) = _; rw [map_smul,hA]; rfl

theorem commutes_comp {A B : End} (hA : Commutes A) (hB : Commutes B) :
    Commutes (A.comp B) := fun f => (hA (B f)).trans (congrArg A (hB f))

theorem commutes_sum {ι : Type*} [Fintype ι] {A : ι → End}
    (commutes : ∀ i, Commutes (A i)) : Commutes (∑ i, A i) := by
  intro f
  simp only [LinearMap.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i _ => commutes i f)

theorem commutes_adjoint {A B : End} (hA : Commutes A)
    (paired : ∀ f h, sourcePair f (B h) = sourcePair (A f) h) : Commutes B := by
  intro f
  apply GaussCoreLabel.pair_separates
  intro h
  rw [project_pair,paired,←hA,←project_pair,←paired]

theorem derivative_project (f : QuantumTest) (z v : SourceCoordinateSlice) :
    fderiv ℝ (project f) z v = fiberProjection (fderiv ℝ f z v) := by
  let P := fiberProjection.restrictScalars ℝ
  have h := P.hasFDerivAt.comp z ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change fderiv ℝ (P ∘ f) z v = _
  rw [h.fderiv]
  rfl

theorem commutes_directional (v : GaussLiveMomentum.Ambient) : Commutes (directional v) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply,directional_apply,directional_apply,derivative_project]

theorem commutes_derivative (v : SourceCoordinateSlice) : Commutes (GaussCoframeCore.derivative v) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply,GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,derivative_project]

theorem commutes_real (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commutes (GaussNativeForm.multiply c smooth) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply,GaussNativeForm.multiply_apply,GaussNativeForm.multiply_apply,project_apply,map_smul]

theorem commutes_local (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) (source : ∀ z, Generator (A z)) :
    Commutes (localMultiplier A smooth) := by
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (projection_commutes (source z)).eq

theorem native_connection (v : GaussLiveMomentum.Ambient) :
    Commutes (localMultiplier (connection v) (connection_smooth v)) :=
  commutes_local _ _ (fun _ => Generator.native _)

theorem native_momentum (v : GaussLiveMomentum.Ambient) : Commutes (covariantMomentum v) :=
  commutes_smul (commutes_add (commutes_directional v) (native_connection v)) (-Complex.I)

theorem native_adjoint (v : GaussLiveMomentum.Ambient) : Commutes (GaussMomentumAdjoint.adjoint v) :=
  commutes_adjoint (native_momentum v) (GaussNativeForm.adjoint_pair v)

theorem native_sandwich (v w : GaussLiveMomentum.Ambient)
    (c : SourceCoordinateSlice → ℝ) (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commutes (GaussNativeForm.sandwich v w c smooth) :=
  commutes_comp (native_adjoint v) (commutes_comp (commutes_real c smooth) (native_momentum w))

theorem native_action : Commutes GaussNativeForm.nativeAction := by
  have hs : Commutes GaussNativeForm.scalarKinetic :=
    commutes_smul (commutes_sum (fun _ => native_sandwich _ _ _ _)) (1/2)
  have hg : Commutes GaussNativeForm.gaugeKinetic :=
    commutes_smul (commutes_sum (fun _ => commutes_sum (fun _ => commutes_sum
      (fun _ => native_sandwich _ _ _ _)))) (1/2)
  exact commutes_add (commutes_add hs hg) (commutes_real _ _)

theorem coframe_momentum (i : Fin 6) : Commutes (GaussCoframeCore.momentum i) :=
  commutes_smul (commutes_derivative (GaussCoframeCore.coframeDirection i)) (-Complex.I)

theorem coframe_adjoint (i : Fin 6) : Commutes (GaussCoframeCore.adjoint i) :=
  commutes_adjoint (coframe_momentum i) (GaussCoframeKinetic.adjoint_pair i)

theorem coframe_kinetic : Commutes GaussCoframeKinetic.kinetic :=
  commutes_sum (fun i => commutes_sum (fun j =>
    commutes_comp (coframe_adjoint i) (commutes_comp (commutes_real _ _) (coframe_momentum j))))

theorem spin_current (a : Fin 7) : Commutes (GaussCoframeSpin.current a) :=
  commutes_local (fun _ => GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a))
    (fun _ => contDiffAt_const) (fun _ => Generator.spin a)

theorem mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : Commutes (GaussCoframeForm.mixed i a c smooth) :=
  commutes_smul (commutes_add
    (commutes_comp (spin_current a) (commutes_comp (commutes_real c smooth) (coframe_momentum i)))
    (commutes_comp (coframe_adjoint i) (commutes_comp (commutes_real c smooth) (spin_current a)))) (1/2)

theorem number : Commutes GaussCoframeForm.number := by
  have he (f : QuantumTest) (z : SourceCoordinateSlice) :
      GaussCoframeForm.number f z = GaussFockWeights.weight (fun n => (n : ℂ)) (f z) := by
    apply PiLp.ext
    intro word
    exact GaussCoframeForm.number_apply f z word
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply,he,he,project_apply]
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (projection_commutes (Generator.number _)).eq

theorem coframe_action : Commutes GaussCoframeForm.coframeAction := by
  have hc : Commutes GaussCoframeForm.currentAction :=
    commutes_add (commutes_add (commutes_add (mixed _ _ _ _) (mixed _ _ _ _))
      (mixed _ _ _ _)) (mixed _ _ _ _)
  have hs (a : Fin 7) : Commutes (GaussCoframeForm.spinSquare a) :=
    commutes_smul (commutes_comp (spin_current a)
      (commutes_comp (commutes_real _ _) (spin_current a))) _
  have hn : Commutes GaussCoframeForm.numberShift :=
    commutes_smul (commutes_add (commutes_comp number (commutes_real _ _))
      (commutes_comp (commutes_real _ _) number)) (1/2)
  exact commutes_add (commutes_add (commutes_add (commutes_add coframe_kinetic hc)
    (commutes_sum hs)) hn) (commutes_real _ _)

theorem matter_action : Commutes GaussMatterCore.matterAction :=
  commutes_sum (fun i => commutes_sum (fun b =>
    commutes_local _ _ (fun z => Generator.matter i b z)))

theorem diagonal_action : Commutes diagonalAction :=
  commutes_add (commutes_add native_action coframe_action) matter_action

theorem stable (f : diagonal.domain) : projection (f : H) ∈ diagonal.domain := by
  obtain ⟨g,hg⟩ := embed_surjective_core f
  change projection (f : H) ∈ Core
  rw [←hg,projection_core]
  exact embed_mem_core _

theorem diagonal_commutes (f : diagonal.domain) :
    diagonal ⟨projection (f : H),stable f⟩ = projection (diagonal f) := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective f
  have hp : (⟨projection (embed f),stable (coreEquiv f)⟩ : diagonal.domain) =
      coreEquiv (project f) := Subtype.ext (projection_core f)
  erw [hp]
  change embed (diagonalAction (coreEquiv.symm (coreEquiv (project f)))) =
    projection (embed (diagonalAction (coreEquiv.symm (coreEquiv f))))
  rw [coreEquiv.symm_apply_apply,coreEquiv.symm_apply_apply,projection_core]
  exact congrArg embed (diagonal_action f).symm

theorem projection_idempotent : projection * projection = projection := by
  apply ContinuousLinearMap.ext
  intro x
  have he : Set.EqOn (fun x => projection (projection x)) (fun x => projection x) (Core : Set H) := by
    intro y hy
    obtain ⟨f,hf⟩ := embed_surjective_core ⟨y,hy⟩
    change embed f = y at hf
    dsimp only
    rw [←hf,projection_core,projection_core]
    congr 1
    apply DFunLike.ext
    intro z
    exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) projection_square
  exact he.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense x)

#print axioms diagonal_commutes
#print axioms projection_idempotent
end LowEnergy.CanonicalCompletedSector
