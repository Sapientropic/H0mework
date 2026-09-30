import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Passivity

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalResponseNext
open Set
open NativeWindowHistoryCausalResponse
noncomputable section

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem response_original (A : ℝ → E →L[ℝ] E) (Ac : Continuous A)
    (f : ℝ → E) (fc : Continuous f) (a B : ℝ) (aB : a≤B)
    (path : ℝ → E) (initial : path a=0)
    (evolution : ∀ t∈Icc a B,HasDerivWithinAt path (A t (path t)+f t) (Icc a B) t) :
    EqOn (response A Ac f fc a B aB) path (Icc a B) := by
  have paired : EqOn (lifted A Ac f fc a B aB) (fun t => (path t,1)) (Icc a B) := by
    apply NativeWindowHistoryPropagator.applied_original (block A f) (block_continuous A Ac f fc)
      a B aB (0,1) (fun t => (path t,1))
    · rw [initial]
    · intro t ht
      simpa only [block_apply,one_smul] using
        (evolution t ht).prodMk (hasDerivWithinAt_const t (Icc a B) (1 : ℝ))
  exact fun t ht => congrArg Prod.fst (paired ht)

theorem response_translate (A A' : ℝ → E →L[ℝ] E) (Ac : Continuous A) (Ac' : Continuous A')
    (f f' : ℝ → E) (fc : Continuous f) (fc' : Continuous f')
    (c a B : ℝ) (aB : a≤B)
    (actions : EqOn (fun t => A (c+t)) A' (Icc a B))
    (inputs : EqOn (fun t => f (c+t)) f' (Icc a B)) :
    EqOn (fun t => response A Ac f fc (c+a) (c+B) (add_le_add_right aB c) (c+t))
      (response A' Ac' f' fc' a B aB) (Icc a B) := by
  let p := fun t => response A Ac f fc (c+a) (c+B) (add_le_add_right aB c) (c+t)
  have initial : p a=0 := response_initial A Ac f fc (c+a) (c+B) (add_le_add_right aB c)
  have evolution (t : ℝ) (ht : t∈Icc a B) :
      HasDerivWithinAt p (A' t (p t)+f' t) (Icc a B) t := by
    have into : MapsTo (fun s : ℝ => c+s) (Icc a B) (Icc (c+a) (c+B)) :=
      fun s hs => ⟨add_le_add_right hs.1 c,add_le_add_right hs.2 c⟩
    have old := response_derivative A Ac f fc (c+a) (c+B) (add_le_add_right aB c) (c+t) (into ht)
    have shifted := HasDerivWithinAt.scomp (F := E) t old ((hasDerivAt_id t).const_add c).hasDerivWithinAt into
    have rate : HasDerivWithinAt p (A (c+t) (p t)+f (c+t)) (Icc a B) t := by
      simpa only [one_smul,Function.comp_def] using! shifted
    exact rate.congr_deriv (congrArg₂ (fun (op : E →L[ℝ] E) (y : E) => op (p t)+y)
      (actions ht) (inputs ht))
  exact (response_original A' Ac' f' fc' a B aB p initial evolution).symm
end Generic

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanBlocks (bath)
open NativeWindowHistoryCausalBath (bath_continuous bath_next)
open NativeWindowHistoryCausalPassivity
open NativeWholeResolvent (wholePhysical)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

theorem bathResponse_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (f f' : ℝ → H) (fc : Continuous f) (fc' : Continuous f')
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a)
    (inputs : EqOn (fun t => f (step.2.clockAdvance+t)) f' (Icc a B)) :
    EqOn (fun t => bathResponse seed M f fc (step.2.clockAdvance+a) (step.2.clockAdvance+B)
      (add_le_add_right aB _) (step.2.clockAdvance+t))
      (bathResponse step.1 M f' fc' a B aB) (Icc a B) := by
  simpa only [bathResponse] using! response_translate (E := H)
    (bath seed M) (bath step.1 M) (bath_continuous seed M) (bath_continuous step.1 M)
    f f' fc fc' step.2.clockAdvance a B aB
    (fun t ht => bath_next seed M step generated t (a0.trans ht.1)) inputs

theorem creationResponse_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (v v' : ℝ → wholePhysical) (vc : Continuous v) (vc' : Continuous v')
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a)
    (curves : EqOn (fun t => v (step.2.clockAdvance+t)) v' (Icc a B)) :
    EqOn (fun t => creationResponse seed M v vc (step.2.clockAdvance+a) (step.2.clockAdvance+B)
      (add_le_add_right aB _) (step.2.clockAdvance+t))
      (creationResponse step.1 M v' vc' a B aB) (Icc a B) := by
  apply bathResponse_next seed M step generated (creationInput seed M v) (creationInput step.1 M v')
    (creationInput_continuous seed M v vc) (creationInput_continuous step.1 M v' vc') a B aB a0
  intro t ht
  exact congrArg₂ (fun (op : wholePhysical →L[ℝ] H) (x : wholePhysical) => op x)
    (NativeWindowHistoryMeanBlocks.creation_next seed M step generated t (a0.trans ht.1)) (curves ht)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalResponseNext
