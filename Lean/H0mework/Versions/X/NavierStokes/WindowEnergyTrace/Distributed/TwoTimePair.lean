import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredRate
import Mathlib.Analysis.InnerProductSpace.TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology TensorProduct
namespace SaturationMonoid.NavierStokes.NativeResponseJointControl
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed
open NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWindowTraceDualEvolution (inverse lifted)
open NativeWindowTraceAdjoint (dual)
noncomputable section
variable {nu : Viscosity}

-- The coefficient range carries the original physical L² pairing.
abbrev Velocity (M : ℕ) := LinearMap.range (coefficients (modes M))
abbrev Pair (M : ℕ) := Velocity M ⊗[ℝ] Velocity M

local instance coefficientHilbert (M : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℂ (modes M×Coordinate)) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : modes M×Coordinate => ℂ)

local instance velocityHilbert (M : ℕ) : InnerProductSpace ℝ (Velocity M) :=
  Submodule.innerProductSpace (LinearMap.range (coefficients (modes M)))

noncomputable instance (M : ℕ) : NormedAddCommGroup (Pair M) :=
  TensorProduct.instNormedAddCommGroup (𝕜 := ℝ) (E := Velocity M) (F := Velocity M)

instance (M : ℕ) : InnerProductSpace ℝ (Pair M) :=
  TensorProduct.instInnerProductSpace (𝕜 := ℝ) (E := Velocity M) (F := Velocity M)

def velocityEquiv (M : ℕ) : physicalSpace (modes M) ≃ₗ[ℝ] Velocity M :=
  LinearEquiv.ofInjective (coefficients (modes M)) (coefficients_injective (modes M))

def encode (M : ℕ) : physicalSpace (modes M) →L[ℝ] Velocity M :=
  (velocityEquiv M).toLinearMap.toContinuousLinearMap

def decode (M : ℕ) : Velocity M →L[ℝ] physicalSpace (modes M) :=
  (velocityEquiv M).symm.toLinearMap.toContinuousLinearMap

theorem decode_encode (M : ℕ) (v : physicalSpace (modes M)) : decode M (encode M v)=v :=
  (velocityEquiv M).symm_apply_apply v

def pair (M : ℕ) (u p : physicalSpace (modes M)) : Pair M :=
  encode M u ⊗ₜ[ℝ] encode M p

def pairCLM (M : ℕ) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) →L[ℝ] Pair M :=
  (TensorProduct.mkL ℝ (Velocity M) (Velocity M)).bilinearComp (encode M) (encode M)

theorem pairCLM_apply (M : ℕ) (u p : physicalSpace (modes M)) : pairCLM M u p=pair M u p := rfl

theorem pair_inner (M : ℕ) (u p v q : physicalSpace (modes M)) :
    inner ℝ (pair M u p) (pair M v q)=pairing (modes M) u v*pairing (modes M) p q := by
  rw [pair,pair]
  erw [TensorProduct.inner_tmul]
  rfl

theorem pair_norm_square (M : ℕ) (u p : physicalSpace (modes M)) :
    ‖pair M u p‖^2=‖coefficients (modes M) u‖^2*‖coefficients (modes M) p‖^2 := by
  calc
    _=inner ℝ (pair M u p) (pair M u p) := (real_inner_self_eq_norm_sq _).symm
    _=pairing (modes M) u u*pairing (modes M) p p := pair_inner M u p u p
    _=_ := by
      change inner ℝ (coefficients (modes M) u) (coefficients (modes M) u)*
        inner ℝ (coefficients (modes M) p) (coefficients (modes M) p)=_
      rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]

def row (M : ℕ) (k l : modes M) (i j : Coordinate) : Pair M →ₗ[ℝ] ℂ :=
  let first := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : modes M×Coordinate => ℂ) (k,i)).comp
    (LinearMap.range (coefficients (modes M))).subtypeL
  let last := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : modes M×Coordinate => ℂ) (l,j)).comp
    (LinearMap.range (coefficients (modes M))).subtypeL
  TensorProduct.lift (((ContinuousLinearMap.mul ℝ ℂ).bilinearComp first last).toLinearMap₁₂)

theorem row_pair (M : ℕ) (k l : modes M) (i j : Coordinate) (u p : physicalSpace (modes M)) :
    row M k l i j (pair M u p)=u.1 k.1 i*p.1 l.1 j := by
  rw [row,pair,TensorProduct.lift.tmul]
  rfl

-- This contraction uses the quarter encoding, including all nine rows and zero output wave.
def diagonal (M : ℕ) : Pair M →L[ℝ] NativeCompleteStressCarrier.Space :=
  LinearMap.toContinuousLinearMap (TensorProduct.lift
    (((NativeResponseTensorPayment.pairTensorCLM M).bilinearComp (decode M) (decode M)).toLinearMap₁₂))

theorem diagonal_pair (M : ℕ) (u p : physicalSpace (modes M)) :
    diagonal M (pair M u p)=NativeResponseTensorPayment.pairTensor M u p := by
  change TensorProduct.lift _ (encode M u ⊗ₜ[ℝ] encode M p)=_
  rw [TensorProduct.lift.tmul]
  change NativeResponseTensorPayment.pairTensorCLM M (decode M (encode M u)) (decode M (encode M p))=_
  rw [decode_encode,decode_encode]
  rfl

def rightInverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : Pair M →L[ℝ] Pair M :=
  LinearMap.toContinuousLinearMap (TensorProduct.map (LinearMap.id : Velocity M →ₗ[ℝ] Velocity M)
    (((encode M).comp ((inverse seed M F radius time).comp (decode M))).toLinearMap))

theorem rightInverse_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (u p : physicalSpace (modes M)) :
    rightInverse seed M F radius time (pair M u p)=pair M u (lifted seed M F radius time p) := by
  change TensorProduct.map (LinearMap.id : Velocity M →ₗ[ℝ] Velocity M)
    (((encode M).comp ((inverse seed M F radius time).comp (decode M))).toLinearMap)
    (encode M u ⊗ₜ[ℝ] encode M p)=_
  rw [TensorProduct.map_tmul]
  change encode M u ⊗ₜ[ℝ] encode M (inverse seed M F radius time (decode M (encode M p)))=_
  rw [decode_encode]
  rfl

theorem original_centered_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (p : physicalSpace (modes M)) :
    diagonal M (rightInverse seed M F radius time
      (pair M (NativeCenteredResponseTensor.centered seed M frame time) p))=
      NativeCenteredResponseTensor.tensor seed M F radius frame time p := by
  rw [rightInverse_pair,diagonal_pair]
  rfl

private theorem forward_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (u : physicalSpace (modes M)) :
    pairing (modes M) u (NativeWindowTraceAdjoint.forward seed M time u) =
      -nu.coeff*curlPair (modes M) u.1 u.1 :=
  physicalOperator_pairing (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time) u

private theorem dual_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (p : physicalSpace (modes M)) :
    pairing (modes M) p (dual seed M time p) = -nu.coeff*curlPair (modes M) p.1 p.1 := by
  rw [← NativeWindowTraceAdjoint.adjoint_pairing,pairing_symmetric]
  exact forward_energy seed M time p

theorem antidirectional_heat (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (s t : ℝ) (v p : physicalSpace (modes M)) :
    2*inner ℝ (pair M v p)
      (pair M (NativeWindowTraceAdjoint.forward seed M s v) p+pair M v (dual seed M t p)) =
      -2*nu.coeff*(curlPair (modes M) v.1 v.1*‖coefficients (modes M) p‖^2+
        ‖coefficients (modes M) v‖^2*curlPair (modes M) p.1 p.1) := by
  rw [inner_add_right,pair_inner,pair_inner,forward_energy,dual_energy]
  have normed (w : physicalSpace (modes M)) : pairing (modes M) w w=‖coefficients (modes M) w‖^2 := by
    change inner ℝ (coefficients (modes M) w) (coefficients (modes M) w)=_
    exact real_inner_self_eq_norm_sq _
  rw [normed,normed]
  ring

private theorem bilinear_derivative {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {u : ℝ → E} {v : ℝ → F} {u' : E} {v' : F} {time : ℝ}
    (du : HasDerivAt u u' time) (dv : HasDerivAt v v' time) :
    HasDerivAt (fun t => B (u t) (v t)) (B u' (v time)+B (u time) v') time :=
  (B.hasFDerivAt.comp_hasDerivAt time du).clm_apply dv

-- The two native actions retain their own times along (s + h, t - h).
theorem pair_directional_writer (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (s t : ℝ) {u p : ℝ → physicalSpace (modes M)} {f g : physicalSpace (modes M)}
    (du : HasDerivAt u (NativeWindowTraceAdjoint.forward seed M s (u s)+f) s)
    (dp : HasDerivAt p (-dual seed M t (p t)-g) t) :
    HasDerivAt (fun h => pair M (u (s+h)) (p (t-h)))
      (pair M (NativeWindowTraceAdjoint.forward seed M s (u s)+f) (p t)+
        pair M (u s) (dual seed M t (p t)+g)) 0 := by
  have left := du.scomp_of_eq 0 ((hasDerivAt_const (0 : ℝ) s).add (hasDerivAt_id (0 : ℝ))) (by simp)
  have right := dp.scomp_of_eq 0 ((hasDerivAt_const (0 : ℝ) t).sub (hasDerivAt_id (0 : ℝ))) (by simp)
  have l : HasDerivAt (fun h => u (s+h)) (NativeWindowTraceAdjoint.forward seed M s (u s)+f) 0 := by
    simpa only [zero_add,one_smul,Function.comp_def,Pi.add_apply,id_eq] using! left
  have r : HasDerivAt (fun h => p (t-h)) (dual seed M t (p t)+g) 0 := by
    apply right.congr_deriv
    simp only [zero_sub,neg_one_smul]
    abel
  simpa only [pairCLM_apply,add_zero,sub_zero] using bilinear_derivative (pairCLM M) l r

theorem pair_directional_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (s t : ℝ) {u p : ℝ → physicalSpace (modes M)} {f g : physicalSpace (modes M)}
    (du : HasDerivAt u (NativeWindowTraceAdjoint.forward seed M s (u s)+f) s)
    (dp : HasDerivAt p (-dual seed M t (p t)-g) t) :
    HasDerivAt (fun h => ‖pair M (u (s+h)) (p (t-h))‖^2)
      (-2*nu.coeff*(curlPair (modes M) (u s).1 (u s).1*‖coefficients (modes M) (p t)‖^2+
        ‖coefficients (modes M) (u s)‖^2*curlPair (modes M) (p t).1 (p t).1)+
        2*inner ℝ (pair M (u s) (p t)) (pair M f (p t)+pair M (u s) g)) 0 := by
  have writer := pair_directional_writer seed M s t du dp
  have principal := antidirectional_heat seed M s t (u s) (p t)
  apply writer.norm_sq.congr_deriv
  simp only [add_zero,sub_zero]
  change 2*inner ℝ (pair M (u s) (p t))
    (pairCLM M (_+_) (p t)+pairCLM M (u s) (_+_))=_
  simp only [map_add,add_apply,pairCLM_apply,inner_add_right] at ⊢ principal
  linarith only [principal]

theorem source_pair_square_writer (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (observation frame : ℝ) (test : physicalSpace (modes M)) (a b : ℝ) (ordered : a ≤ b) :
    ∀ᵐ s : ℝ,0 ≤ s →∀ t∈Ioo a b,
      let p := NativeWindowDistributedAdjoint.response seed M observation test a b ordered
      let v := NativeCenteredResponseTensor.centered seed M frame s
      let q := p t
      let Fc := NativeCenteredResponseRate.forcing seed M frame s
      let g := NativeWindowDistributedAdjoint.load (nu := nu) observation M test t
      HasDerivAt (fun h => ‖pair M (NativeCenteredResponseTensor.centered seed M frame (s+h)) (p (t-h))‖^2)
        (-2*nu.coeff*(curlPair (modes M) v.1 v.1*‖coefficients (modes M) q‖^2+
          ‖coefficients (modes M) v‖^2*curlPair (modes M) q.1 q.1)+
          2*inner ℝ (pair M v q) (pair M Fc q+pair M v g)) 0 := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,
    NativeWindowTraceAdjoint.source_action_ae seed M] with s actual action positive t inside
  have du := (NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt s actual
  change HasDerivAt (NativeWindowTraceAdjoint.value seed M) _ s at du
  rw [action positive,NativeCenteredResponseTensor.centered_action_split seed M frame s] at du
  have dv := du.sub_const (NativeWindowHistoryMeanAction.meanValue seed M frame)
  have dp := (NativeWindowDistributedAdjoint.response_derivative seed M observation test a b ordered t
    (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  exact pair_directional_energy seed M s t dv dp

end
end SaturationMonoid.NavierStokes.NativeResponseJointControl
