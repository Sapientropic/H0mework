import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCoframeVolume

/-! The six original coframe kinetic columns generate the volume current. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceCoframeVolumeCurrent
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussNativeForm GaussCoframeCore SourceCoframeVolume
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Topology InnerProductSpace
abbrev CoreEnd := QuantumTest →ₗ[ℂ] QuantumTest

def coordinateAction (i : Fin 6) : CoreEnd := multiply (fun z => z.1 i) (by intro z; fun_prop)
def coefficientAction (i j : Fin 6) : CoreEnd :=
  multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)

theorem scalar_volume_commutes
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) :
    Commute (localMultiplier A smooth) volumeAction := by
  change (localMultiplier A smooth)*volumeAction=volumeAction*(localMultiplier A smooth)
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (volume z : ℂ) (f z)

theorem source_gradient_contraction (i : Fin 6) :
    (∑ j : Fin 6, coefficientAction i j * gradientAction j) =
      ((sourceTime 0/4 : ℝ) : ℂ) • coordinateAction i := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (∑ j : Fin 6, (GaussCoframeKinetic.coefficient i j z : ℂ) *
      ((volumeGradient z j : ℂ)*f z word)) =
    ((sourceTime 0/4 : ℝ) : ℂ) * ((z.1 i : ℂ)*f z word)
  by_cases hz : z ∈ physicalChart
  · have h := coefficient_volume ⟨z,hz⟩ i
    simp_rw [←mul_assoc]
    rw [←Finset.sum_mul]
    have hc : (∑ j : Fin 6, (GaussCoframeKinetic.coefficient i j z : ℂ) *
        (volumeGradient z j : ℂ)) = ((sourceTime 0/4*z.1 i : ℝ) : ℂ) := by
      exact_mod_cast h
    rw [hc]
    push_cast
    ring
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp [hf]

private theorem real_multipliers_commute (a b : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (hb : ∀ z : physicalChart, ContDiffAt ℝ ∞ b z.val) :
    Commute (multiply a ha) (multiply b hb) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (a z : ℂ) (b z : ℂ) (f z)

private theorem coefficient_symmetry (i j : Fin 6) : coefficientAction i j=coefficientAction j i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (GaussCoframeKinetic.coefficient i j z : ℂ) • f z =
    (GaussCoframeKinetic.coefficient j i z : ℂ) • f z
  rw [GaussCoframeKinetic.coefficient_symmetric i j z]

private theorem source_gradient_left (j : Fin 6) :
    (∑ i : Fin 6, gradientAction i * coefficientAction i j) =
      ((sourceTime 0/4 : ℝ) : ℂ) • coordinateAction j := by
  have he (i : Fin 6) : gradientAction i*coefficientAction i j=
      coefficientAction j i*gradientAction i := by
    have hc : Commute (gradientAction i) (coefficientAction i j) :=
      real_multipliers_commute _ _ _ _
    exact hc.eq.trans (congrArg (fun A => A*gradientAction i) (coefficient_symmetry i j))
  simp_rw [he]
  exact source_gradient_contraction j

private theorem term_law {R : Type*} [Ring R] (A C B U K L : R)
    (hA : A*U=U*A+K) (hB : B*U=U*B+L) (hC : C*U=U*C) :
    (A*(C*B))*U-U*(A*(C*B))=A*(C*L)+K*(C*B) := by
  calc
    _ = A*(C*(B*U))-U*(A*(C*B)) := by simp only [mul_assoc]
    _ = A*(C*(U*B+L))-U*(A*(C*B)) := by rw [hB]
    _ = A*((C*U)*B)+A*(C*L)-U*(A*(C*B)) := by noncomm_ring
    _ = (A*U)*(C*B)+A*(C*L)-U*(A*(C*B)) := by rw [hC]; noncomm_ring
    _ = _ := by rw [hA]; noncomm_ring

private theorem source_term (i j : Fin 6) :
    GaussCoframeKinetic.term i j*volumeAction-volumeAction*GaussCoframeKinetic.term i j =
      (-Complex.I) • (GaussCoframeCore.adjoint i*(coefficientAction i j*gradientAction j)+
        gradientAction i*(coefficientAction i j*GaussCoframeCore.momentum j)) := by
  have hC : Commute (coefficientAction i j) volumeAction :=
    real_multipliers_commute _ _ (GaussCoframeKinetic.coefficient_smooth i j)
      (fun _ => volume_smooth.contDiffAt)
  have h := term_law (GaussCoframeCore.adjoint i) (coefficientAction i j)
    (GaussCoframeCore.momentum j) volumeAction ((-Complex.I) • gradientAction i)
    ((-Complex.I) • gradientAction j) (LinearMap.ext (adjoint_volume i))
    (LinearMap.ext (momentum_volume j)) hC.eq
  simpa only [mul_smul_comm, smul_mul_assoc, smul_add] using! h

def dilation : CoreEnd := (1/3 : ℂ) • (∑ i : Fin 6,
  (GaussCoframeCore.adjoint i*coordinateAction i+coordinateAction i*GaussCoframeCore.momentum i))

theorem coframe_volume_current :
    GaussCoframeKinetic.kinetic*volumeAction-volumeAction*GaussCoframeKinetic.kinetic =
      (-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation := by
  have hright : (∑ i : Fin 6, ∑ j : Fin 6,
      GaussCoframeCore.adjoint i*(coefficientAction i j*gradientAction j)) =
      ((sourceTime 0/4 : ℝ) : ℂ) • ∑ i : Fin 6, GaussCoframeCore.adjoint i*coordinateAction i := by
    simp only [←Finset.mul_sum, source_gradient_contraction, mul_smul_comm, Finset.smul_sum]
  have hleft : (∑ i : Fin 6, ∑ j : Fin 6,
      gradientAction i*(coefficientAction i j*GaussCoframeCore.momentum j)) =
      ((sourceTime 0/4 : ℝ) : ℂ) • ∑ j : Fin 6, coordinateAction j*GaussCoframeCore.momentum j := by
    rw [Finset.sum_comm]
    simp only [←mul_assoc, ←Finset.sum_mul, source_gradient_left, smul_mul_assoc, Finset.smul_sum]
  unfold GaussCoframeKinetic.kinetic
  simp only [Finset.sum_mul, Finset.mul_sum, ←Finset.sum_sub_distrib, source_term,
    ←Finset.smul_sum, Finset.sum_add_distrib]
  rw [hright, hleft]
  unfold dilation
  rw [←smul_add, smul_smul, Finset.sum_add_distrib, smul_smul]
  congr 1
  push_cast
  ring

end LowEnergy.SourceCoframeVolumeCurrent
