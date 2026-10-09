import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCanonicalPacketDensity

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedPacketGreen
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace Stage9C.Material.SpinPair
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb UnifiedAction.AtomicScales
open MeasureTheory Set Filter
open scoped Topology

private theorem sourceDistance_norm (x : Point) : distance x=‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [distance,Real.norm_eq_abs,sq_abs]

/-- The field solution is read with the same original canonical charge at the second material leg. -/
def sourcePacketPotentialEnergy (x : Point) : ℝ := (4*spinScale)*sourcePacketGaussPotential x

theorem sourcePacketPotentialEnergy_green (x : Point) :
    sourcePacketPotentialEnergy x=(4*spinScale)^2*(∫y : Point,sourcePacketDensity y*Stage10.StaticGreen.green (x-y)) := by
  unfold sourcePacketPotentialEnergy sourcePacketGaussPotential Stage10.StaticGreen.potential
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

/-- The original Green fundamental equation pays the complete coefficient, including its spatial 4π normalization. -/
theorem sourcePacketPotentialEnergy_kernel (x : Point) :
    sourcePacketPotentialEnergy x=canonicalCoulomb*(∫y : Point,sourcePacketDensity y*kernel (x-y)) := by
  rw [sourcePacketPotentialEnergy_green,original_coulomb_coefficient]
  simp_rw [Stage10.StaticGreen.green_kernel,←mul_div_assoc]
  rw [integral_div]
  ring

private theorem kernel_tail (x y : Point) (outside : 1<distance x) (inside : ‖WithLp.toLp 2 y‖<1) :
    |kernel (x-y)-kernel x|≤1/(distance x*(distance x-1)) := by
  let X : FullSpace.Position:=WithLp.toLp 2 x
  let Y : FullSpace.Position:=WithLp.toLp 2 y
  have difference : WithLp.toLp 2 (x-y)=X-Y := rfl
  have outsideNorm : 1<‖X‖ := by simpa only [sourceDistance_norm] using outside
  have positive : 0<‖X‖ := by change 0<‖WithLp.toLp 2 x‖; rw [←sourceDistance_norm]; linarith
  have lower : ‖X‖-1≤‖X-Y‖ := by
    have triangle:=norm_sub_norm_le X Y
    dsimp [Y] at *
    linarith
  have separation : 0<‖X-Y‖ := by
    linarith
  have differenceNorm : |‖X‖-‖X-Y‖|≤1 := by
    have h:=abs_norm_sub_norm_le X (X-Y)
    rw [sub_sub_cancel] at h
    exact h.trans inside.le
  simp only [kernel,sourceDistance_norm,difference]
  change |‖X-Y‖⁻¹-‖X‖⁻¹|≤1/(‖X‖*(‖X‖-1))
  rw [inv_sub_inv separation.ne' positive.ne',abs_div,abs_of_pos (mul_pos separation positive)]
  apply (div_le_div_of_nonneg_right differenceNorm (mul_nonneg separation.le positive.le)).trans
  apply one_div_le_one_div_of_le
  · exact mul_pos positive (by linarith)
  · nlinarith

/-- Finite support is inherited from the actual preparation, so this error uses no selected cutoff scale. -/
theorem sourcePacketKernel_tail (x : Point) (outside : 1<distance x) :
    |(∫y : Point,sourcePacketDensity y*kernel (x-y))-kernel x|≤1/(distance x*(distance x-1)) := by
  have convolution:=integrable_mul_shifted_kernel sourcePacketDensity sourcePacketDensity_integrable
    (HistoryPrepared.packetScale⁻¹^2) sourcePacketDensity_bounded x
  have flipped : Integrable (fun y : Point=>sourcePacketDensity y*kernel (x-y)) := by
    convert convolution using 1
    funext y
    simp only [kernel,distance,Pi.sub_apply]
    congr 3
    apply Finset.sum_congr rfl
    intro j _
    ring
  have subintegrable:=flipped.sub (sourcePacketDensity_integrable.mul_const (kernel x))
  have weighted : (∫y : Point,sourcePacketDensity y*(kernel (x-y)-kernel x))=
      (∫y : Point,sourcePacketDensity y*kernel (x-y))-kernel x := by
    simp_rw [mul_sub]
    rw [integral_sub flipped (sourcePacketDensity_integrable.mul_const (kernel x)),integral_mul_const,sourcePacketDensity_mass,one_mul]
  rw [←weighted]
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have estimate : ∀y : Point,‖sourcePacketDensity y*(kernel (x-y)-kernel x)‖≤
      sourcePacketDensity y*(1/(distance x*(distance x-1))) := by
    intro y
    by_cases inside : ‖WithLp.toLp 2 y‖<1
    · rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sourcePacketDensity_nonnegative y),Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (kernel_tail x y outside inside) (sourcePacketDensity_nonnegative y)
    · rw [sourcePacketDensity_support y (le_of_not_gt inside),zero_mul,norm_zero,zero_mul]
  have price:=sourcePacketDensity_integrable.mul_const (1/(distance x*(distance x-1)))
  have absolute : Integrable (fun y : Point=>‖sourcePacketDensity y*(kernel (x-y)-kernel x)‖) := by
    convert subintegrable.norm using 1
    funext y
    simp only [mul_sub,Pi.sub_apply]
  have bound:=integral_mono absolute price estimate
  simpa only [integral_mul_const,sourcePacketDensity_mass,one_mul] using bound

theorem sourcePacketPotentialEnergy_tail (x : Point) (outside : 1<distance x) :
    |sourcePacketPotentialEnergy x-canonicalCoulomb*kernel x|≤canonicalCoulomb/(distance x*(distance x-1)) := by
  have positive : 0<canonicalCoulomb := by
    rw [original_coulomb_coefficient]
    exact div_pos (sq_pos_of_pos (mul_pos (by norm_num) spinScale_pos))
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) lapse_pos)
  rw [sourcePacketPotentialEnergy_kernel,←mul_sub,abs_mul,abs_of_pos positive]
  exact (mul_le_mul_of_nonneg_left (sourcePacketKernel_tail x outside)
    positive.le).trans_eq (by ring)

end LowEnergy.PreparationVacuumChargedPacketGreen
