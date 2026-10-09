import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceRetardedBandCurrent
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeSourceLeg
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualCutoffFrequencyBase
open GaussCoreHilbert GaussUnitaryHistory FullYSourceResolventGraphSplice
open SourceResolventBandLimit MeasureTheory Filter
open scoped Topology
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H
attribute [local irreducible] finiteResolvent

def frequency (advanced : Bool) (μ w : ℝ) : ℂ := line (if advanced then -μ else μ) w

theorem frequency_im (advanced : Bool) (μ w : ℝ) :
    (frequency advanced μ w).im = if advanced then -μ else μ := line_im _ _

theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (frequency advanced μ w).im ≠ 0 := by
  rw [frequency_im]
  cases advanced <;> simpa using hμ.ne'

theorem frequency_abs_im (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    |(frequency advanced μ w).im| = μ := by
  rw [frequency_im]
  cases advanced <;> simp only [Bool.false_eq_true,ite_false,ite_true,abs_neg,abs_of_pos hμ]

private theorem resolvent_adjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) :
    FullYSourceResolventGraphSplice.resolvent C (star z) =
      (FullYSourceResolventGraphSplice.resolvent C z).adjoint := by
  unfold FullYSourceResolventGraphSplice.resolvent
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,hC.star_eq]

private theorem finite_star (F : Index) (z : ℂ) :
    finiteResolvent F (star z) = (finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  exact resolvent_adjoint _ (GaussGradedCompression.compression_selfAdjoint F) z

private theorem frequency_true (μ w : ℝ) : frequency true μ w = star (line μ w) := by
  simp only [frequency,ite_true,line,map_add,map_mul,Complex.star_def,Complex.conj_ofReal,
    Complex.conj_I,Complex.ofReal_neg]
  ring

theorem actual_frequency_resolvent_continuous (F : Index) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) : Continuous (fun w : ℝ => finiteResolvent F (frequency advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have ha : Continuous (fun w : ℝ => (finiteResolvent F (line μ w)).adjoint) :=
      ContinuousLinearMap.adjoint.continuous.comp
        (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F)
    exact ha.congr (fun w => (finite_star F (line μ w)).symm.trans
      (congrArg (finiteResolvent F) (frequency_true μ w).symm))

private theorem base_norm (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) (w : ℝ) :
    ‖finiteResolvent F (frequency advanced μ w) g‖ = ‖finiteResolvent F (line μ w) g‖ := by
  cases advanced
  · rfl
  · rw [frequency_true]
    exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
      (by simpa only [line_im] using hμ.ne') g

theorem actual_base_square_integrable (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) :
    Integrable (fun w : ℝ => ‖finiteResolvent F (frequency advanced μ w) g‖^2) := by
  simp_rw [base_norm F advanced μ hμ g]
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using
    SourceActualResolventEnergy.actual_square_integrable F μ hμ g

theorem actual_base_square_integral (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) :
    (∫w : ℝ,‖finiteResolvent F (frequency advanced μ w) g‖^2) = Real.pi/μ*‖g‖^2 := by
  simp_rw [base_norm F advanced μ hμ g]
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using
    SourceActualResolventEnergy.actual_square_integral F μ hμ g

theorem actual_base_memLp (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) :
    MemLp (fun w : ℝ => finiteResolvent F (frequency advanced μ w) g) 2 (volume : Measure ℝ) :=
  (memLp_two_iff_integrable_sq_norm
    (((actual_frequency_resolvent_continuous F advanced μ hμ).clm_apply continuous_const).aestronglyMeasurable)).mpr
      (actual_base_square_integrable F advanced μ hμ g)

def finiteBase (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) : Lp H 2 (volume : Measure ℝ) :=
  (actual_base_memLp F advanced μ hμ g).toLp (fun w => finiteResolvent F (frequency advanced μ w) g)

theorem actual_finite_base_read (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) :
    (fun w : ℝ => finiteBase F advanced μ hμ g w) =ᵐ[volume]
      (fun w => finiteResolvent F (frequency advanced μ w) g) :=
  (actual_base_memLp F advanced μ hμ g).coeFn_toLp

theorem actual_finite_base_square (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) :
    ‖finiteBase F advanced μ hμ g‖^2 = Real.pi/μ*‖g‖^2 := by
  rw [FullYSourceCutoffTimeGraph.square_integral]
  calc
    _ = ∫w : ℝ,‖finiteResolvent F (frequency advanced μ w) g‖^2 := by
      apply integral_congr_ae
      filter_upwards [actual_finite_base_read F advanced μ hμ g] with w hw
      rw [hw]
    _ = _ := actual_base_square_integral F advanced μ hμ g

theorem actual_finite_base_bound (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : H) :
    ‖finiteBase F advanced μ hμ g‖ ≤ Real.sqrt (Real.pi/μ*‖g‖^2) := by
  have he := actual_finite_base_square F advanced μ hμ g
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi/μ*‖g‖^2 by positivity)
  nlinarith [norm_nonneg (finiteBase F advanced μ hμ g),Real.sqrt_nonneg (Real.pi/μ*‖g‖^2)]

end LowEnergy.ActualCutoffFrequencyBase
