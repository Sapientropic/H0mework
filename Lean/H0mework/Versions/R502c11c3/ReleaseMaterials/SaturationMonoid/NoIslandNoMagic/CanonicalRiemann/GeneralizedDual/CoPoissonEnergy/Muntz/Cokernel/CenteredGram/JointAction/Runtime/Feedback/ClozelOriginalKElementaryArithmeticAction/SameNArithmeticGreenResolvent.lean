import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SameNArithmeticGreen
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DilationWard
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSameNArithmeticGreen
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "b" => burnolRieszSingleFourierSource
local notation "C" => ConstantDual.seed
local notation "D" => burnolMultiplicativeDilation
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
open private sourceFunctional
  from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SameNArithmeticGreen

private theorem sourceFunctional_read (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    sourceFunctional c value=(c.value-1)*inner ℂ (E (b c:Hq)) value+
      star (Kernel.A c)*inner ℂ Response.wholeU value-star (Kernel.beta c)*inner ℂ Response.wholeV value := by
  change inner ℂ (E (Euler.sourceEuler c:Hq)) value-(1/2:ℂ)*inner ℂ (E (b c:Hq)) value=_
  rw [Euler.sourceEuler_eq]
  simp only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul,
    inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply,star_div₀,star_ofNat,star_one,star_star]
  change ((c.value-(1/2:ℂ))*inner ℂ (E (b c:Hq)) value+
    star (Kernel.A c)*inner ℂ Response.wholeU value-star (Kernel.beta c)*inner ℂ Response.wholeV value)-
    (1/2:ℂ)*inner ℂ (E (b c:Hq)) value=_
  ring

private theorem channel_dilation (h a:ℝ) (positive:0<a) (value:BurnolL2) :
    D h (ContinuousChannels.channel 1 a value)=
      (Real.exp (h/2):ℂ) • ContinuousChannels.channel 1 (a*Real.exp h) value := by
  have root:Real.sqrt (Real.exp h)=Real.exp (h/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos h),Real.log_exp]
    congr 1
    ring
  simp only [ContinuousChannels.channel,one_mul,map_smul,burnolMultiplicativeDilation_add,
    Real.log_mul positive.ne' (Real.exp_ne_zero h),Real.log_exp,Real.sqrt_mul positive.le,root,Complex.ofReal_mul]
  rw [add_comm h (Real.log a),smul_smul]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr positive),
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (h/2))]

def shiftedContactProgramme (c:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) : ℂ :=
  (Real.exp (h/2):ℂ)*((∑n∈Finset.Ico 1 N,contact c ((n:ℝ)*Real.exp h))-
    ∫a:ℝ in Ioc 0 (N:ℝ),contact c (a*Real.exp h))

theorem actual_same_N_shifted_unit_green (c:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) :
    sourceFunctional c (D h (DualSource.source N C))=shiftedContactProgramme c h N := by
  let action:BurnolL2→L[ℂ]ℂ:=(sourceFunctional c).comp (D h).toContinuousLinearEquiv.toContinuousLinearMap
  have channel (a:ℝ) (positive:0<a):
      action (ContinuousChannels.channel 1 a C)=(Real.exp (h/2):ℂ)*contact c (a*Real.exp h) := by
    change sourceFunctional c (D h (ContinuousChannels.channel 1 a C))=_
    rw [channel_dilation h a positive,map_smul,actual_unit_channel_green c _ (mul_pos positive (Real.exp_pos h))]
    rfl
  change action (DualSource.source N C)=_
  rw [DualSource.source,map_sub,map_sum,←action.integral_comp_comm (ContinuousChannels.channel_integrable 1 N C)]
  have sum:(∑n∈Finset.Ico 1 N,action (ContinuousChannels.channel 1 n C))=
      ∑n∈Finset.Ico 1 N,(Real.exp (h/2):ℂ)*contact c ((n:ℝ)*Real.exp h) :=
    Finset.sum_congr rfl (fun n inside=>channel n (by exact_mod_cast (Finset.mem_Ico.mp inside).1))
  have integral:(fun a:ℝ=>action (ContinuousChannels.channel 1 a C))=ᵐ[volume.restrict (Ioc 0 (N:ℝ))]
      fun a=>(Real.exp (h/2):ℂ)*contact c (a*Real.exp h) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    exact channel a inside.1
  rw [sum,integral_congr_ae integral,←Finset.mul_sum,integral_const_mul]
  unfold shiftedContactProgramme
  ring

theorem actual_same_N_shifted_B_unit_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) :
    (c.value-1)*inner ℂ (E (b c:Hq)) (D h (DualSource.source N C))+
      star (Kernel.A c)*inner ℂ Response.wholeU (D h (DualSource.source N C))-
      star (Kernel.beta c)*inner ℂ Response.wholeV (D h (DualSource.source N C))=shiftedContactProgramme c h N := by
  rw [←sourceFunctional_read]
  exact actual_same_N_shifted_unit_green c h N

private theorem constant_euler :
    GapEuler.euler (C:TemperedDistribution ℝ ℂ)=
      -GapEuler.edge q-(1/2:ℂ) • (C:TemperedDistribution ℝ ℂ) := by
  ext test
  have source:=ConstantDual.seed_edge test
  rw [ConstantDual.edgeRead_apply] at source
  simp only [sub_apply,neg_apply,smul_apply,smul_eq_mul]
  linear_combination -source

/-- Removing precisely the original beta jump gives the actual L2 Euler field. -/
private theorem corrected_B_euler (c:BurnolCompletedMellinCoordinate) :
    GapEuler.euler ((E (b c:Hq)-Kernel.beta c • C:BurnolL2):TemperedDistribution ℝ ℂ)=
      ((E (Euler.sourceEuler c:Hq)+(Kernel.beta c/2) • C:BurnolL2):TemperedDistribution ℝ ℂ) := by
  have source:=Euler.source_euler c
  change GapEuler.euler (E (b c:Hq):TemperedDistribution ℝ ℂ)=
    (E (Euler.sourceEuler c:Hq):TemperedDistribution ℝ ℂ)-Kernel.beta c • GapEuler.edge q at source
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 _)=
    Lp.toTemperedDistributionCLM ℂ volume 2 _
  simp only [map_sub,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
  rw [source,constant_euler]
  module

/-- True source Euler and actual Rbar remove the B/Rbar-Y query in favor of its input and all units. -/
theorem actual_B_Rbar_green (c d:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    (c.value-star d.value)*inner ℂ (E (b c:Hq)) (OriginalKSourceResolventReconstruction.sourceResolvent d value)+
      star (Kernel.A c)*inner ℂ Response.wholeU (OriginalKSourceResolventReconstruction.sourceResolvent d value)-
      star (Kernel.beta c)*inner ℂ Response.wholeV (OriginalKSourceResolventReconstruction.sourceResolvent d value)=
      2*inner ℂ (E (b c:Hq)) value-2*star (Kernel.beta c)*inner ℂ C value-
        star d.value*star (Kernel.beta c)*inner ℂ C (OriginalKSourceResolventReconstruction.sourceResolvent d value) := by
  let R:=OriginalKSourceResolventReconstruction.sourceResolvent d value
  have inverse:=OriginalKSourceResolventReconstruction.sourceResolvent_euler d value
  have right:GapEuler.euler (R:TemperedDistribution ℝ ℂ)=
      ((-(2:ℂ) • value-OriginalKSourceResolventReconstruction.sourceRate d • R:BurnolL2):TemperedDistribution ℝ ℂ) := by
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 _
    simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
    exact eq_sub_of_add_eq inverse
  have actual:=DilationWard.cross_balance
    (E (b c:Hq)-Kernel.beta c • C) (E (Euler.sourceEuler c:Hq)+(Kernel.beta c/2) • C)
    R (-(2:ℂ) • value-OriginalKSourceResolventReconstruction.sourceRate d • R)
    (corrected_B_euler c) right
  rw [Euler.sourceEuler_eq] at actual
  simp only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul,
    inner_add_left,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    starRingEnd_apply,star_div₀,star_ofNat,star_one,star_star] at actual
  unfold OriginalKSourceResolventReconstruction.sourceRate at actual
  change (c.value-star d.value)*inner ℂ (E (b c:Hq)) R+
    star (Kernel.A c)*inner ℂ (E (Response.u:Hq)) R-star (Kernel.beta c)*inner ℂ (E (Response.v:Hq)) R=_
  linear_combination actual

def reverseContactProgramme (c d:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) : ℂ :=
  let value:=D h (DualSource.source N C)
  let acted:=OriginalKSourceResolventReconstruction.sourceResolvent d value
  (star d.value*GapEuler.gapMean q d)*
    (shiftedContactProgramme c h N-star (Kernel.A c)*inner ℂ Response.wholeU value+
      star (Kernel.beta c)*inner ℂ Response.wholeV value+
      ((1-star d.value)/2)*
        (star (Kernel.A c)*inner ℂ Response.wholeU acted-
          star (Kernel.beta c)*inner ℂ Response.wholeV acted+
          2*star (Kernel.beta c)*inner ℂ C value+
          star d.value*star (Kernel.beta c)*inner ℂ C acted))

/-- The right source is the actual e_d programme; no eigenvalue, price, or noncollision is supplied. -/
theorem actual_same_N_reverse_B (c d:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) :
    (c.value-star d.value)*inner ℂ (E (b c:Hq))
      (D h (DualSource.source N (OriginalKCoefficientBFiniteAction.elementarySource d)))=
      reverseContactProgramme c d h N := by
  have arithmetic:=actual_same_N_shifted_B_unit_price c h N
  have resolvent:=actual_B_Rbar_green c d (D h (DualSource.source N C))
  have acted:D h (DualSource.source N (OriginalKCoefficientBFiniteAction.elementarySource d))=
      OriginalKElementaryArithmeticAction.unitResolventSource d (D h (DualSource.source N C)) := by
    rw [OriginalKElementaryArithmeticAction.unit_resolvent_finite,
      OriginalKElementaryArithmeticAction.unitResolventSource,map_smul,map_sub,map_smul]
    unfold OriginalKElementaryArithmeticAction.unitResolventSource
    congr 2
    congr 1
    change D h (burnolDirectRightResolvent (star d.value/2) _)=
      burnolDirectRightResolvent (star d.value/2) (D h _)
    rw [burnolDirectRightResolvent_dilation]
  rw [acted,OriginalKElementaryArithmeticAction.unitResolventSource,inner_smul_right,inner_sub_right,inner_smul_right]
  unfold reverseContactProgramme
  dsimp only
  linear_combination (star d.value*GapEuler.gapMean q d)*arithmetic-
    (star d.value*GapEuler.gapMean q d*((1-star d.value)/2))*resolvent

/-- The conjugate right source generates its resonant balance by actual substitution, without division. -/
theorem actual_same_N_conjugate_source_balance (c:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) :
    reverseContactProgramme c (barC c) h N=0 := by
  have source:=actual_same_N_reverse_B c (barC c) h N
  simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,sub_self,zero_mul] using source.symm

/-- The independent original z_d consumes the same finite source law and true dilation. -/
theorem actual_original_reverse_B_tendsto (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta d.value=0) (h:ℝ) :
    Tendsto (reverseContactProgramme c d h) atTop
      (𝓝 ((c.value-star d.value)*inner ℂ (E (b c:Hq))
        (D h (OriginalKElementaryArithmeticAction.elementaryReverseSource d zero)))) := by
  have update:=((D h).continuous.tendsto _).comp (OriginalKElementaryArithmeticAction.elementary_reverse_tendsto d zero)
  have source:=(tendsto_const_nhds (x:=E (b c:Hq))).inner (𝕜:=ℂ) update
  have actual:=source.const_mul (c.value-star d.value)
  apply actual.congr'
  filter_upwards [] with N
  exact actual_same_N_reverse_B c d h N

def boundaryContactProgramme (c d:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) : ℂ :=
  pairedMellinTranslationCharacter d.value h*reverseContactProgramme c d 0 N-
    (1/2:ℂ)*(reverseContactProgramme c d h N+reverseContactProgramme c d (-h) N)

/-- The exact original paired boundary word consumes both generated dilation actions at the same cutoff. -/
theorem actual_same_N_reverse_boundary_B (c d:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) :
    (c.value-star d.value)*inner ℂ (E (b c:Hq))
      (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction d h
        (DualSource.source N (OriginalKCoefficientBFiniteAction.elementarySource d)))=
      boundaryContactProgramme c d h N := by
  have base:=actual_same_N_reverse_B c d 0 N
  rw [burnolMultiplicativeDilation_zero] at base
  have plus:=actual_same_N_reverse_B c d h N
  have minus:=actual_same_N_reverse_B c d (-h) N
  unfold OriginalKFixedBoundarySourceFibre.finiteBoundaryAction boundaryContactProgramme
  simp only [inner_sub_right,inner_smul_right,inner_add_right]
  linear_combination pairedMellinTranslationCharacter d.value h*base-(1/2:ℂ)*(plus+minus)

/-- The fixed-h primitive of the complete source consumes the independently generated z_d. -/
theorem actual_original_reverse_boundary_B_tendsto (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta d.value=0) (h:ℝ) :
    Tendsto (boundaryContactProgramme c d h) atTop
      (𝓝 ((c.value-star d.value)*inner ℂ (E (b c:Hq))
        (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction d h
          (OriginalKElementaryArithmeticAction.elementaryReverseSource d zero)))) := by
  have base:=actual_original_reverse_B_tendsto c d zero 0
  rw [burnolMultiplicativeDilation_zero] at base
  have plus:=actual_original_reverse_B_tendsto c d zero h
  have minus:=actual_original_reverse_B_tendsto c d zero (-h)
  have actual:=(base.const_mul (pairedMellinTranslationCharacter d.value h)).sub
    ((plus.add minus).const_mul (1/2:ℂ))
  change Tendsto (boundaryContactProgramme c d h) atTop _ at actual
  convert! actual using 1
  unfold OriginalKFixedBoundarySourceFibre.finiteBoundaryAction
  simp only [inner_sub_right,inner_smul_right,inner_add_right]
  ring

theorem actual_same_N_conjugate_boundary_balance (c:BurnolCompletedMellinCoordinate) (h:ℝ) (N:ℕ) :
    boundaryContactProgramme c (barC c) h N=0 := by
  unfold boundaryContactProgramme
  rw [actual_same_N_conjugate_source_balance,actual_same_N_conjugate_source_balance,
    actual_same_N_conjugate_source_balance]
  ring

end OriginalSameNArithmeticGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
