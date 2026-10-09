import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceBulkTwoTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceBulkTimeFlow
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory
open SourceBulkTwoTime SourceInverseNoetherChannelGap SourceInverseNoetherEnergy SourceInverseChannelSourceJets
open SourceJointResidualEnergy FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem phase_derivative (a t : ℝ) :
    HasDerivAt (phase a) ((-Complex.I)*(a : ℂ)*phase a t) t := by
  have h := (((hasDerivAt_id t).ofReal_comp).const_mul ((-Complex.I)*(a : ℂ))).cexp
  unfold phase
  simpa only [id_eq,Complex.ofReal_one,mul_one,mul_comm] using! h

private theorem left_expansion (F : Index) (T : End) (k g : diagonal.domain) (t s : ℝ) :
    kernel F T k g t s=∑ i : Channel F,star (phase (channelValue F i) t)*
      sourcePair (T (channelTest F k i)) (bulkAction (T (coreTime F g s))) := by
  rw [kernel,coreTime]
  simp only [map_sum,map_smul,sourcePair,sum_inner,inner_smul_left,starRingEnd_apply,phase]

private theorem pair_sum {ι : Type*} [Fintype ι] (f : ι → QuantumTest) (c : ι → ℂ) :
    sourcePair (∑ i,c i • f i) (bulkAction (∑ j,c j • f j))=
      ∑ i,∑ j,star (c i)*c j*sourcePair (f i) (bulkAction (f j)) := by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pair_real (a : ℝ) (u v : QuantumTest) :
    sourcePair ((a : ℂ) • u) v=(a : ℂ)*sourcePair u v := by
  simp only [sourcePair,map_smul,inner_smul_left,Complex.conj_ofReal]

attribute [local irreducible] kernel coreTime sourcePair bulkAction inverseForm

/-- The original unbounded bulk generates a positive time kernel with all coherent cross terms. -/
theorem actual_kernel_positive {ι : Type*} [Fintype ι] (F : Index) (T : End) (g : diagonal.domain)
    (t : ι → ℝ) (c : ι → ℂ) :
    0≤(∑ i,∑ j,star (c i)*c j*kernel F T g g (t i) (t j)).re ∧
      (∑ i,∑ j,star (c i)*c j*kernel F T g g (t i) (t j)).im=0 := by
  let q := ∑ i,c i • T (coreTime F g (t i))
  have h : (∑ i,∑ j,star (c i)*c j*kernel F T g g (t i) (t j))=sourcePair q (bulkAction q) := by
    simpa only [kernel] using! (pair_sum (fun i => T (coreTime F g (t i))) c).symm
  have hr := (congrArg Complex.re h).trans (original_bulk_energy q)
  have hi := (congrArg Complex.im h).trans (original_bulk_real q)
  exact ⟨hr.symm ▸ original_inverse_nonnegative q,hi⟩

/-- One fixed-source prefix generates the complete time derivative, before all cutoffs and times. -/
theorem actual_left_time_derivative (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (T : End) (t s : ℝ),
      HasDerivAt (fun u => kernel F T k g u s)
        (Complex.I*kernel F T (iterate 1 k) g t s) t := by
  filter_upwards [actual_channel_source_jet 1 k] with F hF T t s
  simp only [pow_one] at hF
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((phase_derivative (SourceJointResidualEnergy.channelValue F i) t).star).mul_const
      (sourcePair (T (channelTest F k i)) (bulkAction (T (coreTime F g s)))))
  have he : (fun u => kernel F T k g u s)=(fun u => ∑ i : SourceJointResidualEnergy.Channel F,
      star (phase (SourceJointResidualEnergy.channelValue F i) u)*
        sourcePair (T (channelTest F k i)) (bulkAction (T (coreTime F g s)))) := by
    funext u
    exact left_expansion F T k g u s
  rw [he]
  convert! h using 1
  rw [left_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hF i,map_smul]
  rw [pair_real]
  simp only [star_mul,star_neg,Complex.star_def,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  ring

def flowLaplace (F : Index) (T : End) (g : diagonal.domain) (z : ℂ) : ℂ :=
  ∫ s : ℝ in Set.Ioi 0,∫ t : ℝ in Set.Ioi 0,
    star (Complex.exp (Complex.I*z*(t : ℂ)))*Complex.exp (Complex.I*z*(s : ℂ))*
      deriv (fun u => kernel F T g g u s) t

/-- The signed original current is the real Laplace readout of the positive bulk kernel's time derivative. -/
theorem actual_current_flow (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (μ : ℝ) (hμ : 0<μ) (k : diagonal.domain) (T : End),
      SourceInverseGapWardFirstJet.fixedSourceCurrent F μ hμ g k T=
        ∫ w : ℝ,‖finiteResolvent F (star (line μ w)) (k : H)‖^2*(flowLaplace F T g (line μ w)).re := by
  filter_upwards [actual_left_time_derivative g g] with F hF μ hμ k T
  have hd (t s : ℝ) : deriv (fun u => kernel F T g g u s) t=
      Complex.I*kernel F T (iterate 1 g) g t s := (hF T t s).deriv
  have hi (z : ℂ) : flowLaplace F T g z=Complex.I*laplaceKernel F T (iterate 1 g) g z z := by
    unfold flowLaplace
    simp_rw [hd]
    calc
      _ = ∫ s : ℝ in Set.Ioi 0,∫ t : ℝ in Set.Ioi 0,
          Complex.I*weightedKernel F T (iterate 1 g) g z z t s := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun s => integral_congr_ae (Eventually.of_forall (fun t => by
          unfold weightedKernel
          ring)))
      _ = _ := by simp only [integral_const_mul,laplaceKernel]
  rw [actual_fixed_source_time_current F μ hμ]
  unfold timeCurrent
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => by
    dsimp only
    rw [hi]
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,Complex.neg_im])

end LowEnergy.SourceBulkTimeFlow
