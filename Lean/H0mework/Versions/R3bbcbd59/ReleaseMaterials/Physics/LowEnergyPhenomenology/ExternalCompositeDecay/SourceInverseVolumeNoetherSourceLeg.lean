import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNoetherEnergy
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeFixedEnergyTail
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeSourceLeg

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseNoetherSourceLeg
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourcePhysicalKineticSquare
open SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy SourceScalarInverseRetardedBudget
open SourceScalarInverseEnergyExchange SourceInverseNoetherEnergy SourceInverseFixedEnergyTail
open SourceInverseSourceLeg SourceMixedNativeReturn SourceGammaNativeBudget SourceMovingJetFlux
open SourceQuantumScalarChart FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceRelativePowerTail SourceRetardedForcingTail SourceRetardedBandCurrent
open MeasureTheory Filter
open scoped ENNReal
attribute [local irreducible] diagonalAction state inverseForm sourceGamma primitive
  raisedNoetherCurrent coefficientCost

/-- The Noether upper retains the actual exterior resolvent state, including its escape component. -/
theorem actual_gamma_source_leg_noether_upper (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    z.im^2*(4*sourceTime 0*‖sourceGamma sharp m ell F g k z+Complex.I*inner ℂ (k : H)
      ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))‖^2) ≤
      ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖finiteResolvent F (star z) (k : H)‖^2*coefficientCost sharp*
        (inverseForm (theta m ell (coreEquiv.symm g))+
          2*z.im*raisedNoetherCurrent F (theta m ell) (state F z hz g)+
          z.im^2*(2*sourceTime 0*‖vacuum‖^2*‖embed (theta m ell (state F z hz g))‖^2)) := by
  have hg := actual_gamma_source_leg_bound sharp m ell F z hz g k
  rw [original_diagonal_energy_exchange] at hg
  have hn := actual_raised_energy_upper F z hz g (theta m ell)
  have hc : 0≤coefficientCost sharp := by
    unfold coefficientCost
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : 0≤‖-96*(sourceTime 0 : ℂ)^2‖^2*
      ‖finiteResolvent F (star z) (k : H)‖^2*coefficientCost sharp := by positivity
  have hs := mul_le_mul_of_nonneg_left hg (sq_nonneg z.im)
  have he := mul_le_mul_of_nonneg_left hn hp
  nlinarith only [hs,he]

/-- The fixed-input energy is integrated against the original exterior source leg over the full real line. -/
theorem actual_fixed_input_leg_energy (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (k : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (star (line μ w)) k‖^2*
      inverseForm (theta m ell (coreEquiv.symm g))))=
      ENNReal.ofReal (((Real.pi/μ)*‖k‖^2)*inverseForm (theta m ell (coreEquiv.symm g))) := by
  simp_rw [actual_conjugate_leg_norm F (line μ _) (by simpa only [line_im] using hμ.ne')]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hl : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) k‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖k‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ k
  rw [hl,←ENNReal.ofReal_mul (by positivity : 0≤(Real.pi/μ)*‖k‖^2)]

/-- The original fixed-source cutoff energy now has the full-frequency exterior-leg tail, uniformly in F. -/
theorem actual_fixed_input_leg_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (k : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (star (line μ w)) k‖^2*
        inverseForm (theta m ell (coreEquiv.symm g))))≤ENNReal.ofReal ε := by
  intro ε hε
  let C := (Real.pi/μ)*‖k‖^2
  have hC : 0≤C := by dsimp [C];positivity
  let δ := ε/(C+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N,hN⟩ := original_fixed_energy_tail (coreEquiv.symm g) δ hδ
  refine ⟨N,fun m hm ell hell F => ?_⟩
  rw [actual_fixed_input_leg_energy m ell F μ hμ g k]
  apply ENNReal.ofReal_le_ofReal
  have he := mul_le_mul_of_nonneg_left (hN m hm ell hell) hC
  have hd : δ*(C+1)=ε := div_mul_cancel₀ ε (by positivity)
  change C*inverseForm (theta m ell (coreEquiv.symm g))≤ε
  nlinarith

private theorem theta_state (m ell : ℕ) (F : Index) (μ w : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    embed (theta m ell (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))=
      relativeTail m ell (finiteResolvent F (line μ w) (g : H)) := by
  change embed (SourceNativeCutoffContact.thetaAction m ell
    (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))=_
  rw [SourceNativeCutoffContact.theta_core]
  congr 1
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The remaining vacuum lower-order term is paid by the existing actual theta tail and genuine exterior leg. -/
theorem actual_vacuum_leg_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (k : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (star (line μ w)) k‖^2*
        (2*sourceTime 0*‖vacuum‖^2*
          ‖embed (theta m ell (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)))
        ≤ENNReal.ofReal ε := by
  intro ε hε
  let C := (μ⁻¹*‖k‖)^2*(2*sourceTime 0*‖vacuum‖^2)
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hC : 0≤C := by dsimp [C];positivity
  let δ := ε/(C+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N,hN⟩ := actual_theta_full_frequency_tail μ hμ g δ hδ
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have hb (w : ℝ) : ‖finiteResolvent F (star (line μ w)) k‖^2≤(μ⁻¹*‖k‖)^2 := by
    rw [actual_conjugate_leg_norm F (line μ w) (by simpa only [line_im] using hμ.ne')]
    exact pow_le_pow_left₀ (norm_nonneg _) (finite_input_bound μ hμ F k w) 2
  calc
    _≤∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal
        (‖relativeTail m ell (finiteResolvent F (line μ w) (g : H))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [theta_state m ell F μ w hμ g,←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hs := mul_le_mul_of_nonneg_right (hb w)
        (by positivity : 0≤2*sourceTime 0*‖vacuum‖^2*
          ‖relativeTail m ell (finiteResolvent F (line μ w) (g : H))‖^2)
      exact hs.trans_eq (by dsimp [C];ring)
    _=ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal
        (‖relativeTail m ell (finiteResolvent F (line μ w) (g : H))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤ENNReal.ofReal C*ENNReal.ofReal δ := mul_le_mul' (le_refl _) hF
    _≤ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hd : δ*(C+1)=ε := div_mul_cancel₀ ε (by positivity)
      nlinarith

end LowEnergy.SourceInverseNoetherSourceLeg
