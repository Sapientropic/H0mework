import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationConeSupport
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylKernel

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylDecay
open PreparationVacuumWeyl PreparationPhaseSource PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform

theorem b1_smooth : ContDiff ℝ ∞ b1 := by
  rw [contDiff_iff_contDiffAt]
  intro zp
  by_cases nonzero : zp.2≠0
  · by_cases position : zp.1∈thetaPositionClosed
    · by_cases direction : normalizedMomentum zp.2∈thetaDirectionClosed
      · exact b1_smooth_at zp (source_support_positiveCone zp.1 zp.2 position direction nonzero)
      · have nearby : ∀ᶠ q : FlatConfiguration × PhysicalMomentum in 𝓝 zp,
            normalizedMomentum q.2∉thetaDirectionClosed :=
          ((normalizedMomentum_smooth nonzero).continuousAt.comp continuousAt_snd).eventually
            (thetaDirectionClosed_closed.isOpen_compl.mem_nhds direction)
        have zero : b1 =ᶠ[𝓝 zp] (fun _ => (0 : ℝ)) := by
          filter_upwards [nearby] with q outside
          simp only [b1,factorWeight,sourceThetaRoot_split,directionRoot_zero_outside outside,
            mul_zero,zero_mul]
        exact contDiffAt_const.congr_of_eventuallyEq zero
    · have nearby : ∀ᶠ q : FlatConfiguration × PhysicalMomentum in 𝓝 zp,
          q.1∉thetaPositionClosed :=
        (thetaPositionClosed_closed.isOpen_compl.preimage continuous_fst).mem_nhds position
      have zero : b1 =ᶠ[𝓝 zp] (fun _ => (0 : ℝ)) := by
        filter_upwards [nearby] with q outside
        simp only [b1,factorWeight,sourceThetaRoot_split,positionRoot_zero_outside outside,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq zero
  · have momentumZero : zp.2=0 := not_not.mp nonzero
    have nearby : ∀ᶠ q : FlatConfiguration × PhysicalMomentum in 𝓝 zp, ‖q.2‖<1/2 :=
      (isOpen_lt continuous_snd.norm continuous_const).mem_nhds
        (by change ‖zp.2‖<1/2; rw [momentumZero]; norm_num)
    have zero : b1 =ᶠ[𝓝 zp] (fun _ => (0 : ℝ)) := by
      filter_upwards [nearby] with q low
      exact b1_zero_low q low.le
    exact contDiffAt_const.congr_of_eventuallyEq zero

def jointSymbol (xp : PhysicalMomentum × PhysicalMomentum) : ℂ := symbolSlice xp.2 xp.1

theorem jointSymbol_smooth : ContDiff ℝ ∞ jointSymbol :=
  Complex.ofRealCLM.contDiff.comp
    (b1_smooth.comp ((flatPosition.contDiff.comp contDiff_fst).prodMk contDiff_snd))

theorem symbolSlice_smooth (p : PhysicalMomentum) : ContDiff ℝ ∞ (symbolSlice p) :=
  by
    change ContDiff ℝ ∞ (fun x : PhysicalMomentum => jointSymbol (x,p))
    have embed : ContDiff ℝ ∞ (fun x : PhysicalMomentum => (x,p)) :=
      contDiff_id.prodMk contDiff_const
    exact jointSymbol_smooth.comp embed

def sourceSchwartzSlice (p : PhysicalMomentum) : 𝓢(PhysicalMomentum,ℂ) :=
  (symbolSlice_compact p).toSchwartzMap (symbolSlice_smooth p)

theorem sourceSchwartzSlice_apply (p x : PhysicalMomentum) :
    sourceSchwartzSlice p x=symbolSlice p x := rfl

theorem sourceSchwartzSlice_fourier (p k : PhysicalMomentum) :
    𝓕 (sourceSchwartzSlice p) k=partialFourier p k := rfl

def unitMomentum (p : PhysicalMomentum) : PhysicalMomentum := ‖p‖⁻¹ • p

theorem unitMomentum_norm (p : PhysicalMomentum) (nonzero : p≠0) : ‖unitMomentum p‖=1 := by
  rw [unitMomentum,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr nonzero)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero)]

theorem normalized_unitMomentum (p : PhysicalMomentum) (nonzero : p≠0) :
    normalizedMomentum (unitMomentum p)=normalizedMomentum p := by
  ext i
  change unitMomentum p i/‖unitMomentum p‖=p i/‖p‖
  rw [unitMomentum_norm p nonzero,div_one]
  simp only [unitMomentum,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem unit_radialRoot (p : PhysicalMomentum) (unit : ‖p‖=1) : radialRoot p=1 := by
  rw [radialRoot,unit]
  norm_num [sourceChi]

theorem symbolSlice_radial (p : PhysicalMomentum) (nonzero : p≠0) :
    symbolSlice p=((‖p‖*radialRoot p : ℝ) : ℂ) • symbolSlice (unitMomentum p) := by
  ext x
  have realVersion : b1 (flatPosition x,p)=(‖p‖*radialRoot p)*b1 (flatPosition x,unitMomentum p) := by
    rw [b1_radial_readback (flatPosition x,p) nonzero]
    change sourceThetaRoot (flatPosition x,normalizedMomentum p)*radialRoot p*‖p‖*
      principalFactor (PreparationScalarCoordinates.fullCoordinates.symm (flatPosition x))
        (nativeCovector (unitMomentum p))=(‖p‖*radialRoot p)*
          (sourceThetaRoot (flatPosition x,normalizedMomentum (unitMomentum p))*radialRoot (unitMomentum p)*
            principalFactor (PreparationScalarCoordinates.fullCoordinates.symm (flatPosition x))
              (nativeCovector (unitMomentum p)))
    rw [normalized_unitMomentum p nonzero,unit_radialRoot _ (unitMomentum_norm p nonzero)]
    ring
  change (b1 (flatPosition x,p) : ℂ)=((‖p‖*radialRoot p : ℝ) : ℂ)*
    (b1 (flatPosition x,unitMomentum p) : ℂ)
  rw [realVersion,Complex.ofReal_mul]

end LowEnergy.PreparationVacuumWeylDecay
