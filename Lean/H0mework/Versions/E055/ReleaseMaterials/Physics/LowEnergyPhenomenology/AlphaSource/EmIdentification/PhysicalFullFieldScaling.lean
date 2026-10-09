import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldMixed
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldTransfer

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalFullFieldScattering
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldCovector
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField SU7MotherLieAlgebra StageNineLorentzConnectionVariation
open StageNineCoframeScalarMatterRegularity StageNineP286GaugeConnectionVariation
open SU7MotherGaugeTheory
open FullQuantum.StateGreen FullQuantum.Triangular YangMills.FullPairing
open FullQuantum.CoframeResponse FullQuantum.FullSpace
open Electromagnetic.CanonicalCoframe
open scoped Matrix BigOperators Topology InnerProductSpace

local instance scaleIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _

/-- The real part of a real-scaled complex field is the real-scaled real
    part. -/
private theorem complexRe_smul (r : ℝ) (v : Fin 289 → ℂ) :
    (fun j => (((r : ℂ) • v) j).re) = r • fun j => (v j).re := by
  funext j
  rw [Pi.smul_apply]
  show ((r : ℂ) • v j).re = r • (v j).re
  rw [smul_eq_mul, smul_eq_mul]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private theorem complexIm_smul (r : ℝ) (v : Fin 289 → ℂ) :
    (fun j => (((r : ℂ) • v) j).im) = r • fun j => (v j).im := by
  funext j
  rw [Pi.smul_apply]
  show ((r : ℂ) • v j).im = r • (v j).im
  rw [smul_eq_mul, smul_eq_mul]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- The original density coefficients scale by `(r : ℂ)` under a real field
    scaling. -/
theorem fieldCoefficients_smul (r : ℝ) (f : Field289) (i : Fin 4) :
    fieldCoefficients (sourceField (r • f)) i =
      (r : ℂ) • fieldCoefficients (sourceField f) i := by
  rw [← realDensityCoefficients_source (r • f) i,
    ← realDensityCoefficients_source f i, map_smul]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) r (realDensityCoefficients i f)

/-- The original frequency coefficients scale by `(r : ℂ)`. -/
theorem frequencyCoefficients_smul (r : ℝ) (f : Field289) (i : Fin 4) :
    frequencyCoefficients (sourceField (r • f)) i =
      (r : ℂ) • frequencyCoefficients (sourceField f) i := by
  rw [← realFrequencyCoefficients_source (r • f) i,
    ← realFrequencyCoefficients_source f i, map_smul]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) r
    (realFrequencyCoefficients i f)

/-- The original mixed coefficients scale by `(r : ℂ)` in each real field
    argument. -/
theorem mixedCoefficients_smul_coe_left (r : ℝ) (f g : Field289) (i : Fin 4) :
    mixedCoefficients (sourceField (r • f)) (sourceField g) i =
      (r : ℂ) • mixedCoefficients (sourceField f) (sourceField g) i := by
  rw [mixedCoefficients_smul_left r f g i]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) r
    (mixedCoefficients (sourceField f) (sourceField g) i)

theorem mixedCoefficients_smul_coe_right (r : ℝ) (f g : Field289) (i : Fin 4) :
    mixedCoefficients (sourceField f) (sourceField (r • g)) i =
      (r : ℂ) • mixedCoefficients (sourceField f) (sourceField g) i := by
  rw [mixedCoefficients_smul_right r f g i]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) r
    (mixedCoefficients (sourceField f) (sourceField g) i)

/-- The complex direction coefficients scale by `(r : ℂ)` when the original
    complex field is scaled by the real `r`. -/
theorem complexCoefficients_smul (r : ℝ) (v : Fin 289 → ℂ) (i : Fin 4) :
    complexCoefficients (originalComplexDirection ((r : ℂ) • v)) i =
      (r : ℂ) • complexCoefficients (originalComplexDirection v) i := by
  unfold complexCoefficients originalComplexDirection
  dsimp only
  rw [complexRe_smul r v, complexIm_smul r v, fieldCoefficients_smul,
    fieldCoefficients_smul]
  rw [smul_add, smul_comm Complex.I]

private theorem complexCoefficients_smul_map (r : ℝ) (v : Fin 289 → ℂ) :
    complexCoefficients (originalComplexDirection ((r : ℂ) • v)) =
      (r : ℂ) • complexCoefficients (originalComplexDirection v) :=
  funext (complexCoefficients_smul r v)

theorem complexFrequencyCoefficients_smul (r : ℝ) (v : Fin 289 → ℂ)
    (i : Fin 4) :
    complexFrequencyCoefficients (originalComplexDirection ((r : ℂ) • v)) i =
      (r : ℂ) • complexFrequencyCoefficients (originalComplexDirection v) i := by
  unfold complexFrequencyCoefficients originalComplexDirection
  dsimp only
  rw [complexRe_smul r v, complexIm_smul r v, frequencyCoefficients_smul,
    frequencyCoefficients_smul]
  rw [smul_add, smul_comm Complex.I]

private theorem complexFrequencyCoefficients_smul_map (r : ℝ)
    (v : Fin 289 → ℂ) :
    complexFrequencyCoefficients (originalComplexDirection ((r : ℂ) • v)) =
      (r : ℂ) • complexFrequencyCoefficients (originalComplexDirection v) :=
  funext (complexFrequencyCoefficients_smul r v)

/-- The original complex mixed coefficients scale by `(r : ℂ)²` under the
    common real field scaling of both directions. -/
theorem complexMixedCoefficients_smul (r : ℝ) (v w : Fin 289 → ℂ) (i : Fin 4) :
    complexMixedCoefficients (originalComplexDirection ((r : ℂ) • v))
        (originalComplexDirection ((r : ℂ) • w)) i =
      (r : ℂ)^2 • complexMixedCoefficients (originalComplexDirection v)
        (originalComplexDirection w) i := by
  unfold complexMixedCoefficients originalComplexDirection
  dsimp only
  rw [complexRe_smul r v, complexIm_smul r v, complexRe_smul r w,
    complexIm_smul r w]
  simp only [mixedCoefficients_smul_coe_left, mixedCoefficients_smul_coe_right]
  rw [pow_two]
  simp only [smul_smul, smul_add, smul_sub, smul_comm Complex.I]

/-- `shiftCoefficients` is complex-linear in the coefficient row. -/
theorem shiftCoefficients_smul (s : ℂ) (A : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (i : Fin 4) :
    shiftCoefficients (s • A) shift i = s • shiftCoefficients A shift i := by
  induction i using Fin.cases with
  | zero =>
      simp only [shiftCoefficients, Fin.cases_zero, Pi.smul_apply, smul_add,
        Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _
  | succ j =>
      simp only [shiftCoefficients, Fin.cases_succ, Pi.smul_apply]

private theorem shiftCoefficients_smul_map (s : ℂ)
    (A : Fin 4 → FiberOperators) (shift : Fin 3 → ℝ) :
    shiftCoefficients (s • A) shift = s • shiftCoefficients A shift :=
  funext (shiftCoefficients_smul s A shift)

/-- The adjoint row of a real-scaled coefficient row is the scaled adjoint
    row: `r` real survives the conjugate-linear adjoint. -/
theorem adjointCoefficients_smul (r : ℝ) (A : Fin 4 → FiberOperators)
    (i : Fin 4) :
    adjointCoefficients ((r : ℂ) • A) i =
      (r : ℂ) • adjointCoefficients A i := by
  simp only [adjointCoefficients, Pi.smul_apply]
  rw [map_smulₛₗ ContinuousLinearMap.adjoint, starRingEnd_apply,
    Complex.star_def, Complex.conj_ofReal]

private theorem adjointCoefficients_smul_map (r : ℝ)
    (A : Fin 4 → FiberOperators) :
    adjointCoefficients ((r : ℂ) • A) = (r : ℂ) • adjointCoefficients A :=
  funext (adjointCoefficients_smul r A)

/-- The real-reader coefficient row scales by `(r : ℂ)`. -/
theorem realReaderCoefficients_smul (r : ℝ) (vp vn : Fin 289 → ℂ)
    (shift : Fin 3 → ℝ) (i : Fin 4) :
    realReaderCoefficients (originalTransferPair ((r : ℂ) • vp)
        ((r : ℂ) • vn)) shift i =
      (r : ℂ) • realReaderCoefficients (originalTransferPair vp vn) shift i := by
  unfold realReaderCoefficients originalTransferPair
  dsimp only
  rw [complexCoefficients_smul_map, complexCoefficients_smul_map,
    shiftCoefficients_smul_map, adjointCoefficients_smul_map]
  simp only [Pi.smul_apply]
  rw [smul_add, smul_add, smul_add]
  rw [smul_comm (2⁻¹ : ℂ) ((r : ℂ)), smul_comm (2⁻¹ : ℂ) ((r : ℂ))]

private theorem realReaderCoefficients_smul_map (r : ℝ) (vp vn : Fin 289 → ℂ)
    (shift : Fin 3 → ℝ) :
    realReaderCoefficients (originalTransferPair ((r : ℂ) • vp)
        ((r : ℂ) • vn)) shift =
      (r : ℂ) • realReaderCoefficients (originalTransferPair vp vn) shift :=
  funext (realReaderCoefficients_smul r vp vn shift)

/-- The real mixed coefficient row scales by `(r : ℂ)²`. -/
theorem realMixedCoefficients_smul (r : ℝ) (vp vn wp wn : Fin 289 → ℂ)
    (i : Fin 4) :
    realMixedCoefficients (originalTransferPair ((r : ℂ) • vp)
        ((r : ℂ) • vn)) (originalTransferPair ((r : ℂ) • wp)
        ((r : ℂ) • wn)) i =
      (r : ℂ)^2 • realMixedCoefficients (originalTransferPair vp vn)
        (originalTransferPair wp wn) i := by
  unfold realMixedCoefficients originalTransferPair
  dsimp only
  rw [complexMixedCoefficients_smul, complexMixedCoefficients_smul]
  have hadj : ContinuousLinearMap.adjoint
      ((r : ℂ)^2 •
        complexMixedCoefficients (originalComplexDirection vp)
          (originalComplexDirection wn) i) =
      (r : ℂ)^2 • ContinuousLinearMap.adjoint
        (complexMixedCoefficients (originalComplexDirection vp)
          (originalComplexDirection wn) i) := by
    rw [map_smulₛₗ ContinuousLinearMap.adjoint, starRingEnd_apply,
      Complex.star_def, map_pow, Complex.conj_ofReal]
  rw [hadj]
  rw [smul_add, smul_add, smul_add]
  rw [smul_comm (2⁻¹ : ℂ) ((r : ℂ)^2), smul_comm (2⁻¹ : ℂ) ((r : ℂ)^2)]

private theorem realMixedCoefficients_smul_map (r : ℝ) (vp vn wp wn :
    Fin 289 → ℂ) :
    realMixedCoefficients (originalTransferPair ((r : ℂ) • vp)
        ((r : ℂ) • vn)) (originalTransferPair ((r : ℂ) • wp)
        ((r : ℂ) • wn)) =
      (r : ℂ)^2 • realMixedCoefficients (originalTransferPair vp vn)
        (originalTransferPair wp wn) :=
  funext (realMixedCoefficients_smul r vp vn wp wn)

private theorem orderedLeft_smul (s : ℂ) (A : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (time age : ℝ) (i : Fin 4) :
    orderedLeft (s • A) shift time age i =
      s • orderedLeft A shift time age i := by
  unfold orderedLeft
  rw [shiftCoefficients_smul, ContinuousLinearMap.smul_compLpL]
  simp only [mul_smul_comm, smul_mul_assoc]

private theorem orderedRight_smul (s : ℂ) (B : Fin 4 → FiberOperators)
    (age : ℝ) (j : Fin 4) :
    orderedRight (s • B) age j = s • orderedRight B age j := by
  unfold orderedRight
  rw [Pi.smul_apply, ContinuousLinearMap.smul_compLpL]
  simp only [smul_mul_assoc]

private theorem orderedWord_smul_left (s : ℂ) (A B : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (time age : ℝ) :
    orderedWord (s • A) B shift time age =
      s • orderedWord A B shift time age := by
  unfold orderedWord
  simp only [orderedLeft_smul, smul_mul_assoc, Finset.smul_sum]

private theorem orderedWord_smul_right (s : ℂ) (A B : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (time age : ℝ) :
    orderedWord A (s • B) shift time age =
      s • orderedWord A B shift time age := by
  unfold orderedWord
  simp only [orderedRight_smul, mul_smul_comm, Finset.smul_sum]

/-- The two-time kernel of the common real-scaled transfer fields is the
    `(r : ℂ)²`-scaled original kernel. -/
theorem fieldTwoTimeKernel_smul (r : ℝ) (vp vn wp wn : Fin 289 → ℂ)
    (shift : Fin 3 → ℝ) (time age : ℝ) :
    fieldTwoTimeKernel (originalTransferPair ((r : ℂ) • vp) ((r : ℂ) • vn))
        (originalTransferPair ((r : ℂ) • wp) ((r : ℂ) • wn)) shift time age =
      (r : ℂ)^2 • fieldTwoTimeKernel (originalTransferPair vp vn)
        (originalTransferPair wp wn) shift time age := by
  dsimp only [fieldTwoTimeKernel]
  simp only [realReaderCoefficients_smul_map]
  simp only [originalTransferPair]
  simp only [complexFrequencyCoefficients_smul_map]
  simp only [adjointCoefficients_smul_map, shiftCoefficients_smul_map]
  simp only [orderedWord_smul_left, orderedWord_smul_right]
  rw [← smul_sub, ← smul_sub, smul_comm Complex.I, smul_comm Complex.I]
  rw [pow_two]
  simp only [smul_smul, mul_assoc]

/-- The contact word of a scaled coefficient row is the scaled contact
    word. -/
theorem contactWord_smul (s : ℂ) (C : Fin 4 → FiberOperators) (time : ℝ) :
    contactWord (s • C) time = s • contactWord C time := by
  unfold contactWord
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_compLpL, mul_smul_comm,
    smul_mul_assoc, Finset.smul_sum]

/-- The direct mixed contact of the common real-scaled transfer fields is the
    `(r : ℂ)²`-scaled original contact. -/
theorem fieldMixedContact_smul (r : ℝ) (vp vn wp wn : Fin 289 → ℂ)
    (time : ℝ) :
    fieldMixedContact (originalTransferPair ((r : ℂ) • vp) ((r : ℂ) • vn))
        (originalTransferPair ((r : ℂ) • wp) ((r : ℂ) • wn)) time =
      (r : ℂ)^2 • fieldMixedContact (originalTransferPair vp vn)
        (originalTransferPair wp wn) time := by
  unfold fieldMixedContact
  rw [realMixedCoefficients_smul_map]
  exact contactWord_smul _ _ _


/-- The original scattering pair of the common real-scaled transfer fields is
    the `(r : ℂ)²`-scaled pair, including the contact component. -/
theorem original_scattering_real_scale (momentum : Fin 3 → ℝ)
    (vp vn wp wn : Fin 289 → ℂ) (shift : Fin 3 → ℝ) (time age : ℝ) (r : ℝ) :
    originalScatteringPair momentum
        (originalTransferPair ((r : ℂ) • vp) ((r : ℂ) • vn))
        (originalTransferPair ((r : ℂ) • wp) ((r : ℂ) • wn)) shift time age =
      (r : ℂ)^2 • originalScatteringPair momentum
        (originalTransferPair vp vn) (originalTransferPair wp wn)
        shift time age := by
  simp only [originalScatteringPair, fieldMother_read, fieldContactMother_read]
  simp only [fieldTwoTimeKernel_smul, fieldMixedContact_smul]
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · simp only [Prod.smul_mk, smul_apply, inner_smul_right, smul_eq_mul]
    ring
  · simp only [Prod.smul_mk, smul_apply, inner_smul_right, smul_eq_mul]
    ring

end LowEnergy.GaussComposite.PhysicalFullFieldScattering
