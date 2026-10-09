import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldScaling

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
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

-- Keep the source coefficient ports opaque inside this module; every
-- continuity argument reads them only through the named port lemmas.
attribute [local irreducible] sourceField originalComplexDirection
  originalTransferPair complexCoefficients complexFrequencyCoefficients
  complexMixedCoefficients realReaderCoefficients realMixedCoefficients

noncomputable section

/-- The carrier of the four complex field vectors consumed by the joint
    continuity statements. -/
abbrev FourFields :=
  ((Fin 289 → ℂ) × (Fin 289 → ℂ)) × ((Fin 289 → ℂ) × (Fin 289 → ℂ))

/-- The Lp lift of a fiber operator, bundled as a continuous linear map of the
    operator. It is the source `compLpL` lifted through `compLpL₂` on the
    identity. -/
def coefficientLpLift :
    FiberOperators →L[ℂ] (FullMatterL2 →L[ℂ] FullMatterL2) :=
  (ContinuousLinearMap.id ℂ FiberOperators).compLpL₂ 2 MeasureTheory.volume

private theorem coefficientLpLift_eq (A : FiberOperators) :
    coefficientLpLift A = A.compLpL 2 MeasureTheory.volume := by
  ext1 f
  rw [show coefficientLpLift A =
      ((ContinuousLinearMap.id ℂ FiberOperators).compLpL₂ 2
        MeasureTheory.volume) A from rfl]
  rw [ContinuousLinearMap.compLpL₂_apply_apply]
  rfl

/-- The real-bilinear mixed coefficient package as a joint continuous
    bilinear map, by finite-dimensionality of `Field289`. -/
def realMixedCoefficientContinuous (i : Fin 4) :
    Field289 →L[ℝ] Field289 →L[ℝ] FiberOperators :=
  LinearMap.toContinuousBilinearMap (realMixedCoefficientBilinear i)

/-- The continuous bilinear package reads back the original mixed
    coefficient. -/
theorem realMixedCoefficientContinuous_source (f g : Field289) (i : Fin 4) :
    realMixedCoefficientContinuous i f g =
      mixedCoefficients (sourceField f) (sourceField g) i :=
  (LinearMap.toContinuousBilinearMap_apply _ f g).trans
    (realMixedCoefficientBilinear_source f g i)

private theorem re289_continuous :
    Continuous (fun v : Fin 289 → ℂ => fun j => (v j).re) :=
  continuous_pi fun j => Complex.continuous_re.comp (continuous_apply j)

private theorem im289_continuous :
    Continuous (fun v : Fin 289 → ℂ => fun j => (v j).im) :=
  continuous_pi fun j => Complex.continuous_im.comp (continuous_apply j)

private theorem complexCoefficients_cts (i : Fin 4) :
    Continuous (fun v : Fin 289 → ℂ =>
      complexCoefficients (originalComplexDirection v) i) := by
  have e : (fun v : Fin 289 → ℂ =>
        complexCoefficients (originalComplexDirection v) i) =
      fun v => realDensityCoefficients i (fun j => (v j).re) +
        Complex.I • realDensityCoefficients i (fun j => (v j).im) := by
    funext v
    simp only [complexCoefficients, originalComplexDirection,
      realDensityCoefficients_source]
  rw [e]
  exact ((LinearMap.continuous_of_finiteDimensional
      (realDensityCoefficients i)).comp re289_continuous).add
    (((LinearMap.continuous_of_finiteDimensional
      (realDensityCoefficients i)).comp im289_continuous).const_smul Complex.I)

private theorem complexCoefficients_row_cts :
    Continuous (fun v : Fin 289 → ℂ =>
      complexCoefficients (originalComplexDirection v)) :=
  continuous_pi fun i => complexCoefficients_cts i

private theorem complexFrequencyCoefficients_cts (i : Fin 4) :
    Continuous (fun v : Fin 289 → ℂ =>
      complexFrequencyCoefficients (originalComplexDirection v) i) := by
  have e : (fun v : Fin 289 → ℂ =>
        complexFrequencyCoefficients (originalComplexDirection v) i) =
      fun v => realFrequencyCoefficients i (fun j => (v j).re) +
        Complex.I • realFrequencyCoefficients i (fun j => (v j).im) := by
    funext v
    simp only [complexFrequencyCoefficients, originalComplexDirection,
      realFrequencyCoefficients_source]
  rw [e]
  exact ((LinearMap.continuous_of_finiteDimensional
      (realFrequencyCoefficients i)).comp re289_continuous).add
    (((LinearMap.continuous_of_finiteDimensional
      (realFrequencyCoefficients i)).comp im289_continuous).const_smul
      Complex.I)

private theorem complexFrequencyCoefficients_row_cts :
    Continuous (fun v : Fin 289 → ℂ =>
      complexFrequencyCoefficients (originalComplexDirection v)) :=
  continuous_pi fun i => complexFrequencyCoefficients_cts i

private theorem shiftCoefficients_cts (shift : Fin 3 → ℝ) (i : Fin 4) :
    Continuous (fun A : Fin 4 → FiberOperators =>
      shiftCoefficients A shift i) := by
  induction i using Fin.cases with
  | zero =>
      simp only [shiftCoefficients, Fin.cases_zero]
      exact Continuous.add (continuous_apply 0)
        (continuous_finsetSum _ fun j _ =>
          (continuous_apply (j.succ : Fin 4)).const_smul ((shift j : ℂ)))
  | succ j =>
      simp only [shiftCoefficients, Fin.cases_succ]
      exact continuous_apply _

private theorem shiftCoefficients_row_cts (shift : Fin 3 → ℝ) :
    Continuous (fun A : Fin 4 → FiberOperators => shiftCoefficients A shift) :=
  continuous_pi fun i => shiftCoefficients_cts shift i

private theorem adjointCoefficients_cts (i : Fin 4) :
    Continuous (fun A : Fin 4 → FiberOperators => adjointCoefficients A i) :=
  ContinuousLinearMap.adjoint.continuous.comp (continuous_apply i)

private theorem adjointCoefficients_row_cts :
    Continuous (fun A : Fin 4 → FiberOperators => adjointCoefficients A) :=
  continuous_pi fun i => adjointCoefficients_cts i

private theorem realReaderCoefficients_cts (shift : Fin 3 → ℝ) (i : Fin 4) :
    Continuous (fun p : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      realReaderCoefficients (originalTransferPair p.1 p.2) shift i) := by
  have e : (fun p : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
        realReaderCoefficients (originalTransferPair p.1 p.2) shift i) =
      fun p => (2 : ℂ)⁻¹ •
        (complexCoefficients (originalComplexDirection p.2) i +
          adjointCoefficients
            (shiftCoefficients (complexCoefficients
              (originalComplexDirection p.1)) (-shift)) i) := by
    funext p
    simp only [realReaderCoefficients, originalTransferPair]
  rw [e]
  have hneg : Continuous (fun p : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      complexCoefficients (originalComplexDirection p.2) i) :=
    (complexCoefficients_cts i).comp continuous_snd
  have hpos : Continuous (fun p : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      adjointCoefficients (shiftCoefficients
        (complexCoefficients (originalComplexDirection p.1)) (-shift)) i) :=
    (adjointCoefficients_cts i).comp
      ((shiftCoefficients_row_cts (-shift)).comp
        (complexCoefficients_row_cts.comp continuous_fst))
  exact Continuous.const_smul (hneg.add hpos) (2 : ℂ)⁻¹

private theorem realReaderCoefficients_row_cts (shift : Fin 3 → ℝ) :
    Continuous (fun p : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      realReaderCoefficients (originalTransferPair p.1 p.2) shift) :=
  continuous_pi fun i => realReaderCoefficients_cts shift i

private theorem complexMixedCoefficients_cts (i : Fin 4) :
    Continuous (fun q : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      complexMixedCoefficients (originalComplexDirection q.1)
        (originalComplexDirection q.2) i) := by
  have e : (fun q : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
        complexMixedCoefficients (originalComplexDirection q.1)
          (originalComplexDirection q.2) i) =
      fun q => realMixedCoefficientContinuous i (fun j => (q.1 j).re)
          (fun j => (q.2 j).re) -
        realMixedCoefficientContinuous i (fun j => (q.1 j).im)
          (fun j => (q.2 j).im) +
        Complex.I • (realMixedCoefficientContinuous i (fun j => (q.1 j).re)
            (fun j => (q.2 j).im) +
          realMixedCoefficientContinuous i (fun j => (q.1 j).im)
            (fun j => (q.2 j).re)) := by
    funext q
    simp only [complexMixedCoefficients, originalComplexDirection,
      realMixedCoefficientContinuous_source]
  rw [e]
  have hrr : Continuous (fun q : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      realMixedCoefficientContinuous i (fun j => (q.1 j).re)
        (fun j => (q.2 j).re)) :=
    ((realMixedCoefficientContinuous i).continuous.comp
      (re289_continuous.comp continuous_fst)).clm_apply
      (re289_continuous.comp continuous_snd)
  have hii : Continuous (fun q : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      realMixedCoefficientContinuous i (fun j => (q.1 j).im)
        (fun j => (q.2 j).im)) :=
    ((realMixedCoefficientContinuous i).continuous.comp
      (im289_continuous.comp continuous_fst)).clm_apply
      (im289_continuous.comp continuous_snd)
  have hri : Continuous (fun q : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      realMixedCoefficientContinuous i (fun j => (q.1 j).re)
        (fun j => (q.2 j).im)) :=
    ((realMixedCoefficientContinuous i).continuous.comp
      (re289_continuous.comp continuous_fst)).clm_apply
      (im289_continuous.comp continuous_snd)
  have hir : Continuous (fun q : (Fin 289 → ℂ) × (Fin 289 → ℂ) =>
      realMixedCoefficientContinuous i (fun j => (q.1 j).im)
        (fun j => (q.2 j).re)) :=
    ((realMixedCoefficientContinuous i).continuous.comp
      (im289_continuous.comp continuous_fst)).clm_apply
      (re289_continuous.comp continuous_snd)
  exact Continuous.add (hrr.sub hii)
    (Continuous.const_smul (hri.add hir) Complex.I)

/-- Joint continuity of the four-argument real mixed coefficient row. -/
theorem realMixedCoefficients_joint_cts (i : Fin 4) :
    Continuous (fun p : FourFields =>
      realMixedCoefficients (originalTransferPair p.1.1 p.1.2)
        (originalTransferPair p.2.1 p.2.2) i) := by
  have e : (fun p : FourFields =>
        realMixedCoefficients (originalTransferPair p.1.1 p.1.2)
          (originalTransferPair p.2.1 p.2.2) i) =
      fun p => (2 : ℂ)⁻¹ •
        (complexMixedCoefficients (originalComplexDirection p.1.2)
            (originalComplexDirection p.2.1) i +
          (complexMixedCoefficients (originalComplexDirection p.1.1)
            (originalComplexDirection p.2.2) i).adjoint) := by
    funext p
    simp only [realMixedCoefficients, originalTransferPair]
  rw [e]
  have hA : Continuous (fun p : FourFields =>
      complexMixedCoefficients (originalComplexDirection p.1.2)
        (originalComplexDirection p.2.1) i) :=
    (complexMixedCoefficients_cts i).comp
      (continuous_fst.snd.prodMk continuous_snd.fst)
  have hB : Continuous (fun p : FourFields =>
      (complexMixedCoefficients (originalComplexDirection p.1.1)
        (originalComplexDirection p.2.2) i).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp
      ((complexMixedCoefficients_cts i).comp
        (continuous_fst.fst.prodMk continuous_snd.snd))
  exact Continuous.const_smul (hA.add hB) (2 : ℂ)⁻¹

private theorem orderedLeft_cts (shift : Fin 3 → ℝ) (time age : ℝ)
    (i : Fin 4) :
    Continuous (fun A : Fin 4 → FiberOperators =>
      orderedLeft A shift time age i) := by
  have e : (fun A : Fin 4 → FiberOperators =>
        orderedLeft A shift time age i) =
      fun A => (coordinateLeg i).adjoint * spatialFlow 0 (-time) *
        coefficientLpLift (shiftCoefficients A shift i) *
        shiftFlow shift (time - age) := by
    funext A
    unfold orderedLeft
    rw [coefficientLpLift_eq]
  rw [e]
  exact (((continuous_const.mul continuous_const).mul
      (coefficientLpLift.continuous.comp
        (shiftCoefficients_cts shift i))).mul continuous_const)

private theorem orderedRight_cts (age : ℝ) (j : Fin 4) :
    Continuous (fun B : Fin 4 → FiberOperators => orderedRight B age j) := by
  have e : (fun B : Fin 4 → FiberOperators => orderedRight B age j) =
      fun B => coefficientLpLift (B j) * spatialFlow 0 age *
        coordinateLeg j := by
    funext B
    unfold orderedRight
    rw [coefficientLpLift_eq]
  rw [e]
  exact (((coefficientLpLift.continuous.comp (continuous_apply j)).mul
      continuous_const).mul continuous_const)

private theorem orderedWord_cts (shift : Fin 3 → ℝ) (time age : ℝ) :
    Continuous (fun q : (Fin 4 → FiberOperators) × (Fin 4 → FiberOperators) =>
      orderedWord q.1 q.2 shift time age) := by
  have e : (fun q : (Fin 4 → FiberOperators) × (Fin 4 → FiberOperators) =>
        orderedWord q.1 q.2 shift time age) =
      fun q => ∑ i : Fin 4, ∑ j : Fin 4,
        orderedLeft q.1 shift time age i * orderedRight q.2 age j := by
    funext q
    simp only [orderedWord]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ =>
      ((orderedLeft_cts shift time age i).comp continuous_fst).mul
        ((orderedRight_cts age j).comp continuous_snd)

private theorem contactWord_cts (time : ℝ) :
    Continuous (fun C : Fin 4 → FiberOperators => contactWord C time) := by
  have e : (fun C : Fin 4 → FiberOperators => contactWord C time) =
      fun C => ∑ j : Fin 4, (coordinateLeg 0).adjoint * spatialFlow 0 (-time) *
        coefficientLpLift (C j) * spatialFlow 0 time * coordinateLeg j := by
    funext C
    unfold contactWord
    apply Finset.sum_congr rfl
    intro j _
    rw [coefficientLpLift_eq]
  rw [e]
  exact continuous_finsetSum _ fun j _ =>
    ((((continuous_const.mul continuous_const).mul
        (coefficientLpLift.continuous.comp (continuous_apply j))).mul
      continuous_const).mul continuous_const)

/-- Joint continuity of the original two-time kernel in the four complex
    field vectors. -/
theorem fieldTwoTimeKernel_joint_cts (shift : Fin 3 → ℝ) (time age : ℝ) :
    Continuous (fun p : FourFields =>
      fieldTwoTimeKernel (originalTransferPair p.1.1 p.1.2)
        (originalTransferPair p.2.1 p.2.2) shift time age) := by
  have e : (fun p : FourFields =>
        fieldTwoTimeKernel (originalTransferPair p.1.1 p.1.2)
          (originalTransferPair p.2.1 p.2.2) shift time age) =
      fun p => Complex.I •
        (orderedWord
          (shiftCoefficients (adjointCoefficients
            (complexFrequencyCoefficients (originalComplexDirection p.2.2)))
            shift)
          (realReaderCoefficients (originalTransferPair p.1.1 p.1.2) shift)
          (-shift) age time -
        orderedWord
          (realReaderCoefficients (originalTransferPair p.1.1 p.1.2) shift)
          (complexFrequencyCoefficients (originalComplexDirection p.2.1))
          shift time age) := by
    funext p
    simp only [fieldTwoTimeKernel, originalTransferPair]
  rw [e]
  have hb : Continuous (fun p : FourFields =>
      shiftCoefficients (adjointCoefficients
        (complexFrequencyCoefficients (originalComplexDirection p.2.2)))
        shift) :=
    (shiftCoefficients_row_cts shift).comp (adjointCoefficients_row_cts.comp
      (complexFrequencyCoefficients_row_cts.comp continuous_snd.snd))
  have hJ : Continuous (fun p : FourFields =>
      realReaderCoefficients (originalTransferPair p.1.1 p.1.2) shift) :=
    (realReaderCoefficients_row_cts shift).comp continuous_fst
  have hfp : Continuous (fun p : FourFields =>
      complexFrequencyCoefficients (originalComplexDirection p.2.1)) :=
    complexFrequencyCoefficients_row_cts.comp continuous_snd.fst
  have hw1 : Continuous (fun p : FourFields =>
      orderedWord
        (shiftCoefficients (adjointCoefficients
          (complexFrequencyCoefficients (originalComplexDirection p.2.2)))
          shift)
        (realReaderCoefficients (originalTransferPair p.1.1 p.1.2) shift)
        (-shift) age time) := by
    convert (orderedWord_cts (-shift) age time).comp (hb.prodMk hJ) using 1
    funext p
    rfl
  have hw2 : Continuous (fun p : FourFields =>
      orderedWord
        (realReaderCoefficients (originalTransferPair p.1.1 p.1.2) shift)
        (complexFrequencyCoefficients (originalComplexDirection p.2.1))
        shift time age) := by
    convert (orderedWord_cts shift time age).comp (hJ.prodMk hfp) using 1
    funext p
    rfl
  exact Continuous.const_smul (hw1.sub hw2) Complex.I

/-- Joint continuity of the direct mixed contact in the four complex field
    vectors. -/
theorem fieldMixedContact_joint_cts (time : ℝ) :
    Continuous (fun p : FourFields =>
      fieldMixedContact (originalTransferPair p.1.1 p.1.2)
        (originalTransferPair p.2.1 p.2.2) time) := by
  have e : (fun p : FourFields =>
        fieldMixedContact (originalTransferPair p.1.1 p.1.2)
          (originalTransferPair p.2.1 p.2.2) time) =
      fun p => contactWord
        (fun i => realMixedCoefficients
          (originalTransferPair p.1.1 p.1.2)
          (originalTransferPair p.2.1 p.2.2) i) time := by
    funext p
    simp only [fieldMixedContact]
  rw [e]
  exact (contactWord_cts time).comp (continuous_pi realMixedCoefficients_joint_cts)

/-- The original scattering pair is jointly continuous in the four complex
    field vectors at fixed momentum, shift, time and age. Both components keep
    the two-time kernel and the direct contact separate. -/
theorem original_scattering_joint_continuous (momentum : Fin 3 → ℝ)
    (shift : Fin 3 → ℝ) (time age : ℝ) :
    Continuous (fun p : FourFields =>
      originalScatteringPair momentum
        (originalTransferPair p.1.1 p.1.2)
        (originalTransferPair p.2.1 p.2.2) shift time age) := by
  have e : (fun p : FourFields =>
        originalScatteringPair momentum
          (originalTransferPair p.1.1 p.1.2)
          (originalTransferPair p.2.1 p.2.2) shift time age) =
      fun p => (packetNormalization momentum *
          inner ℂ (Electromagnetic.CanonicalPacket.packet momentum)
            (fieldTwoTimeKernel (originalTransferPair p.1.1 p.1.2)
              (originalTransferPair p.2.1 p.2.2) shift time age
              (Electromagnetic.CanonicalPacket.packet momentum)),
        packetNormalization momentum *
          inner ℂ (Electromagnetic.CanonicalPacket.packet momentum)
            (fieldMixedContact (originalTransferPair p.1.1 p.1.2)
              (originalTransferPair p.2.1 p.2.2) time
              (Electromagnetic.CanonicalPacket.packet momentum))) := by
    funext p
    simp only [originalScatteringPair, fieldMother_read, fieldContactMother_read]
  rw [e]
  have hk : Continuous (fun p : FourFields =>
      inner ℂ (Electromagnetic.CanonicalPacket.packet momentum)
        (fieldTwoTimeKernel (originalTransferPair p.1.1 p.1.2)
          (originalTransferPair p.2.1 p.2.2) shift time age
          (Electromagnetic.CanonicalPacket.packet momentum))) :=
    continuous_inner.comp (continuous_const.prodMk
      ((fieldTwoTimeKernel_joint_cts shift time age).clm_apply
        continuous_const))
  have hc : Continuous (fun p : FourFields =>
      inner ℂ (Electromagnetic.CanonicalPacket.packet momentum)
        (fieldMixedContact (originalTransferPair p.1.1 p.1.2)
          (originalTransferPair p.2.1 p.2.2) time
          (Electromagnetic.CanonicalPacket.packet momentum))) :=
    continuous_inner.comp (continuous_const.prodMk
      ((fieldMixedContact_joint_cts time).clm_apply continuous_const))
  exact (continuous_const.mul hk).prodMk (continuous_const.mul hc)

end
end LowEnergy.GaussComposite.PhysicalFullFieldScattering
