import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedClockGerm

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedClockSchur
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator ActualDressedFullCoulomb ActualDressedNoether
open ActualDressedSignal ActualDressedPencil ActualDressedClockMoment ActualDressedPhysicalClock
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint
open ActualEMDressedSchur ActualEMDressedClockGerm Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceGreen originalJacobi originalChange originalInverse originalReadback
  originalRowLift sourceNull sourceNullLift sourceNullCoordinates sourceCokernel clockResolvent
  clockFeedback clockGreen dressedSynchronizedPencil dressedWindowPolarization anchorEvent

private def quantum (event : DressedEvent) (T : ℝ) (z : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  dressedWindowPolarization (anchorEvent event) 0 (sourceInputClock z) z T

/-- The two original nine-coordinate maps both vary with the same Fourier clock. -/
def clockResponseNine (event : DressedEvent) (T : ℝ) (z : ℂ) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) : SignalAmplitude :=
  clockResolvent event T z*ᵥ((T:ℂ)⁻¹ • (clockGreen z*ᵥforcing)+sourceNullLift (sourceInputClock z) initial)

def clockSchur (event : DressedEvent) (T : ℝ) (z : ℂ) : Matrix (Fin 9) (Fin 9) ℂ :=
  LinearMap.toMatrix' ((sourceCokernel (sourceInputClock z)).comp
    ((Matrix.toLin' (quantum event T z)).comp
      ((Matrix.toLin' (clockResolvent event T z)).comp (sourceNullLift (sourceInputClock z)))))

def clockSchurSource (event : DressedEvent) (T : ℝ) (z : ℂ) (forcing : SignalAmplitude) : Fin 9→ℂ :=
  -sourceCokernel (sourceInputClock z) (forcing+quantum event T z*ᵥ
    (clockResolvent event T z*ᵥ((T:ℂ)⁻¹ • (clockGreen z*ᵥforcing))))

theorem clock_schur_generated (event : DressedEvent) (T : ℝ) (z : ℂ)
    (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    sourceCokernel (sourceInputClock z) (forcing+quantum event T z*ᵥclockResponseNine event T z forcing initial)=
      clockSchur event T z*ᵥinitial-clockSchurSource event T z forcing := by
  rw [clockSchur,LinearMap.toMatrix'_mulVec]
  simp only [LinearMap.comp_apply,Matrix.toLin'_apply]
  unfold clockResponseNine clockSchurSource
  rw [Matrix.mulVec_add,Matrix.mulVec_add,←add_assoc,map_add]
  abel

private theorem source_pencil (event : DressedEvent) (T : ℝ) (z : ℂ) :
    dressedSynchronizedPencil (anchorEvent event) 0 z T=
      (T:ℂ) • originalJacobi (sourceInputClock z)-quantum event T z := by
  have point : fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial 0) z=sourceInputClock z := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simp only [fullMomentum,Fin.cases_succ,sourceInputClock,Pi.single_eq_of_ne (Fin.succ_ne_zero j),
        PreparationVacuumPhysicalFeedback.physicalSpatial,Pi.zero_apply,Complex.ofReal_zero,mul_zero]
  rw [dressed_synchronized_pencil_original_action,ActualEMAction.em_jacobi_source,point]
  rfl

private theorem response_generated (event : DressedEvent) (T : ℝ) (z : ℂ)
    (unit : IsUnit (clockFeedback event T z)) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    clockResponseNine event T z forcing initial=sourceNullLift (sourceInputClock z) initial+(T:ℂ)⁻¹ •
      (clockGreen z*ᵥ(forcing+quantum event T z*ᵥclockResponseNine event T z forcing initial)) := by
  have determinant:=(Matrix.isUnit_iff_isUnit_det _).mp unit
  have inverse : clockFeedback event T z*clockResolvent event T z=1:=by
    unfold clockResolvent
    exact Matrix.mul_nonsing_inv _ determinant
  have equation:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥ
    ((T:ℂ)⁻¹ • (clockGreen z*ᵥforcing)+sourceNullLift (sourceInputClock z) initial)) inverse
  rw [←Matrix.mulVec_mulVec,Matrix.one_mulVec,←clockResponseNine] at equation
  rw [clockFeedback,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,←Matrix.mulVec_mulVec] at equation
  have generated:=sub_eq_iff_eq_add.mp equation
  calc
    _=_ := generated
    _=_ := by rw [Matrix.mulVec_add,smul_add]; abel

attribute [local irreducible] clockResponseNine quantum

private theorem response_initial (event : DressedEvent) (T : ℝ) (z : ℂ)
    (regular : sourceInputClock z∈regularSource) (unit : IsUnit (clockFeedback event T z))
    (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    sourceNullCoordinates (sourceInputClock z) (clockResponseNine event T z forcing initial)=initial := by
  have nullGreen : sourceNull (sourceInputClock z)*clockGreen z=0 := by
    rw [clock_green_actual z regular]
    exact source_null_green ⟨sourceInputClock z,regular⟩
  have projected : sourceNull (sourceInputClock z)*ᵥclockResponseNine event T z forcing initial=
      sourceNullLift (sourceInputClock z) initial := by
    conv_lhs => arg 2; rw [response_generated event T z unit]
    rw [Matrix.mulVec_add,source_null_lift_fixed,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
      nullGreen,Matrix.zero_mulVec,smul_zero,add_zero]
  have read:=congrArg (sourceNullCoordinates (sourceInputClock z)) projected
  rw [←source_null_coordinates_generated,source_null_lift_coordinates,source_null_lift_coordinates] at read
  exact read

private theorem response_euler (event : DressedEvent) (T : ℝ) (nonzero : T≠0) (z : ℂ)
    (regular : sourceInputClock z∈regularSource) (unit : IsUnit (clockFeedback event T z))
    (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    dressedSynchronizedPencil (anchorEvent event) 0 z T*ᵥclockResponseNine event T z forcing initial=
      forcing-originalRowLift (sourceInputClock z)*ᵥsourceCompatibility (sourceInputClock z)
        (forcing+quantum event T z*ᵥclockResponseNine event T z forcing initial) := by
  have tn : (T:ℂ)≠0:=by exact_mod_cast nonzero
  have nullLift : originalJacobi (sourceInputClock z)*ᵥsourceNullLift (sourceInputClock z) initial=0 := by
    rw [←source_null_lift_fixed (sourceInputClock z) initial,Matrix.mulVec_mulVec,source_null_euler,Matrix.zero_mulVec]
  rw [source_pencil,Matrix.sub_mulVec,Matrix.smul_mulVec]
  conv_lhs => arg 1; arg 2; rw [response_generated event T z unit]
  rw [Matrix.mulVec_add,nullLift,zero_add,Matrix.mulVec_smul,smul_smul,mul_inv_cancel₀ tn,one_smul,
    clock_green_actual z regular]
  have original:=original_forced_field ⟨sourceInputClock z,regular⟩
    (forcing+quantum event T z*ᵥclockResponseNine event T z forcing initial)
  rw [PreparationVacuumOriginalGreenFeedback.sourceField] at original
  rw [original]
  abel

private theorem response_restores (event : DressedEvent) (T : ℝ) (nonzero : T≠0) (z : ℂ)
    (regular : sourceInputClock z∈regularSource) (unit : IsUnit (clockFeedback event T z)) (a : SignalAmplitude) :
    clockResponseNine event T z (dressedSynchronizedPencil (anchorEvent event) 0 z T*ᵥa)
      (sourceNullCoordinates (sourceInputClock z) a)=a := by
  have tn : (T:ℂ)≠0:=by exact_mod_cast nonzero
  have original : clockGreen z*originalJacobi (sourceInputClock z)=1-sourceNull (sourceInputClock z) := by
    rw [clock_green_actual z regular,sourceNull]
    exact sourceGreen_original_left ⟨sourceInputClock z,regular⟩
  have equation : (T:ℂ)⁻¹ • (clockGreen z*ᵥ(dressedSynchronizedPencil (anchorEvent event) 0 z T*ᵥa))+
      sourceNullLift (sourceInputClock z) (sourceNullCoordinates (sourceInputClock z) a)=clockFeedback event T z*ᵥa := by
    rw [source_null_coordinates_generated,source_pencil,Matrix.sub_mulVec,Matrix.smul_mulVec,
      Matrix.mulVec_sub,Matrix.mulVec_smul,smul_sub,smul_smul,inv_mul_cancel₀ tn,one_smul,
      Matrix.mulVec_mulVec,original,Matrix.sub_mulVec,Matrix.one_mulVec,clockFeedback,
      Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,←Matrix.mulVec_mulVec]
    unfold quantum
    abel
  have inverse : clockResolvent event T z*clockFeedback event T z=1:=by
    unfold clockResolvent
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp unit)
  rw [clockResponseNine,equation,Matrix.mulVec_mulVec,inverse,Matrix.one_mulVec]

/-- The generated dynamic germ retains and solves for exactly the original nine initial coordinates. -/
theorem clock_full_solution_schur (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    ∀ᶠz in 𝓝 (3:ℂ),∀forcing a : SignalAmplitude,
      dressedSynchronizedPencil (anchorEvent event) 0 z T*ᵥa=forcing ↔
        ∃initial : Fin 9→ℂ,a=clockResponseNine event T z forcing initial ∧
          sourceNullCoordinates (sourceInputClock z) a=initial ∧
          clockSchur event T z*ᵥinitial=clockSchurSource event T z forcing := by
  obtain ⟨radius,pos,domain⟩:=clock_regular_neighborhood event T positive small
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨radius,pos,?_⟩
  intro z close
  obtain ⟨_,regular,unit⟩:=domain z (by simpa only [dist_eq_norm] using close)
  intro forcing a
  constructor
  · intro equation
    have restored : a=clockResponseNine event T z forcing (sourceNullCoordinates (sourceInputClock z) a) := by
      rw [←equation,response_restores event T positive.ne' z regular unit]
    refine ⟨sourceNullCoordinates (sourceInputClock z) a,restored,rfl,?_⟩
    have sumEq : forcing+quantum event T z*ᵥa=(T:ℂ) • (originalJacobi (sourceInputClock z)*ᵥa) := by
      rw [←equation,source_pencil,Matrix.sub_mulVec,Matrix.smul_mulVec]
      abel
    have compatible : sourceCompatibility (sourceInputClock z) (forcing+quantum event T z*ᵥa)=0 := by
      rw [sumEq,sourceCompatibility,Matrix.mulVec_smul,Matrix.mulVec_smul]
      change (T:ℂ) • sourceCompatibility (sourceInputClock z) (originalJacobi (sourceInputClock z)*ᵥa)=0
      rw [source_compatibility_euler,smul_zero]
    have nine:=(source_compatibility_nine (sourceInputClock z) _).mp compatible
    rw [restored,clock_schur_generated] at nine
    exact sub_eq_zero.mp nine
  · rintro ⟨initial,rfl,_,schur⟩
    have compatible : sourceCompatibility (sourceInputClock z)
        (forcing+quantum event T z*ᵥclockResponseNine event T z forcing initial)=0 := by
      apply (source_compatibility_nine (sourceInputClock z) _).mpr
      rw [clock_schur_generated,schur,sub_self]
    rw [response_euler event T positive.ne' z regular unit,compatible,Matrix.mulVec_zero,sub_zero]

/-- All initial coordinates survive for arbitrary forcing throughout the source-generated regular germ. -/
theorem clock_response_initial (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1) :
    ∀ᶠz in 𝓝 (3:ℂ),∀forcing : SignalAmplitude,∀initial : Fin 9→ℂ,
      sourceNullCoordinates (sourceInputClock z) (clockResponseNine event T z forcing initial)=initial := by
  obtain ⟨radius,pos,domain⟩:=clock_regular_neighborhood event T positive small
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨radius,pos,?_⟩
  intro z close forcing initial
  obtain ⟨_,regular,unit⟩:=domain z (by simpa only [dist_eq_norm] using close)
  exact response_initial event T z regular unit forcing initial

end LowEnergy.GaussComposite.ActualEMDressedClockSchur
