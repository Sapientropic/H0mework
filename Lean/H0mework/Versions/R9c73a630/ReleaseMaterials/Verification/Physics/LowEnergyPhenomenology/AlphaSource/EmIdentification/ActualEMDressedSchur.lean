import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedConstraint

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedSchur
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint
open scoped Matrix BigOperators
attribute [local irreducible] originalChange originalInverse originalReadback sourceGreen
  anchorFeedbackResolvent dressedWindowPolarization anchorResponse anchorInput anchorEvent

private def nullSlot (i : Fin 9) : Fin 289 := ⟨112+i.val,by omega⟩
private theorem nullSlot_injective : Function.Injective nullSlot := by
  intro i j equal
  apply Fin.ext
  have values:=congrArg Fin.val equal
  dsimp only [nullSlot] at values
  omega

private def nullPadMatrix : Matrix (Fin 289) (Fin 9) ℂ := fun i j=>if nullSlot j=i then 1 else 0
private def nullPad : (Fin 9→ℂ)→ₗ[ℂ]SignalAmplitude := Matrix.toLin' nullPadMatrix
private def nullRead : SignalAmplitude→ₗ[ℂ](Fin 9→ℂ) :=
  LinearMap.pi (fun i=>LinearMap.proj (nullSlot i))

private theorem pad_at (v : Fin 9→ℂ) (i : Fin 9) : nullPad v (nullSlot i)=v i := by
  change (∑j : Fin 9,(if nullSlot j=nullSlot i then (1:ℂ) else 0)*v j)=v i
  simp only [nullSlot_injective.eq_iff,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

private theorem pad_outside (v : Fin 9→ℂ) (i : Fin 289) (outside : ¬(112 ≤ i.val ∧ i.val<121)) :
    nullPad v i=0 := by
  change (∑j : Fin 9,(if nullSlot j=i then (1:ℂ) else 0)*v j)=0
  apply Finset.sum_eq_zero
  intro j _
  have different : nullSlot j≠i := by
    intro same
    apply outside
    have values:=congrArg Fin.val same
    dsimp only [nullSlot] at values
    constructor <;> omega
  simp only [different,if_false,zero_mul]

private theorem read_pad (v : Fin 9→ℂ) : nullRead (nullPad v)=v := by
  funext i
  exact pad_at v i

private theorem pad_read (v : SignalAmplitude) : nullPad (nullRead v)=nullProjection*ᵥv := by
  funext i
  simp only [nullProjection,projectionMatrix,Matrix.mulVec_diagonal]
  by_cases inside : 112 ≤ i.val ∧ i.val<121
  · let j : Fin 9:=⟨i.val-112,by omega⟩
    have slot : nullSlot j=i := by apply Fin.ext; dsimp only [nullSlot,j]; omega
    rw [←slot,pad_at]
    change v (nullSlot j)=(if nullFlag (nullSlot j) then (1:ℂ) else 0)*v (nullSlot j)
    have flag : nullFlag (nullSlot j)=true := by unfold nullFlag nullSlot; simp; omega
    simp only [flag,ite_true,one_mul]
  · rw [pad_outside _ i inside]
    have flag : nullFlag i=false := by simpa only [nullFlag,decide_eq_false_iff_not] using inside
    simp only [flag,Bool.false_eq_true,ite_false,zero_mul]

private theorem pad_injective : Function.Injective nullPad := by
  intro a b same
  simpa only [read_pad] using congrArg nullRead same

/-- Exact original nine initial coordinates and nine constraint coordinates; their row maps differ. -/
def sourceNullCoordinates (p : Fin 4→ℂ) : SignalAmplitude→ₗ[ℂ](Fin 9→ℂ) :=
  nullRead.comp (Matrix.toLin' (originalInverse p))

def sourceNullLift (p : Fin 4→ℂ) : (Fin 9→ℂ)→ₗ[ℂ]SignalAmplitude :=
  (Matrix.toLin' (originalChange p)).comp nullPad

def sourceCokernel (p : Fin 4→ℂ) : SignalAmplitude→ₗ[ℂ](Fin 9→ℂ) :=
  nullRead.comp (Matrix.toLin' (originalReadback p))

theorem source_null_coordinates_generated (p : Fin 4→ℂ) (a : SignalAmplitude) :
    sourceNullLift p (sourceNullCoordinates p a)=sourceNull p*ᵥa := by
  simp only [sourceNullLift,sourceNullCoordinates,LinearMap.comp_apply,Matrix.toLin'_apply,pad_read]
  simp only [sourceNull,←Matrix.mulVec_mulVec]

theorem source_null_lift_coordinates (p : Fin 4→ℂ) (c : Fin 9→ℂ) :
    sourceNullCoordinates p (sourceNullLift p c)=c := by
  simp only [sourceNullLift,sourceNullCoordinates,LinearMap.comp_apply,Matrix.toLin'_apply,
    Matrix.mulVec_mulVec,original_inverse_change,Matrix.one_mulVec,read_pad]

theorem source_null_lift_fixed (p : Fin 4→ℂ) (c : Fin 9→ℂ) :
    sourceNull p*ᵥsourceNullLift p c=sourceNullLift p c := by
  rw [←source_null_coordinates_generated,source_null_lift_coordinates]

theorem source_compatibility_nine (p : Fin 4→ℂ) (a : SignalAmplitude) :
    sourceCompatibility p a=0 ↔ sourceCokernel p a=0 := by
  have exactRows : nullPad (sourceCokernel p a)=sourceCompatibility p a := by
    exact pad_read (originalReadback p*ᵥa)
  rw [←exactRows]
  constructor
  · intro zero
    apply pad_injective
    simpa only [map_zero] using zero
  · intro zero
    rw [zero,map_zero]

/-- The full inverse response with exactly nine original initial-data coordinates. -/
def anchorResponseNine (event : DressedEvent) (T : ℝ) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) : SignalAmplitude :=
  anchorFeedbackResolvent event T*ᵥ((T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥforcing)+
    sourceNullLift anchorInput initial)

private theorem response_nine (event : DressedEvent) (T : ℝ) (forcing initial : SignalAmplitude) :
    anchorResponseNine event T forcing (sourceNullCoordinates anchorInput initial)=anchorResponse event T forcing initial := by
  unfold anchorResponseNine anchorResponse
  rw [source_null_coordinates_generated]

private theorem response_lift (event : DressedEvent) (T : ℝ) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    anchorResponseNine event T forcing initial=anchorResponse event T forcing (sourceNullLift anchorInput initial) := by
  unfold anchorResponseNine anchorResponse
  rw [source_null_lift_fixed]

/-- No Ward vanishing or inverse for this remaining source matrix is assumed. -/
def anchorSchur (event : DressedEvent) (T : ℝ) : Matrix (Fin 9) (Fin 9) ℂ :=
  LinearMap.toMatrix' ((sourceCokernel anchorInput).comp
    ((Matrix.toLin' (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T)).comp
      ((Matrix.toLin' (anchorFeedbackResolvent event T)).comp (sourceNullLift anchorInput))))

def anchorSchurSource (event : DressedEvent) (T : ℝ) (forcing : SignalAmplitude) : Fin 9→ℂ :=
  -sourceCokernel anchorInput (forcing+
    dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥ
      (anchorFeedbackResolvent event T*ᵥ((T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥforcing))))

theorem anchor_schur_generated (event : DressedEvent) (T : ℝ) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    sourceCokernel anchorInput (forcing+dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥ
      anchorResponseNine event T forcing initial)=anchorSchur event T*ᵥinitial-anchorSchurSource event T forcing := by
  rw [anchorSchur,LinearMap.toMatrix'_mulVec]
  simp only [LinearMap.comp_apply,Matrix.toLin'_apply]
  unfold anchorResponseNine anchorSchurSource
  rw [Matrix.mulVec_add,Matrix.mulVec_add,←add_assoc,map_add]
  abel

/-- Every full solution and every source Schur solution return to the same unaveraged finite pencil. -/
theorem anchor_full_solution_schur (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T  ≤  1)
    (forcing a : SignalAmplitude) :
    dressedNativeWindowPencil (anchorEvent event) 0 anchorInput 3 T*ᵥa=forcing ↔
      ∃initial : Fin 9→ℂ,a=anchorResponseNine event T forcing initial ∧
        anchorSchur event T*ᵥinitial=anchorSchurSource event T forcing := by
  rw [anchor_solution_iff event T positive small]
  constructor
  · rintro ⟨initial,rfl,compatible⟩
    refine ⟨sourceNullCoordinates anchorInput initial,(response_nine event T forcing initial).symm,?_⟩
    have nine:=(source_compatibility_nine anchorInput _).mp compatible
    rw [←response_nine event T forcing initial,anchor_schur_generated] at nine
    exact sub_eq_zero.mp nine
  · rintro ⟨initial,rfl,schur⟩
    refine ⟨sourceNullLift anchorInput initial,response_lift event T forcing initial,?_⟩
    apply (source_compatibility_nine anchorInput _).mpr
    rw [anchor_schur_generated,schur,sub_self]

end LowEnergy.GaussComposite.ActualEMDressedSchur
