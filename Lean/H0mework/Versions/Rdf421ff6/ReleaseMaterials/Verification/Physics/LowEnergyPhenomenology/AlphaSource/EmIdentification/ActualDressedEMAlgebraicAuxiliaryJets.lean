import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMCorrectedAuxiliaryFeedback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativePhysicalClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeSchurClock
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMClockDispersion
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

private def auxiliaryAlgebraic (t : NativeJetIndex × NativeJetIndex × ℝ) : Bool :=
  decide ((217 ≤ t.1.2.val → t.1.1=none) ∧ (217 ≤ t.2.1.2.val → t.2.1.1=none))

private theorem actual_algebraic_auxiliary_terms :
    nativeCompleteLiteralTerms.all auxiliaryAlgebraic=true := by decide +kernel

private theorem jet_clock_affine (sign : ℂ) (slot : Option (Fin 4)) (omega : ℝ) (k : PhysicalMomentum) :
    jetSymbol slot (fun mu => sign*physicalFrequencyMomentum omega k mu)=
      jetSymbol slot (fun mu => sign*physicalFrequencyMomentum 0 k mu)+
      (omega : ℂ)*(jetSymbol slot (fun mu => sign*physicalFrequencyMomentum 1 k mu)-
        jetSymbol slot (fun mu => sign*physicalFrequencyMomentum 0 k mu)) := by
  cases slot with
  | none => simp only [jetSymbol,sub_self,mul_zero,add_zero]
  | some mu =>
    refine Fin.cases ?_ (fun i => ?_) mu
    · simp only [jetSymbol,physicalFrequencyMomentum,Fin.cases_zero,Complex.ofReal_zero,Complex.ofReal_one]
      ring1
    · simp only [jetSymbol,physicalFrequencyMomentum,Fin.cases_succ]
      ring1

private def orderedEntry (a b : NativeJetIndex) (h : ℂ) (omega : ℝ) (k : PhysicalMomentum)
    (i j : Fin 289) : ℂ :=
  Matrix.single a.2 b.2 (h*jetSymbol a.1 (-physicalFrequencyMomentum omega k)*
    jetSymbol b.1 (physicalFrequencyMomentum omega k)) i j

private theorem jet_none (p : Fin 4 → ℂ) : jetSymbol none p=1 := rfl

private theorem ordered_clock_affine (a b : NativeJetIndex) (h : ℂ) (omega : ℝ) (k : PhysicalMomentum)
    (i j : Fin 289) (aAlgebraic : 217 ≤ a.2.val → a.1=none) (bAlgebraic : 217 ≤ b.2.val → b.1=none)
    (high : 217 ≤ i.val ∨ 217 ≤ j.val) :
    orderedEntry a b h omega k i j=orderedEntry a b h 0 k i j+
      (omega : ℂ)*(orderedEntry a b h 1 k i j-orderedEntry a b h 0 k i j) := by
  by_cases row : a.2=i
  · by_cases col : b.2=j
    · unfold orderedEntry
      simp only [Matrix.single_apply,row,col,and_self,if_true]
      rcases high with left | right
      · have algebraic : a.1=none := aAlgebraic (by simpa only [row] using left)
        rw [algebraic]
        simp only [jet_none,mul_one]
        change h*jetSymbol b.1 (physicalFrequencyMomentum omega k)=
          h*jetSymbol b.1 (physicalFrequencyMomentum 0 k)+(omega : ℂ)*
            (h*jetSymbol b.1 (physicalFrequencyMomentum 1 k)-h*jetSymbol b.1 (physicalFrequencyMomentum 0 k))
        have affine := jet_clock_affine 1 b.1 omega k
        simp only [one_mul] at affine
        rw [affine]
        ring1
      · have algebraic : b.1=none := bAlgebraic (by simpa only [col] using right)
        rw [algebraic]
        simp only [jet_none,mul_one]
        change h*jetSymbol a.1 (-physicalFrequencyMomentum omega k)=
          h*jetSymbol a.1 (-physicalFrequencyMomentum 0 k)+(omega : ℂ)*
            (h*jetSymbol a.1 (-physicalFrequencyMomentum 1 k)-h*jetSymbol a.1 (-physicalFrequencyMomentum 0 k))
        have affine := jet_clock_affine (-1) a.1 omega k
        have negative (w : ℝ) : (fun mu => -physicalFrequencyMomentum w k mu)=-physicalFrequencyMomentum w k := rfl
        simp only [neg_one_mul,negative] at affine
        rw [affine]
        ring1
    · simp [orderedEntry,row,col]
  · simp [orderedEntry,row]

private theorem literal_clock_affine (terms : List (NativeJetIndex × NativeJetIndex × ℝ))
    (algebraic : terms.all auxiliaryAlgebraic=true) (omega : ℝ) (k : PhysicalMomentum)
    (i j : Fin 289) (high : 217 ≤ i.val ∨ 217 ≤ j.val) :
    nativeLiteralFourier terms (physicalFrequencyMomentum omega k) i j=
      nativeLiteralFourier terms (physicalFrequencyMomentum 0 k) i j+
      (omega : ℂ)*(nativeLiteralFourier terms (physicalFrequencyMomentum 1 k) i j-
        nativeLiteralFourier terms (physicalFrequencyMomentum 0 k) i j) := by
  induction terms with
  | nil => simp [nativeLiteralFourier]
  | cons t terms ih =>
    simp only [List.all_cons,Bool.and_eq_true] at algebraic
    have slots : (217 ≤ t.1.2.val → t.1.1=none) ∧ (217 ≤ t.2.1.2.val → t.2.1.1=none) := by
      simpa only [auxiliaryAlgebraic,decide_eq_true_eq] using algebraic.1
    change orderedEntry t.1 t.2.1 (t.2.2 : ℂ) omega k i j+
      orderedEntry t.2.1 t.1 (t.2.2 : ℂ) omega k i j+
      nativeLiteralFourier terms (physicalFrequencyMomentum omega k) i j=
      (orderedEntry t.1 t.2.1 (t.2.2 : ℂ) 0 k i j+orderedEntry t.2.1 t.1 (t.2.2 : ℂ) 0 k i j+
        nativeLiteralFourier terms (physicalFrequencyMomentum 0 k) i j)+
      (omega : ℂ)*((orderedEntry t.1 t.2.1 (t.2.2 : ℂ) 1 k i j+
        orderedEntry t.2.1 t.1 (t.2.2 : ℂ) 1 k i j+
        nativeLiteralFourier terms (physicalFrequencyMomentum 1 k) i j)-
        (orderedEntry t.1 t.2.1 (t.2.2 : ℂ) 0 k i j+orderedEntry t.2.1 t.1 (t.2.2 : ℂ) 0 k i j+
          nativeLiteralFourier terms (physicalFrequencyMomentum 0 k) i j))
    rw [ordered_clock_affine t.1 t.2.1 _ omega k i j slots.1 slots.2 high,
      ordered_clock_affine t.2.1 t.1 _ omega k i j slots.2 slots.1 high,ih algebraic.2]
    ring1

/-- The complete original action has no derivative of an auxiliary B field; every incident clock entry is affine. -/
theorem actual_native_auxiliary_clock_affine (omega : ℝ) (k : PhysicalMomentum) (i j : Fin 289)
    (high : 217 ≤ i.val ∨ 217 ≤ j.val) :
    emOriginalJacobi (physicalFrequencyMomentum omega k) i j=
      emOriginalJacobi (physicalFrequencyMomentum 0 k) i j+
      (omega : ℂ)*(emOriginalJacobi (physicalFrequencyMomentum 1 k) i j-
        emOriginalJacobi (physicalFrequencyMomentum 0 k) i j) := by
  have source (w : ℝ) : emOriginalJacobi (physicalFrequencyMomentum w k)=
      nativeLiteralFourier nativeCompleteLiteralTerms (physicalFrequencyMomentum w k) := by
    unfold emOriginalJacobi
    rw [em_hessian_source,nativeHessian_complete_literal,nativeLiteralFourier_sound]
  rw [source omega,source 0,source 1]
  exact literal_clock_affine _ actual_algebraic_auxiliary_terms omega k i j high

end LowEnergy.GaussComposite.ActualDressedEMNativeSchurClock
