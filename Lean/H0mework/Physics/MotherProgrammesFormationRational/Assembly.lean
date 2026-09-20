import H0mework.Physics.MotherProgrammesFormationRational.Prefix
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RationalSourceFormation

open StageNineEnrichedProofFreeSource MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

def coframeIndex : (LorentzianIndex × LorentzianIndex × LorentzianIndex) ≃ Fin 64 :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def address (visit : MotherVisit) (slot : Fin 66) : ℕ := unpack 66 (codeOf visit) slot

def sampleVisit (visit : MotherVisit) (slot : Fin 66) : MotherVisit :=
  pastVisit visit (address visit slot)

theorem sample_code (visit : MotherVisit) (slot : Fin 66) :
    codeOf (sampleVisit visit slot) = address visit slot :=
  past_code visit _ (unpack_le _ _ _)

theorem sample_depth_le (visit : MotherVisit) (slot : Fin 66) :
    Stage9C.Revision.temporalDepth (sampleVisit visit slot).history ≤
      Stage9C.Revision.temporalDepth visit.history :=
  past_depth_le visit _

def sampleSource (visit : MotherVisit) (slot : Fin 66) : SmoothUnifiedSource :=
  StageEightDiscreteFormation.sourceAtVisit (sampleVisit visit slot)

def sampleTrace (visit : MotherVisit) (slot : Fin 66) : ℝ := sourceTrace (sampleSource visit slot)

theorem sample_source_readback (visit : MotherVisit) (slot : Fin 66) :
    sampleSource visit slot = toSource (materialAt (address visit slot)) := by
  unfold sampleSource StageEightDiscreteFormation.sourceAtVisit
  rw [sample_code]

theorem sample_source_packed (codes : Fin 66 → ℕ) (slot : Fin 66) :
    sampleSource (Stage9C.Revision.SpinPair.visit (10 + pack codes)) slot =
      StageEightDiscreteFormation.sourceAtVisit (Stage9C.Revision.SpinPair.visit (10 + codes slot)) := by
  rw [sample_source_readback, address, code_at, unpack_pack,
    StageEightDiscreteFormation.sourceAtVisit, code_at]

theorem sample_trace_packed (codes : Fin 66 → ℕ) (slot : Fin 66) :
    sampleTrace (Stage9C.Revision.SpinPair.visit (10 + pack codes)) slot =
      traceAtVisit (Stage9C.Revision.SpinPair.visit (10 + codes slot)) := by
  unfold sampleTrace traceAtVisit
  rw [sample_source_packed]

/-- One bounded historical bundle supplies the complete discrete source and
65 native traces: one contact coordinate and all 64 coframe coefficients. -/
def assembledSource (visit : MotherVisit) : SmoothUnifiedSource :=
  let discrete := sampleSource visit 0
  { discrete with
    stageEight :=
      { discrete.stageEight with
        coframeLinearCoefficient := fun direction row column =>
          sampleTrace visit (coframeIndex (direction, row, column)).succ.succ }
    continuousContactResidual := sampleTrace visit 1 }

theorem discrete_retained (visit : MotherVisit) :
    readMaterial (assembledSource visit) = readMaterial (sampleSource visit 0) := rfl

theorem coframe_rational (visit : MotherVisit) (direction row column : LorentzianIndex) :
    ∃ value : ℚ, (value : ℝ) = (assembledSource visit).stageEight.coframeLinearCoefficient direction row column :=
  ⟨rationalTrace (sampleSource visit (coframeIndex (direction, row, column)).succ.succ),
    rational_trace_cast _⟩

theorem contact_rational (visit : MotherVisit) :
    ∃ value : ℚ, (value : ℝ) = (assembledSource visit).continuousContactResidual :=
  ⟨rationalTrace (sampleSource visit 1), rational_trace_cast _⟩

/-- Coverage compiles the finite integer/rational witnesses into addresses;
the source constructor still reads only the current complete mother prefix. -/
theorem every_rational_source_generated (source : SmoothUnifiedSource)
    (coframe : ∀ direction row column, ∃ value : ℚ,
      (value : ℝ) = source.stageEight.coframeLinearCoefficient direction row column)
    (contact : ∃ value : ℚ, (value : ℝ) = source.continuousContactResidual) :
    ∃ code, assembledSource (Stage9C.Revision.SpinPair.visit (10 + code)) = source := by
  obtain ⟨discreteCode, discreteRead⟩ := every_source_discrete_generated source
  obtain ⟨contactValue, contactValueEq⟩ := contact
  obtain ⟨contactCode, contactRead⟩ := every_rational_generated contactValue
  have coefficientCodes : ∀ slot : Fin 64, ∃ code,
      traceAtVisit (Stage9C.Revision.SpinPair.visit (10 + code)) =
        source.stageEight.coframeLinearCoefficient
          (coframeIndex.symm slot).1 (coframeIndex.symm slot).2.1 (coframeIndex.symm slot).2.2 := by
    intro slot
    obtain ⟨value, valueEq⟩ := coframe
      (coframeIndex.symm slot).1 (coframeIndex.symm slot).2.1 (coframeIndex.symm slot).2.2
    obtain ⟨code, codeEq⟩ := every_rational_generated value
    exact ⟨code, codeEq.trans valueEq⟩
  choose coefficients coefficientRead using coefficientCodes
  let codes : Fin 66 → ℕ := Fin.cons discreteCode (Fin.cons contactCode coefficients)
  refine ⟨pack codes, ?_⟩
  have discrete : sampleSource (Stage9C.Revision.SpinPair.visit (10 + pack codes)) 0 =
      retainReferenceContinuous source := by
    rw [sample_source_packed]
    exact discreteRead
  have coframeRead : (fun direction row column =>
      sampleTrace (Stage9C.Revision.SpinPair.visit (10 + pack codes))
        (coframeIndex (direction, row, column)).succ.succ) = source.stageEight.coframeLinearCoefficient := by
    funext direction row column
    rw [sample_trace_packed]
    simpa only [codes, Fin.cons_succ, Equiv.symm_apply_apply] using
      coefficientRead (coframeIndex (direction, row, column))
  have contactResult : sampleTrace (Stage9C.Revision.SpinPair.visit (10 + pack codes)) 1 =
      source.continuousContactResidual := by
    rw [sample_trace_packed]
    exact contactRead.trans contactValueEq
  unfold assembledSource
  rw [discrete]
  change { source with
    stageEight := { source.stageEight with coframeLinearCoefficient := _ }, continuousContactResidual := _ } = source
  rw [coframeRead, contactResult]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RationalSourceFormation
