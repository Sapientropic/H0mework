import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.ProgramCore
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Constant

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram

/-- The two original roots are renamed by the actual shared-code constructor. -/
def Program.share (program : Program) : Program :=
  let generated := Reduce.smartCompact program.code
  let bound := (Reduce.smartCompact_represents program.code (fun _ => false)).2.2.2.1
  ⟨generated.state.code,
    ⟨generated.mapping.getD program.weight.val 0, bound program.weight.val⟩,
    ⟨generated.mapping.getD program.phase.val 0, bound program.phase.val⟩⟩

theorem Program.eval_share (program : Program) (environment : Nat → Bool) :
    program.share.eval environment = program.eval environment := by
  simp only [share, eval, Reduce.smartCompact_reads]

theorem Program.share_forward (program : Program) : Reduce.Forward program.share.code :=
  Reduce.smartCompact_forward program.code

theorem Program.share_size (program : Program) : program.share.code.size ≤ program.code.size + 1 :=
  Reduce.smartCompact_code_size program.code

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram
