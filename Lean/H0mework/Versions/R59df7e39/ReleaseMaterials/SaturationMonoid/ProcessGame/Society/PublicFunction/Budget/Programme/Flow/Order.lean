import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow.Matrix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow

open Distributed

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument) (menu : List Technology)

theorem an_attained_source_envelope_forces_every_material_input_and_output
    (oldDebit newDebit oldCredit newCredit : Party × Good → ℚ)
    (nonnegative : ∀ input,0 ≤ newDebit input)
    (debitOrder : ∀ input,newDebit input ≤ oldDebit input)
    (creditOrder : ∀ output,oldCredit output ≤ newCredit output)
    (envelope : ∀ output,newCredit output ≤ applyMatrix code menu newDebit output)
    (attained : ∀ output,oldCredit output = applyMatrix code menu oldDebit output)
    (visible : ∀ input,oldDebit input = 0 ∨
      ∃ output ∈ Dynamic.Cost.axes code,0 < matrix code menu output input) :
    newDebit = oldDebit ∧ newCredit = oldCredit := by
  have debitExact (input : Party × Good) : newDebit input = oldDebit input := by
    rcases visible input with zero | ⟨output,_,positive⟩
    · exact le_antisymm (debitOrder input) (by rw [zero];exact nonnegative input)
    · have gap : applyMatrix code menu (fun axis => oldDebit axis-newDebit axis) output ≤ 0 := by
        have bound := (creditOrder output).trans (envelope output)
        rw [attained output] at bound
        have subtract : applyMatrix code menu (fun axis => oldDebit axis-newDebit axis) output =
            applyMatrix code menu oldDebit output-applyMatrix code menu newDebit output := by
          unfold applyMatrix
          generalize Dynamic.Cost.axes code = axes
          induction axes with
          | nil => simp
          | cons axis axes ih =>
            simp only [List.map_cons,List.sum_cons,ih]
            simp only [mul_sub]
            ring
        rw [subtract]
        exact sub_nonpos.mpr bound
      have term : matrix code menu output input * (oldDebit input-newDebit input) ≤ 0 := by
        apply le_trans _ gap
        apply List.single_le_sum
        · intro value member
          obtain ⟨axis,_,rfl⟩ := List.mem_map.mp member
          exact mul_nonneg (the_generated_matrix_is_nonnegative code menu output axis) (sub_nonneg.mpr (debitOrder axis))
        · exact List.mem_map.mpr ⟨input,List.mem_flatMap.mpr
            ⟨input.1,code.parties_cover _,List.mem_map.mpr ⟨input.2,code.goods_cover _,rfl⟩⟩,rfl⟩
      have delta : oldDebit input-newDebit input ≤ 0 := by nlinarith
      exact le_antisymm (debitOrder input) (sub_nonpos.mp delta)
  have sameDebit : newDebit = oldDebit := funext debitExact
  refine ⟨sameDebit,funext fun output => le_antisymm ?_ (creditOrder output)⟩
  simpa only [sameDebit,← attained output] using envelope output

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow
