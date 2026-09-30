import RequestProject.Watermark.W7
open Watermark

-- The final theorem and its axioms
#check @Watermark.watermark_theorem
#print axioms Watermark.watermark_theorem

-- Every definition needed to read the statement
#print Watermark.Point
#print Watermark.Line
#print Watermark.gramUpper
#print Watermark.gram
#print Watermark.A
#print Watermark.gramLin
#print Watermark.K
#print Watermark.V
#print Watermark.gramForm
#print Watermark.gramFormAux
#print Watermark.formV

-- Non-vacuity: at m = 5 a Z-basis of V exists, the rank is 37, and its Gram determinant is 5^12
example : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℤ (V 5)),
    Fintype.card ι = 37 ∧ (LinearMap.BilinForm.toMatrix b (formV 5)).det = 5 ^ 12 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hF, hr, hd⟩ := watermark_theorem (m := 5) (by norm_num)
  haveI := hF
  classical
  refine ⟨Module.Free.ChooseBasisIndex ℤ (V 5), inferInstance, inferInstance,
    Module.Free.chooseBasis ℤ (V 5), ?_, ?_⟩
  · rw [← Module.finrank_eq_card_chooseBasisIndex, hr]
  · rw [hd]; norm_num
