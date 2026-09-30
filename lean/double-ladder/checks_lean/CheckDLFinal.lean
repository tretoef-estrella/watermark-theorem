import RequestProject.DoubleLadder.DL3
open Watermark DoubleLadder

-- The two final theorems and their axioms
#check @DoubleLadder.double_ladder_theorem
#check @DoubleLadder.double_ladder_five
#print axioms DoubleLadder.double_ladder_theorem
#print axioms DoubleLadder.double_ladder_five

-- The one new definition needed to read the statements (the rest are the Watermark's)
#print DoubleLadder.D
#print DoubleLadder.ylad

-- The main intermediate theorems
#check @DoubleLadder.gram_mul_ylad_mul_gram
#check @DoubleLadder.exists_formV_eq_smul
#check @DoubleLadder.rank_gram_map
#check @DoubleLadder.rank_gram_map_five
#print axioms DoubleLadder.gram_mul_ylad_mul_gram
#print axioms DoubleLadder.rank_gram_map
#print axioms DoubleLadder.rank_gram_map_five

-- Non-vacuity: the theorem instantiated at m = 7, 11, 13, with the exponents computed.
-- These are the profiles of Aljovin-Movasati-Villaflor, Table 1, rows (2,7), (2,11), (2,13).
example : Nonempty (D 7 ≃+ ((Fin 38 → ZMod 7) × (Fin 5 → ZMod (7 ^ 2)))) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact double_ladder_theorem 7 (by norm_num)

example : Nonempty (D 11 ≃+ ((Fin 158 → ZMod 11) × (Fin 17 → ZMod (11 ^ 2)))) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact double_ladder_theorem 11 (by norm_num)

example : Nonempty (D 13 ≃+ ((Fin 254 → ZMod 13) × (Fin 23 → ZMod (13 ^ 2)))) := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact double_ladder_theorem 13 (by norm_num)
