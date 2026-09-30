module

public import RequestProject.Watermark.W6

/-!
# The Watermark Theorem, piece W7: the discriminant of `V`

Throughout, `m` is prime (`[Fact m.Prime]`) and `m ≥ 5`.

* `V m` is torsion-free, hence free, of rank `3(m − 1)(m − 2) + 1` (`V_free`, `finrank_V`).
* `W7.cvec`: the spanning vectors of `F`: for each spanning block `β` the `m − 1` vectors
  `pb β.fam β.pen (δ_x − δ_0)`, `x ≠ 0`, and `famVec m 0`.  Their `B`-Gram matrix `W7.gramC`
  is block diagonal with determinant `m ^ (3(m − 2)(2m − 1) + 3)` (`W7.det_gramC`).
* For a basis `b` of `V`, `gramC = Pᵀ · Gram_b · P` with `P` the matrix of the images of the
  spanning vectors in `b`, and `|det P| = [V : φ(F)] = [A : F + K]` (W6.e).

The final statement is `watermark_theorem`.
-/

@[expose] public section

open Matrix

namespace Watermark

variable {m : ℕ}

/-! ### `V` is free of rank `3(m − 1)(m − 2) + 1` -/

section Free

variable [NeZero m]

instance V_isTorsionFree : Module.IsTorsionFree ℤ (V m) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r v h => ?_
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_K, mulVec_smul,
      smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ((Submodule.Quotient.mk_eq_zero _).mpr (mem_K.mpr h))

/-- `V m` is a free `ℤ`-module. -/
theorem V_free : Module.Free ℤ (V m) := inferInstance

end Free

/-- `rank V = 3(m − 1)(m − 2) + 1`. -/
theorem finrank_V [Fact m.Prime] (hm : 5 ≤ m) :
    Module.finrank ℤ (V m) = 3 * (m - 1) * (m - 2) + 1 := by
  have h := Submodule.finrank_quotient_add_finrank (K m)
  rw [finrank_K hm, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_prod,
    ZMod.card, Fintype.card_fin] at h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  rw [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega]
  have : 9 * (n + 5) - 7 = 9 * n + 38 := by omega
  rw [this] at h
  have h2 : 3 * ((n + 5) * (n + 5)) = 3 * (n + 4) * (n + 3) + 1 + (9 * n + 38) := by ring
  linarith

/-! ### The spanning vectors of `F` and their Gram matrix -/

namespace W7

variable (m) in
/-- Index set of the spanning vectors of `F`: `inl (x, β)` with `x ≠ 0` a point and `β` a
spanning block, and `inr ()` for `famVec m 0`. -/
abbrev CIdx : Type := ({x : ZMod m // x ≠ 0} × FIdx m) ⊕ Unit

/-- The spanning vectors of `F`: `pb β.fam β.pen (δ_x − δ_0)` and `famVec m 0`. -/
def cvec : CIdx m → A m
  | .inl (x, β) => pb β.fam β.pen (W6.dd x.1)
  | .inr _ => famVec m 0

/-- The `B`-Gram matrix of the spanning vectors of `F`. -/
noncomputable def gramC [NeZero m] : Matrix (CIdx m) (CIdx m) ℤ :=
  Matrix.of fun i j => gramForm m (cvec i) (cvec j)

variable [Fact m.Prime]

lemma dd_mem (x : ZMod m) : W6.dd x ∈ sumZero ℤ m := mem_sumZero.mpr (W6.sum_dd x)

lemma gramC_eq (hm : 5 ≤ m) : gramC (m := m) = Matrix.fromBlocks
    (Matrix.blockDiagonal fun _ => (-(m : ℤ) ^ 2) • (1 + Matrix.of fun _ _ => 1)) 0 0
    (Matrix.of fun _ _ => (m : ℤ) ^ 3) := by
  ext (⟨x, β⟩ | i) (⟨y, β'⟩ | j)
  · simp only [gramC, cvec, Matrix.of_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.blockDiagonal_apply]
    split_ifs with h
    · subst h
      rw [gramForm_pb_pb_self hm β (dd_mem x.1) (dd_mem y.1), W6.sum_dd_mul x.2 y.2]
      simp [Matrix.one_apply, Subtype.ext_iff]
    · exact gramForm_pb_pb_of_ne hm h (dd_mem x.1) (dd_mem y.1)
  · simp only [gramC, cvec, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    rw [gramForm_comm, gramForm_famVec_pb _ _ (dd_mem x.1)]
  · simp only [gramC, cvec, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [gramForm_famVec_pb _ _ (dd_mem y.1)]
  · simp only [gramC, cvec, Matrix.of_apply, Matrix.fromBlocks_apply₂₂]
    exact gramForm_famVec_self

lemma det_gramC (hm : 5 ≤ m) :
    (gramC (m := m)).det = (m : ℤ) ^ (3 * (m - 2) * (2 * m - 1) + 3) := by
  rw [gramC_eq hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.det_blockDiagonal]
  have hJ : (Matrix.of fun _ _ => 1 : Matrix {x : ZMod m // x ≠ 0} {x : ZMod m // x ≠ 0} ℤ) =
      Matrix.replicateCol Unit (fun _ => (1 : ℤ)) * Matrix.replicateRow Unit (fun _ => (1 : ℤ)) := by
    ext a b; simp [Matrix.mul_apply]
  have h1 : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  have heven : Even (m - 1) := Nat.Odd.sub_odd (W4.odd_of_prime_of_five_le hm) odd_one
  have hdet : ((-(m : ℤ) ^ 2) • (1 + Matrix.of fun _ _ => 1 :
      Matrix {x : ZMod m // x ≠ 0} {x : ZMod m // x ≠ 0} ℤ)).det = (m : ℤ) ^ (2 * m - 1) := by
    rw [Matrix.det_smul, hJ, Matrix.det_one_add_replicateCol_mul_replicateRow, W6.card_ne_zero]
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, W6.card_ne_zero,
      nsmul_eq_mul]
    rw [Nat.cast_sub h1, Nat.cast_one, show (1 : ℤ) + ((m : ℤ) - 1) = m by ring,
      heven.neg_pow, ← pow_mul, ← pow_succ]
    congr 1
    omega
  simp only [hdet, Finset.prod_const, Finset.card_univ, W6.card_FIdx hm, Matrix.of_apply]
  rw [← pow_mul, ← pow_add]
  congr 1
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  rw [show n + 5 - 3 = n + 2 by omega, show n + 5 - 2 = n + 3 by omega,
    show 2 * (n + 5) - 1 = 2 * n + 9 by omega]
  ring

lemma det_gramC_ne_zero (hm : 5 ≤ m) : (gramC (m := m)).det ≠ 0 := by
  rw [det_gramC hm]; exact pow_ne_zero _ (by exact_mod_cast NeZero.ne m)

lemma card_CIdx (hm : 5 ≤ m) : Fintype.card (CIdx m) = 3 * (m - 1) * (m - 2) + 1 := by
  rw [Fintype.card_sum, Fintype.card_prod, W6.card_ne_zero, W6.card_FIdx hm, Fintype.card_unit]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  rw [show n + 5 - 3 = n + 2 by omega, show n + 5 - 2 = n + 3 by omega,
    show n + 5 - 1 = n + 4 by omega]
  ring

lemma span_cvec : Submodule.span ℤ (Set.range (cvec (m := m))) = F m := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨x, β⟩ | _, rfl⟩
    · exact Submodule.mem_sup_left (Submodule.mem_iSup_of_mem β ⟨W6.dd x.1, dd_mem x.1, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  · refine sup_le (iSup_le fun β => ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : u = ∑ x : {x : ZMod m // x ≠ 0}, u x • W6.dd x.1 := funext fun v => by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact (W6.sum_mul_dd hu v).symm
      rw [hu', map_sum]
      exact Submodule.sum_mem _ fun x _ => by
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (x, β), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ rfl
      exact Submodule.subset_span ⟨.inr (), rfl⟩

/-- The images of the spanning vectors in `V`. -/
noncomputable def cV (i : CIdx m) : V m := (K m).mkQ (cvec i)

lemma gramC_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ (V m)) :
    gramC (m := m) = (b.toMatrix cV)ᵀ * LinearMap.BilinForm.toMatrix b (formV m) *
      b.toMatrix cV := by
  ext i j
  simp only [gramC, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Module.Basis.toMatrix_apply]
  rw [← formV_mkQ, LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b]
  simp only [dotProduct, mulVec, cV, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma cV_linearIndependent (hm : 5 ≤ m) : LinearIndependent ℤ (cV (m := m)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : c ᵥ* gramC = 0 := by
    funext j
    have := congrArg (fun v => formV m v (cV j)) hc
    simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      map_zero, LinearMap.zero_apply, smul_eq_mul] at this
    simpa [Matrix.vecMul, dotProduct, gramC, cV, formV_mkQ] using this
  exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero (det_gramC_ne_zero hm) hv) i

lemma span_cV : Submodule.span ℤ (Set.range (cV (m := m))) = (F m).map (K m).mkQ := by
  rw [show (cV (m := m)) = (K m).mkQ ∘ cvec from rfl, Set.range_comp, Submodule.span_image,
    span_cvec]

lemma index_map_F (hm : 5 ≤ m) :
    ((F m).map (K m).mkQ).toAddSubgroup.index = m ^ (3 * (m ^ 2 + m + 2) / 2 - 12) := by
  rw [← index_F_sup_K hm, sup_comm, ← Submodule.comap_map_mkQ]
  exact (AddSubgroup.index_comap_of_surjective (H := ((F m).map (K m).mkQ).toAddSubgroup)
    (f := ((K m).mkQ : A m →+ V m)) (Submodule.mkQ_surjective _)).symm

lemma exponent_eq (hm : 5 ≤ m) :
    3 * (m - 2) * (2 * m - 1) + 3 = 2 * (3 * (m ^ 2 + m + 2) / 2 - 12) + 3 * (m - 3) ^ 2 := by
  obtain ⟨k, hk⟩ := W6.even_exp (m := m)
  rw [hk, show 3 * (2 * k) / 2 = 3 * k by omega]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  have hk' : 2 * k = n ^ 2 + 11 * n + 32 := by rw [← hk]; ring
  rw [show n + 5 - 3 = n + 2 by omega, show n + 5 - 2 = n + 3 by omega,
    show 2 * (n + 5) - 1 = 2 * n + 9 by omega, show 2 * (3 * k - 12) = 3 * (2 * k) - 24 by omega,
    hk']
  have : 24 ≤ 3 * (n ^ 2 + 11 * n + 32) := by nlinarith
  zify [this]
  ring

/-- The discriminant for bases indexed by `CIdx m`. -/
lemma det_toMatrix_CIdx (hm : 5 ≤ m) (b : Module.Basis (CIdx m) ℤ (V m)) :
    (LinearMap.BilinForm.toMatrix b (formV m)).det = (m : ℤ) ^ (3 * (m - 3) ^ 2) := by
  set bN := Module.Basis.span (cV_linearIndependent hm)
  have hidx := Submodule.natAbs_det_basis_change b _ bN
  have hcoe : ((↑) ∘ bN : CIdx m → V m) = cV := funext fun i => Module.Basis.span_apply _ i
  have hcard : Nat.card (V m ⧸ Submodule.span ℤ (Set.range (cV (m := m)))) =
      m ^ (3 * (m ^ 2 + m + 2) / 2 - 12) := by
    rw [span_cV]; exact index_map_F hm
  rw [hcoe, Module.Basis.det_apply, hcard] at hidx
  have hG := congrArg Matrix.det (gramC_eq_mul b)
  rw [det_mul, det_mul, det_transpose, det_gramC hm, exponent_eq hm, pow_add, pow_mul] at hG
  have hP : (b.toMatrix cV).det * (b.toMatrix cV).det = ((m : ℤ) ^ 2) ^
      (3 * (m ^ 2 + m + 2) / 2 - 12) := by
    rw [← Int.natAbs_mul_self, hidx, ← mul_pow]; push_cast; ring
  have hne : ((m : ℤ) ^ 2) ^ (3 * (m ^ 2 + m + 2) / 2 - 12) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast NeZero.ne m))
  refine (mul_left_cancel₀ hne ?_).symm
  rw [hG, ← hP]
  ring

end W7

open W7

/-- **(W7.main) The Watermark Theorem.** For `m` prime, `m ≥ 5`: `V m` is a free `ℤ`-module of
rank `3(m − 1)(m − 2) + 1`, and for every `ℤ`-basis `b` of `V m` the Gram determinant of the
induced form `formV m` in `b` is `m ^ (3(m − 3)²)`. -/
theorem watermark_theorem [Fact m.Prime] (hm : 5 ≤ m) :
    Module.Free ℤ (V m) ∧ Module.finrank ℤ (V m) = 3 * (m - 1) * (m - 2) + 1 ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ (V m)),
        (LinearMap.BilinForm.toMatrix b (formV m)).det = (m : ℤ) ^ (3 * (m - 3) ^ 2) := by
  refine ⟨V_free, finrank_V hm, fun {ι} _ _ b => ?_⟩
  have hc : Fintype.card (CIdx m) = Fintype.card ι := by
    rw [card_CIdx hm, ← finrank_V hm, Module.finrank_eq_card_basis b]
  set e : CIdx m ≃ ι := Fintype.equivOfCardEq hc
  have h := det_toMatrix_CIdx hm (b.reindex e.symm)
  have he : LinearMap.BilinForm.toMatrix (b.reindex e.symm) (formV m) =
      (LinearMap.BilinForm.toMatrix b (formV m)).submatrix e e := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [he, Matrix.det_submatrix_equiv_self] at h
  exact h

end Watermark
