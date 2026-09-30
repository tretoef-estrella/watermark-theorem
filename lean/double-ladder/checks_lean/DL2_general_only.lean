

import RequestProject.DoubleLadder.DL1

/-!
# The Double Ladder Theorem, piece DL2: the rank of the Gram matrix modulo `m`

We define the four pencils `pen4`, the shadow matrix `shadow m`, the pairing matrix `gam m` and
the one-family relation map `relMap m`, and prove
* (DL2.a) `gram_eq_shadow`: `G = Sᵀ Γ S − m • 1`;
* (DL2.b) `ker_relMap_eq_span`, `finrank_ker_relMap`: the kernel of `relMap` is spanned by the
  six relations `rel m`, and has dimension `6`;
* (DL2.c) `sum_mul_shift_eq_zero`: pairings of quadratics vanish for `m ≥ 7`;
* (DL2.main) `rank_gram_map`: `rank (G mod m) = 12 (m − 3)` for `m ≥ 7` prime;
* (DL2.basis) `rank_toMatrix_map`: the same rank for the Gram matrix of `formV m` in any basis;
* (DL2.five) `rank_gram_map_five`: for `m = 5` the rank is `26` (checked by certificates).
-/



open Matrix Watermark

namespace DoubleLadder

/-- The four pencils `k`, `l`, `k − l`, `k + l` on a point `p = (k, l)`. -/
def pen4 {m : ℕ} : Fin 4 → Point m → ZMod m
  | 0 => fun p => p.1
  | 1 => fun p => p.2
  | 2 => fun p => p.1 - p.2
  | 3 => fun p => p.1 + p.2

/-- Slots `(j, i, x)`: a family `j`, one of its four pencils `i`, and a value `x`. -/
abbrev Slot (m : ℕ) : Type := Fin 3 × Fin 4 × ZMod m

/-- The shadow matrix: row `(j, i, x)` is the indicator of the fibre `{pen4 i = x}` of
family `j`. -/
def shadow (m : ℕ) : Matrix (Slot m) (Line m) ℤ :=
  Matrix.of fun s q => if q.1 = s.1 ∧ pen4 s.2.1 q.2 = s.2.2 then 1 else 0

/-- The pairing matrix `Γ` on slots. -/
def gam (m : ℕ) : Matrix (Slot m) (Slot m) ℤ :=
  Matrix.of fun s s' =>
    if (s.1 = s'.1 ∧ s.2.1 = s'.2.1 ∧ (s.2.1 = 0 ∨ s.2.1 = 1) ∧ s.2.2 = s'.2.2) ∨
       ((((s.1, s.2.1) = (0, 2) ∧ (s'.1, s'.2.1) = (1, 2)) ∨
         ((s.1, s.2.1) = (1, 2) ∧ (s'.1, s'.2.1) = (0, 2))) ∧ s.2.2 = s'.2.2) ∨
       ((((s.1, s.2.1) = (1, 3) ∧ (s'.1, s'.2.1) = (2, 3)) ∨
         ((s.1, s.2.1) = (2, 3) ∧ (s'.1, s'.2.1) = (1, 3))) ∧ s.2.2 = s'.2.2) ∨
       ((s.1, s.2.1, s'.1, s'.2.1) = (0, 3, 2, 2) ∧ s'.2.2 = s.2.2 + 1) ∨
       ((s.1, s.2.1, s'.1, s'.2.1) = (2, 2, 0, 3) ∧ s.2.2 = s'.2.2 + 1)
    then 1 else 0

/-- The one-family relation map `h ↦ (p ↦ Σ_i h i (pen4 i p))`, over `ZMod m`. -/
def relMap (m : ℕ) : (Fin 4 → ZMod m → ZMod m) →ₗ[ZMod m] (Point m → ZMod m) where
  toFun h p := ∑ i, h i (pen4 i p)
  map_add' h h' := by
    funext p
    simp [Finset.sum_add_distrib]
  map_smul' c h := by
    funext p
    simp [Finset.mul_sum]

/-- The six relations `(h 0, h 1, h 2, h 3)` spanning the kernel of `relMap`. -/
def rel (m : ℕ) : Fin 6 → Fin 4 → ZMod m → ZMod m :=
  ![![fun _ => 1, fun _ => -1, fun _ => 0, fun _ => 0],
    ![fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 0],
    ![fun _ => 1, fun _ => 0, fun _ => 0, fun _ => -1],
    ![fun x => x, fun x => -x, fun x => -x, fun _ => 0],
    ![fun x => x, fun x => x, fun _ => 0, fun x => -x],
    ![fun x => -2 * x ^ 2, fun x => -2 * x ^ 2, fun x => x ^ 2, fun x => x ^ 2]]

namespace DL2

variable {m : ℕ}

/-- The partner of a pencil index `(j, i)` under `Γ`. -/
def pIdx (a : Fin 3 × Fin 4) : Fin 3 × Fin 4 :=
  if a = (0, 2) then (1, 2) else if a = (1, 2) then (0, 2)
  else if a = (1, 3) then (2, 3) else if a = (2, 3) then (1, 3)
  else if a = (0, 3) then (2, 2) else if a = (2, 2) then (0, 3) else a

/-- The shift of the value under `Γ`. -/
def pShift (a : Fin 3 × Fin 4) : ZMod m :=
  if a = (0, 3) then 1 else if a = (2, 2) then -1 else 0

/-- The involution of slots described by `Γ`. -/
def partner (s : Slot m) : Slot m :=
  ((pIdx (s.1, s.2.1)).1, (pIdx (s.1, s.2.1)).2, s.2.2 + pShift (s.1, s.2.1))

lemma gam_apply (s s' : Slot m) : gam m s s' = if s' = partner s then 1 else 0 := by
  obtain ⟨j, i, x⟩ := s
  obtain ⟨j', i', y⟩ := s'
  simp only [gam, of_apply]
  refine if_congr ?_ rfl rfl
  simp only [partner, pIdx, pShift, Prod.ext_iff]
  fin_cases j <;> fin_cases i <;> simp
  all_goals grind

lemma partner_partner (s : Slot m) : partner (partner s) = s := by
  obtain ⟨j, i, x⟩ := s
  simp only [partner, pIdx, pShift]
  fin_cases j <;> fin_cases i <;> simp

lemma eq_partner_comm {s s' : Slot m} : s' = partner s ↔ s = partner s' := by
  constructor <;> rintro rfl <;> rw [partner_partner]

end DL2

open DL2

/-- `Γ` is symmetric. -/
theorem gam_transpose (m : ℕ) : (gam m)ᵀ = gam m := by
  ext s s'
  simp only [transpose_apply, gam_apply, eq_partner_comm (s := s')]

/-- `Γ² = 1`. -/
theorem gam_mul_gam (m : ℕ) [NeZero m] : gam m * gam m = 1 := by
  ext s s'
  simp only [mul_apply, gam_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, partner_partner, one_apply, eq_comm]

namespace DL2

variable {m : ℕ}

lemma sum_shadow_mul {R : Type*} [CommRing R] [NeZero m] (q : Line m) (φ : Slot m → R) :
    ∑ s, ((shadow m s q : ℤ) : R) * φ s = ∑ i, φ (q.1, i, pen4 i q.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single q.1]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [shadow]
  · intro j _ hj
    simp [shadow, Ne.symm hj]
  · simp

lemma shadowT_gam_shadow_apply [NeZero m] (p q : Line m) :
    ((shadow m)ᵀ * gam m * shadow m) p q =
      ∑ i', ∑ i, gam m (p.1, i, pen4 i p.2) (q.1, i', pen4 i' q.2) := by
  rw [mul_apply]
  have h1 : ∀ s', ((shadow m)ᵀ * gam m) p s' = ∑ i, gam m (p.1, i, pen4 i p.2) s' := by
    intro s'
    rw [mul_apply]
    simpa using sum_shadow_mul (R := ℤ) p (fun s => gam m s s')
  simp only [h1]
  have := sum_shadow_mul (R := ℤ) q (fun s' => ∑ i, gam m (p.1, i, pen4 i p.2) s')
  simp only [Int.cast_id] at this
  rw [← this]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end DL2

/-- **(DL2.a) The shadow factorization.** -/
theorem gram_eq_shadow (m : ℕ) [NeZero m] :
    gram m = (shadow m)ᵀ * gam m * shadow m - (m : ℤ) • 1 := by
  ext ⟨j, a⟩ ⟨j', b⟩
  rw [sub_apply, smul_apply, one_apply, shadowT_gam_shadow_apply]
  simp only [gam_apply, partner, pIdx, pShift, Fin.sum_univ_four, pen4, Prod.ext_iff]
  fin_cases j <;> fin_cases j' <;> simp [Watermark.gram, gramUpper]
  all_goals
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only [Prod.mk.injEq] at *
    split_ifs <;> grind

/-- The relations lie in the kernel of `relMap`. -/
theorem rel_mem_ker (m : ℕ) (k : Fin 6) : rel m k ∈ LinearMap.ker (relMap m) := by
  rw [LinearMap.mem_ker]
  funext p
  fin_cases k <;> simp [relMap, rel, Fin.sum_univ_four, pen4] <;> ring

lemma DL2.relMap_apply {m : ℕ} (h : Fin 4 → ZMod m → ZMod m) (p : Point m) :
    relMap m h p = ∑ i, h i (pen4 i p) := rfl

/-- The six relations are linearly independent. -/
theorem rel_linearIndependent (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) :
    LinearIndependent (ZMod m) (rel m) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have H : ∀ i x, ∑ k, g k * rel m k i x = 0 := fun i x => by
    simpa using congrFun (congrFun hg i) x
  have h2 := LemmaC.two_ne_zero hm
  have e10 := H 1 0
  have e20 := H 2 0
  have e30 := H 3 0
  have e21 := H 2 1
  have e2m := H 2 (-1)
  have e31 := H 3 1
  simp [Fin.sum_univ_six, rel] at e10 e20 e30 e21 e2m e31
  have g5 : g 5 = 0 := by
    have : 2 * g 5 = 0 := by linear_combination e21 + e2m + 2 * e20
    exact (mul_eq_zero.mp this).resolve_left h2
  intro k
  fin_cases k <;> simp
  · exact e10
  · exact e20
  · exact e30
  · linear_combination -e21 - e20 + g5
  · linear_combination -e31 - e30 + g5
  · exact g5

lemma DL2.mem_span_rel_of_mem_ker {m : ℕ} [Fact m.Prime] (hm : 5 ≤ m)
    {h : Fin 4 → ZMod m → ZMod m} (hh : h ∈ LinearMap.ker (relMap m)) :
    h ∈ Submodule.span (ZMod m) (Set.range (rel m)) := by
  have hΦ : ∀ k l, h 0 k + h 1 l + h 2 (k - l) + h 3 (k + l) = 0 := fun k l => by
    have := congrFun (LinearMap.mem_ker.mp hh) (k, l)
    simpa [DL2.relMap_apply, Fin.sum_univ_four, pen4, add_assoc] using this
  have sd := LemmaC.secondDiff_eq hm hΦ
  have h2 := LemmaC.two_ne_zero hm
  obtain ⟨c, hc3, hc2⟩ : ∃ c, (∀ x, LemmaC.secondDiff (h 3) x = 2 * c) ∧
      ∀ x, LemmaC.secondDiff (h 2) x = 2 * c := by
    refine ⟨LemmaC.secondDiff (h 3) 0 / 2, fun x => ?_, fun x => ?_⟩
    · rw [sd x 0, ← sd 0 0]; field_simp
    · rw [← sd 0 x]; field_simp
  have q3 := LemmaC.eq_quad_of_secondDiff hc3
  have q2 := LemmaC.eq_quad_of_secondDiff hc2
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨![-h 1 0, -h 2 0, -h 3 0, -(h 2 1 - h 2 0 - c), -(h 3 1 - h 3 0 - c), c], ?_⟩
  funext i x
  have ex0 := hΦ x 0
  have e0x := hΦ 0 x
  have e00 := hΦ 0 0
  simp only [sub_zero, add_zero, zero_sub, zero_add] at ex0 e0x e00
  fin_cases i <;> simp [Fin.sum_univ_six, rel]
  · linear_combination -ex0 + q2 x + q3 x
  · linear_combination -e0x + e00 + q2 (-x) + q3 x - q2 0 - q3 0
  · linear_combination -q2 x
  · linear_combination -q3 x

/-- **(DL2.b)** The kernel of `relMap` is spanned by the six relations. -/
theorem ker_relMap_eq_span (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) :
    LinearMap.ker (relMap m) = Submodule.span (ZMod m) (Set.range (rel m)) := by
  refine le_antisymm (fun h hh => DL2.mem_span_rel_of_mem_ker hm hh) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact rel_mem_ker m k

/-- **(DL2.b)** The kernel of `relMap` has dimension `6`. -/
theorem finrank_ker_relMap (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) :
    Module.finrank (ZMod m) (LinearMap.ker (relMap m)) = 6 := by
  rw [ker_relMap_eq_span m hm, finrank_span_eq_card (rel_linearIndependent m hm)]
  simp

/-- **(DL2.c) Quadratic pairings vanish.** -/
theorem sum_mul_shift_eq_zero (m : ℕ) [Fact m.Prime] (hm : 7 ≤ m) {f g : ZMod m → ZMod m}
    (hf : ∃ a b c : ZMod m, ∀ x, f x = a + b * x + c * x ^ 2)
    (hg : ∃ a b c : ZMod m, ∀ x, g x = a + b * x + c * x ^ 2) (e : ZMod m) :
    ∑ x, f x * g (x + e) = 0 := by
  obtain ⟨a, b, c, hf⟩ := hf
  obtain ⟨a', b', c', hg⟩ := hg
  have hs : ∀ i ≤ 4, ∑ x : ZMod m, x ^ i = 0 := fun i hi =>
    FiniteField.sum_pow_lt_card_sub_one (ZMod m) i (by rw [ZMod.card]; omega)
  set A0 := a' + b' * e + c' * e ^ 2
  set A1 := b' + 2 * c' * e
  have key : ∀ x, f x * g (x + e) = a * A0 * x ^ 0 + (a * A1 + b * A0) * x ^ 1 +
      (a * c' + b * A1 + c * A0) * x ^ 2 + (b * c' + c * A1) * x ^ 3 + c * c' * x ^ 4 := by
    intro x
    rw [hf, hg]
    ring
  rw [Finset.sum_congr rfl fun x _ => key x]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs 0 (by norm_num), hs 1 (by norm_num),
    hs 2 (by norm_num), hs 3 (by norm_num), hs 4 (by norm_num), mul_zero, add_zero]

namespace DL2

/-- The orthogonal complement of a subspace of `n → F` for the dot product. -/
def orth {n F : Type*} [Fintype n] [Field F] (R : Submodule F (n → F)) :
    Submodule F (n → F) where
  carrier := {u | ∀ r ∈ R, u ⬝ᵥ r = 0}
  add_mem' hu hv r hr := by rw [add_dotProduct, hu r hr, hv r hr, add_zero]
  zero_mem' r _ := zero_dotProduct r
  smul_mem' c u hu r hr := by rw [smul_dotProduct, hu r hr, smul_zero]

lemma finrank_orth_add_le {n F : Type*} [Fintype n] [DecidableEq n] [Field F]
    (R : Submodule F (n → F)) :
    Module.finrank F (orth R) + Module.finrank F R ≤ Fintype.card n := by
  set d := Module.finrank F R
  let b := Module.finBasis F R
  let M : Matrix (Fin d) n F := Matrix.of fun k => (b k : n → F)
  have hle : orth R ≤ LinearMap.ker M.mulVecLin := by
    intro u hu
    rw [LinearMap.mem_ker]
    funext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, Pi.zero_apply]
    rw [dotProduct_comm]
    exact hu _ (b k).2
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∑ k, c k • b k = 0 := by
      apply Subtype.ext
      simpa [Matrix.mulVecLin_apply, mulVec_transpose, vecMul_eq_sum, M] using hc
    funext k
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) c h0 k
  have hrank : Module.finrank F (LinearMap.range M.mulVecLin) = d := by
    have h1 := rank_transpose M
    rw [Matrix.rank, Matrix.rank, LinearMap.finrank_range_of_inj hinj] at h1
    simp at h1
    exact h1.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have := Submodule.finrank_mono hle
  omega

variable {m : ℕ}

/-- The shadow matrix reduced modulo `m`. -/
def Sb (m : ℕ) : Matrix (Slot m) (Line m) (ZMod m) := (shadow m).map (Int.castRingHom (ZMod m))

/-- The pairing matrix reduced modulo `m`. -/
def Gb (m : ℕ) : Matrix (Slot m) (Slot m) (ZMod m) := (gam m).map (Int.castRingHom (ZMod m))

variable [NeZero m]

lemma shadowT_mulVec (u : Slot m → ZMod m) (j : Fin 3) (p : Point m) :
    ((Sb m)ᵀ *ᵥ u) (j, p) = relMap m (fun i x => u (j, i, x)) p := by
  simp only [mulVec, dotProduct, transpose_apply, Sb, map_apply, Int.coe_castRingHom]
  exact sum_shadow_mul (j, p) u

lemma gam_mulVec (u : Slot m → ZMod m) : Gb m *ᵥ u = fun s => u (partner s) := by
  funext s
  simp [mulVec, dotProduct, Gb, gam_apply]

/-- The kernel `R` of `S̄ᵀ`. -/
def Rk (m : ℕ) [NeZero m] : Submodule (ZMod m) (Slot m → ZMod m) :=
  LinearMap.ker (Sb m)ᵀ.mulVecLin

lemma mem_Rk_iff {u : Slot m → ZMod m} :
    u ∈ Rk m ↔ ∀ j, (fun i x => u (j, i, x)) ∈ LinearMap.ker (relMap m) := by
  rw [Rk, LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro h j
    rw [LinearMap.mem_ker]
    funext p
    rw [← shadowT_mulVec, h]
    rfl
  · intro h
    funext ⟨j, p⟩
    rw [shadowT_mulVec]
    exact congrFun (LinearMap.mem_ker.mp (h j)) p

omit [NeZero m] in
lemma quad_of_mem_ker [Fact m.Prime] (hm : 5 ≤ m) {h : Fin 4 → ZMod m → ZMod m}
    (hh : h ∈ LinearMap.ker (relMap m)) (i : Fin 4) :
    ∃ a b c : ZMod m, ∀ x, h i x = a + b * x + c * x ^ 2 := by
  obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    (mem_span_rel_of_mem_ker hm hh)
  fin_cases i
  · refine ⟨g 0 + g 1 + g 2, g 3 + g 4, -2 * g 5, fun x => ?_⟩
    simp [Fin.sum_univ_six, rel]; ring
  · refine ⟨-g 0, -g 3 + g 4, -2 * g 5, fun x => ?_⟩
    simp [Fin.sum_univ_six, rel]; ring
  · refine ⟨-g 1, -g 3, g 5, fun x => ?_⟩
    simp [Fin.sum_univ_six, rel]
  · refine ⟨-g 2, -g 4, g 5, fun x => ?_⟩
    simp [Fin.sum_univ_six, rel]

lemma pairing_eq_zero [Fact m.Prime] (hm : 7 ≤ m) {r r' : Slot m → ZMod m} (hr : r ∈ Rk m)
    (hr' : r' ∈ Rk m) : (Gb m *ᵥ r) ⬝ᵥ r' = 0 := by
  have quad : ∀ {u : Slot m → ZMod m}, u ∈ Rk m → ∀ j i,
      ∃ a b c : ZMod m, ∀ x, u (j, i, x) = a + b * x + c * x ^ 2 := fun hu j i =>
    quad_of_mem_ker (by omega) (mem_Rk_iff.mp hu j) i
  rw [gam_mulVec]
  simp only [dotProduct]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [partner]
  rw [Finset.sum_congr rfl fun x _ => mul_comm _ _]
  exact sum_mul_shift_eq_zero m hm (quad hr' j i) (quad hr _ _) _

/-- The eighteen relation vectors: relation `k` placed on family `j`. -/
def relVec (m : ℕ) (jk : Fin 3 × Fin 6) : Slot m → ZMod m :=
  fun s => if s.1 = jk.1 then rel m jk.2 s.2.1 s.2.2 else 0

lemma relVec_mem (jk : Fin 3 × Fin 6) : relVec m jk ∈ Rk m := by
  rw [mem_Rk_iff]
  intro j
  by_cases h : j = jk.1
  · have : (fun i x => relVec m jk (j, i, x)) = rel m jk.2 := by
      funext i x; simp [relVec, h]
    rw [this]
    exact rel_mem_ker m _
  · have : (fun i x => relVec m jk (j, i, x)) = 0 := by
      funext i x; simp [relVec, h]
    rw [this]
    exact Submodule.zero_mem _

omit [NeZero m] in
lemma relVec_linearIndependent [Fact m.Prime] (hm : 5 ≤ m) :
    LinearIndependent (ZMod m) (relVec m) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg ⟨j, k⟩
  have h0 : ∑ k, g (j, k) • rel m k = 0 := by
    funext i x
    have := congrFun hg (j, i, x)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      relVec, mul_ite, mul_zero, Pi.zero_apply] at this ⊢
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  exact (Fintype.linearIndependent_iff.mp (rel_linearIndependent m hm)) _ h0 k

lemma Rk_eq_span [Fact m.Prime] (hm : 5 ≤ m) :
    Rk m = Submodule.span (ZMod m) (Set.range (relVec m)) := by
  refine le_antisymm (fun u hu => ?_) ?_
  · choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun _).mp
      (mem_span_rel_of_mem_ker hm (mem_Rk_iff.mp hu j))
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun jk => c jk.1 jk.2, ?_⟩
    funext ⟨j, i, x⟩
    have := congrFun (congrFun (hc j) i) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · simp [relVec]
    · intro b _ hb
      simp [relVec, Ne.symm hb]
    · simp
  · rw [Submodule.span_le]
    rintro _ ⟨jk, rfl⟩
    exact relVec_mem jk

lemma finrank_Rk [Fact m.Prime] (hm : 5 ≤ m) : Module.finrank (ZMod m) (Rk m) = 18 := by
  rw [Rk_eq_span hm, finrank_span_eq_card (relVec_linearIndependent hm)]
  simp

end DL2

/-- **(DL2.main) The rank of `G` modulo `m`.** -/
theorem rank_gram_map (m : ℕ) [Fact m.Prime] (hm : 7 ≤ m) :
    ((gram m).map (Int.castRingHom (ZMod m))).rank = 12 * (m - 3) := by
  have hm5 : 5 ≤ m := by omega
  set f := Int.castRingHom (ZMod m)
  -- `Ḡ = S̄ᵀ Γ̄ S̄`
  have hsm : ((m : ℤ) • (1 : Matrix (Line m) (Line m) ℤ)).map f = 0 := by
    ext p q
    rw [map_apply, smul_apply, one_apply]
    split_ifs <;> simp [f]
  have hGbar : (gram m).map f = (Sb m)ᵀ * Gb m * Sb m := by
    rw [gram_eq_shadow m, ← RingHom.mapMatrix_apply, map_sub, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, hsm, sub_zero, Matrix.map_mul, Matrix.map_mul, transpose_map]
    rfl
  -- `Γ̄² = 1`
  have hGG : Gb m * Gb m = 1 := by
    rw [Gb, ← RingHom.mapMatrix_apply, ← map_mul, gam_mul_gam, map_one]
  have hcardU : Module.finrank (ZMod m) (Slot m → ZMod m) = 12 * m := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [ZMod.card]
    ring
  set W := LinearMap.range (Sb m).mulVecLin
  set Fm := ((Sb m)ᵀ * Gb m).mulVecLin
  have hR := finrank_Rk hm5
  -- rank of `S̄ᵀ`
  have hT : Module.finrank (ZMod m) (LinearMap.range (Sb m)ᵀ.mulVecLin) + 18 = 12 * m := by
    have := LinearMap.finrank_range_add_finrank_ker (Sb m)ᵀ.mulVecLin
    rw [hcardU] at this
    rw [← hR]
    exact this
  have hW : Module.finrank (ZMod m) W + 18 = 12 * m := by
    have h1 := rank_transpose (Sb m)
    rw [Matrix.rank, Matrix.rank] at h1
    rw [show Module.finrank (ZMod m) W = _ from h1.symm]
    exact hT
  -- `range S̄ = R^⊥`
  have hWle : W ≤ orth (Rk m) := by
    rintro _ ⟨x, rfl⟩ r hr
    have hr' : (Sb m)ᵀ *ᵥ r = 0 := hr
    rw [mulVecLin_apply, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hr',
      zero_dotProduct]
  have hWeq : W = orth (Rk m) := by
    refine Submodule.eq_of_le_of_finrank_le hWle ?_
    have := finrank_orth_add_le (Rk m)
    simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card] at this
    omega
  -- `ker (S̄ᵀ Γ̄) ⊆ range S̄`
  have hker : LinearMap.ker Fm ≤ W := by
    intro u hu
    have hu' : (Sb m)ᵀ *ᵥ (Gb m *ᵥ u) = 0 := by
      rw [mulVec_mulVec]
      exact hu
    have hmem : Gb m *ᵥ u ∈ Rk m := hu'
    rw [hWeq]
    intro r' hr'
    have hu2 : u = Gb m *ᵥ (Gb m *ᵥ u) := by
      rw [mulVec_mulVec, hGG, one_mulVec]
    rw [hu2]
    exact pairing_eq_zero hm hmem hr'
  -- `dim ker (S̄ᵀ Γ̄) = 18`
  have hkerdim : Module.finrank (ZMod m) (LinearMap.ker Fm) = 18 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Fm
    have h2 : Module.finrank (ZMod m) (LinearMap.range Fm) =
        Module.finrank (ZMod m) (LinearMap.range (Sb m)ᵀ.mulVecLin) :=
      rank_mul_eq_left_of_isUnit_det (Gb m) (Sb m)ᵀ (isUnit_det_of_left_inverse hGG)
    rw [hcardU, h2] at h1
    omega
  -- conclusion
  have hrn := LinearMap.finrank_range_add_finrank_ker (Fm.domRestrict W)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe hker).finrank_eq, hkerdim] at hrn
  have hrank : ((gram m).map f).rank = Module.finrank (ZMod m) (Submodule.map Fm W) := by
    rw [hGbar, Matrix.rank, mulVecLin_mul, LinearMap.range_comp]
  rw [hrank]
  omega

/-- **(DL2.basis) The rank in any basis.** -/
theorem rank_toMatrix_map (m : ℕ) [Fact m.Prime] (hm : 7 ≤ m) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℤ (V m)) :
    ((LinearMap.BilinForm.toMatrix b (formV m)).map (Int.castRingHom (ZMod m))).rank =
      12 * (m - 3) := by
  obtain ⟨Q, hQ⟩ := DL1.exists_projMat_mul_eq_one b
  have hG := DL1.gram_eq_projMat b
  set P := DL1.projMat b
  set M := LinearMap.BilinForm.toMatrix b (formV m)
  have hM : M = Qᵀ * gram m * Q := by
    rw [hG, show Qᵀ * (Pᵀ * M * P) * Q = (P * Q)ᵀ * M * (P * Q) by
      simp only [transpose_mul, Matrix.mul_assoc], hQ]
    simp
  set f := Int.castRingHom (ZMod m)
  have hG' : (gram m).map f = (P.map f)ᵀ * M.map f * P.map f := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, transpose_map]
  have hM' : M.map f = (Q.map f)ᵀ * (gram m).map f * Q.map f := by
    rw [hM, Matrix.map_mul, Matrix.map_mul, transpose_map]
  rw [← rank_gram_map m hm]
  refine le_antisymm ?_ ?_
  · rw [hM']
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · rw [hG']
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)



end DoubleLadder
#print axioms DoubleLadder.gram_eq_shadow
#print axioms DoubleLadder.ker_relMap_eq_span
#print axioms DoubleLadder.finrank_ker_relMap
#print axioms DoubleLadder.sum_mul_shift_eq_zero
#print axioms DoubleLadder.rank_gram_map
#print axioms DoubleLadder.rank_toMatrix_map
