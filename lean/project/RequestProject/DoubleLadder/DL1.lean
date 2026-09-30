module

public import RequestProject.Watermark.W7

/-!
# The Double Ladder Theorem, piece DL1: the exponent of the discriminant group divides `m²`

We define the certificate matrix `ylad m` and prove
* (DL1.a) `gram_mul_ylad_mul_gram`: `G * Y * G = 6m² • G` for `m` prime, `m ≥ 5`;
* (DL1.b) `exists_toMatrix_mul_eq`: for every `ℤ`-basis `b` of `V m`, the Gram matrix `M` of
  `formV m` in `b` satisfies `M * X = m² • 1` for some integer matrix `X`;
* (DL1.c) `exists_formV_eq_smul`: `m² • f` is represented by `formV m` for every
  `f ∈ Hom(V m, ℤ)`, i.e. `m² V* ⊆ V`.
-/

@[expose] public section

open Matrix Watermark

namespace DoubleLadder

/-- The certificate matrix `Y`, block diagonal over the three families: inside each family
`Y = P_k + P_l + 3 P_{k−l} + 3 P_{k+l} − 6m·I`. -/
def ylad (m : ℕ) : Matrix (Line m) (Line m) ℤ := Matrix.of fun p q =>
  if p.1 = q.1 then
      (if p.2.1 = q.2.1 then 1 else 0) + (if p.2.2 = q.2.2 then 1 else 0)
    + 3 * (if p.2.1 - p.2.2 = q.2.1 - q.2.2 then 1 else 0)
    + 3 * (if p.2.1 + p.2.2 = q.2.1 + q.2.2 then 1 else 0)
    - (if p = q then 6 * (m : ℤ) else 0)
  else 0

namespace DL1

variable {m : ℕ}

/-- `P_σ(a, b) = 1` iff the pencil `σ` takes the same value at `a` and `b`. -/
def ind (σ : Option (ZMod m)) (a b : Point m) : ℤ := if pencil σ a = pencil σ b then 1 else 0

lemma ylad_apply' (p q : Line m) :
    ylad m p q = if p.1 = q.1 then
      ind (some 0) p.2 q.2 + ind none p.2 q.2 + 3 * ind (some (-1)) p.2 q.2
        + 3 * ind (some 1) p.2 q.2 - (if p.2 = q.2 then 6 * (m : ℤ) else 0) else 0 := by
  obtain ⟨j, a⟩ := p
  obtain ⟨j', b⟩ := q
  have e1 : (a.1 - a.2 = b.1 - b.2) ↔ (a.1 + -1 * a.2 = b.1 + -1 * b.2) := by
    simp [sub_eq_add_neg]
  simp only [ylad, of_apply, ind, pencil, e1, zero_mul, add_zero, one_mul, Prod.mk.injEq]
  by_cases h : j = j' <;> simp [h]

variable [NeZero m]

lemma ylad_mulVec_pb (j : Fin 3) (π : Option (ZMod m)) (u : ZMod m → ℤ) (j' : Fin 3)
    (a : Point m) :
    (ylad m *ᵥ pb j π u) (j', a) = if j' = j then
      (∑ b, ind (some 0) a b * u (pencil π b)) + (∑ b, ind none a b * u (pencil π b))
        + 3 * (∑ b, ind (some (-1)) a b * u (pencil π b))
        + 3 * (∑ b, ind (some 1) a b * u (pencil π b)) - 6 * (m : ℤ) * u (pencil π a)
      else 0 := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [ylad_apply', pb, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single j']
  · simp only [if_true]
    split_ifs with h
    · simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
        ← Finset.mul_sum, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

lemma sum_ind_same (π : Option (ZMod m)) (u : ZMod m → ℤ) (a : Point m) :
    ∑ b, ind π a b * u (pencil π b) = m * u (pencil π a) := by
  have := sum_pencil_mul_same π (fun x => if pencil π a = x then (1 : ℤ) else 0) u
  simpa [ind] using this

lemma sum_ind_one (σ : Option (ZMod m)) (a : Point m) : ∑ b, ind σ a b = m := by
  simpa using sum_ind_same σ (fun _ => 1) a

lemma sum_ind_other [Fact m.Prime] {σ π : Option (ZMod m)} (h : σ ≠ π) (u : ZMod m → ℤ)
    (a : Point m) : ∑ b, ind σ a b * u (pencil π b) = ∑ x, u x := by
  have := sum_pencil_mul_pencil h (fun x => if pencil σ a = x then (1 : ℤ) else 0) u
  simpa [ind] using this

omit [NeZero m] in
lemma neg_one_ne_one_of_odd [Fact m.Prime] (hm : Odd m) : (-1 : ZMod m) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod m) = 0 := by linear_combination -h
  have hu := W4.isUnit_two_of_odd hm
  rw [h2] at hu
  exact not_isUnit_zero hu

/-! ### Step 1: `Y` on the pieces -/

lemma ylad_mulVec_pb_live [Fact m.Prime] (j : Fin 3) {t : ZMod m} (h0 : t ≠ 0) (h1 : t ≠ 1)
    (h2 : t ≠ -1) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    ylad m *ᵥ pb j (some t) u = (-6 * (m : ℤ)) • pb j (some t) u := by
  ext ⟨j', a⟩
  rw [ylad_mulVec_pb, sum_ind_other (by simpa using Ne.symm h0),
    sum_ind_other (by simp), sum_ind_other (by simpa using Ne.symm h2),
    sum_ind_other (by simpa using Ne.symm h1), mem_sumZero.mp hu]
  simp only [pb, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma ylad_mulVec_pb_one [Fact m.Prime] (hm : Odd m) (j : Fin 3) {u : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) :
    ylad m *ᵥ pb j (some 1) u = (-3 * (m : ℤ)) • pb j (some 1) u := by
  ext ⟨j', a⟩
  rw [ylad_mulVec_pb, sum_ind_other (by simp), sum_ind_other (by simp),
    sum_ind_other (by simpa using neg_one_ne_one_of_odd hm), sum_ind_same, mem_sumZero.mp hu]
  simp only [pb, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma ylad_mulVec_pb_neg_one [Fact m.Prime] (hm : Odd m) (j : Fin 3) {u : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) :
    ylad m *ᵥ pb j (some (-1)) u = (-3 * (m : ℤ)) • pb j (some (-1)) u := by
  ext ⟨j', a⟩
  rw [ylad_mulVec_pb, sum_ind_other (by simp), sum_ind_other (by simp), sum_ind_same,
    sum_ind_other (by simpa using (neg_one_ne_one_of_odd hm).symm), mem_sumZero.mp hu]
  simp only [pb, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

omit [NeZero m] in
lemma famVec_eq_pb (j : Fin 3) : famVec m j = pb j none (fun _ => 1) := by
  ext p
  simp [famVec, pb]

lemma ylad_mulVec_famVec (j : Fin 3) :
    ylad m *ᵥ famVec m j = (2 * (m : ℤ)) • famVec m j := by
  rw [famVec_eq_pb]
  ext ⟨j', a⟩
  rw [ylad_mulVec_pb]
  simp only [mul_one, sum_ind_one, pb, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

omit [NeZero m] in
lemma ones_eq_sum : ones m = ∑ j, famVec m j := by
  ext p
  simp [ones, famVec, Finset.sum_apply]

lemma ylad_mulVec_ones : ylad m *ᵥ ones m = (2 * (m : ℤ)) • ones m := by
  rw [ones_eq_sum, mulVec_sum, Finset.smul_sum]
  simp only [ylad_mulVec_famVec]

lemma gram_mulVec_ones : gram m *ᵥ ones m = (3 * (m : ℤ)) • ones m := by
  conv_lhs => rw [ones_eq_sum, mulVec_sum]
  simp only [Fin.sum_univ_three, gram_mulVec_famVec]
  module

/-! ### Step 2: `G Y G = 6m² G` on the pieces -/

/-- The defect matrix `N = G Y G − 6m² G`. -/
def defect (m : ℕ) [NeZero m] : Matrix (Line m) (Line m) ℤ :=
  gram m * ylad m * gram m - (6 * (m : ℤ) ^ 2) • gram m

lemma defect_mulVec (v : A m) :
    defect m *ᵥ v = gram m *ᵥ (ylad m *ᵥ (gram m *ᵥ v)) - (6 * (m : ℤ) ^ 2) • (gram m *ᵥ v) := by
  rw [defect, sub_mulVec, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]

lemma defect_axis {v : A m} (h : gram m *ᵥ v = 0) : defect m *ᵥ v = 0 := by
  simp [defect_mulVec, h]

lemma defect_live {v : A m} (hG : gram m *ᵥ v = -(m : ℤ) • v)
    (hY : ylad m *ᵥ v = (-6 * (m : ℤ)) • v) : defect m *ᵥ v = 0 := by
  simp only [defect_mulVec, hG, mulVec_smul, hY]
  module

lemma defect_pair {v v' : A m} (hG : gram m *ᵥ v = -(m : ℤ) • v + (m : ℤ) • v')
    (hG' : gram m *ᵥ v' = -(m : ℤ) • v' + (m : ℤ) • v)
    (hY : ylad m *ᵥ v = (-3 * (m : ℤ)) • v) (hY' : ylad m *ᵥ v' = (-3 * (m : ℤ)) • v') :
    defect m *ᵥ v = 0 := by
  simp only [defect_mulVec, hG, mulVec_add, mulVec_smul, hY, hY', hG']
  module

lemma defect_famVec (j : Fin 3) : defect m *ᵥ famVec m j = 0 := by
  simp only [defect_mulVec, gram_mulVec_famVec, mulVec_smul, ylad_mulVec_ones,
    gram_mulVec_ones]
  module

lemma shift_mem {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) (c : ZMod m) :
    (fun x => u (x + c)) ∈ sumZero ℤ m := by
  rw [mem_sumZero] at hu ⊢
  rw [← hu]
  exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

lemma shift_sub_mem {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    (fun x => u (x - 1)) ∈ sumZero ℤ m := by
  simpa [sub_eq_add_neg] using shift_mem hu (-1)

lemma defect_pb_sumZero [Fact m.Prime] (hm : 5 ≤ m) (j : Fin 3) (π : Option (ZMod m))
    {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) : defect m *ᵥ pb j π u = 0 := by
  have hodd := W4.odd_of_prime_of_five_le hm
  rcases π with _ | t
  · exact defect_axis (gram_mulVec_pb_axis_none j hu)
  by_cases h0 : t = 0
  · subst h0; exact defect_axis (gram_mulVec_pb_axis_some_zero j hu)
  by_cases h1 : t = 1
  · subst h1
    fin_cases j
    · have hu' := shift_sub_mem hu
      have hG' := gram_mulVec_pb_two_neg_one hodd hu'
      simp only [add_sub_cancel_right] at hG'
      exact defect_pair (gram_mulVec_pb_zero_one hodd hu) hG'
        (ylad_mulVec_pb_one hodd 0 hu) (ylad_mulVec_pb_neg_one hodd 2 hu')
    · exact defect_pair (gram_mulVec_pb_one_one hodd hu) (gram_mulVec_pb_two_one hodd hu)
        (ylad_mulVec_pb_one hodd 1 hu) (ylad_mulVec_pb_one hodd 2 hu)
    · exact defect_pair (gram_mulVec_pb_two_one hodd hu) (gram_mulVec_pb_one_one hodd hu)
        (ylad_mulVec_pb_one hodd 2 hu) (ylad_mulVec_pb_one hodd 1 hu)
  by_cases h2 : t = -1
  · subst h2
    fin_cases j
    · exact defect_pair (gram_mulVec_pb_zero_neg_one hodd hu)
        (gram_mulVec_pb_one_neg_one hodd hu)
        (ylad_mulVec_pb_neg_one hodd 0 hu) (ylad_mulVec_pb_neg_one hodd 1 hu)
    · exact defect_pair (gram_mulVec_pb_one_neg_one hodd hu)
        (gram_mulVec_pb_zero_neg_one hodd hu)
        (ylad_mulVec_pb_neg_one hodd 1 hu) (ylad_mulVec_pb_neg_one hodd 0 hu)
    · have hu' := shift_mem hu 1
      have hG' := gram_mulVec_pb_zero_one hodd hu'
      simp only [sub_add_cancel] at hG'
      exact defect_pair (gram_mulVec_pb_two_neg_one hodd hu) hG'
        (ylad_mulVec_pb_neg_one hodd 2 hu) (ylad_mulVec_pb_one hodd 0 hu')
  · exact defect_live (gram_mulVec_pb_live j h0 h1 h2 hu) (ylad_mulVec_pb_live j h0 h1 h2 hu)

/-! ### Step 3: from the pieces to all of `A` -/

lemma eq_zero_of_smul {v : A m} (h : (m : ℤ) • v = 0) : v = 0 := by
  rcases smul_eq_zero.mp h with h | h
  · exact absurd (by exact_mod_cast h) (NeZero.ne m)
  · exact h

lemma smul_pb_eq (j : Fin 3) (π : Option (ZMod m)) (w : ZMod m → ℤ) :
    (m : ℤ) • pb j π w =
      pb j π (fun x => (m : ℤ) * w x - ∑ y, w y) + (∑ y, w y) • famVec m j := by
  ext p
  simp only [pb, famVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  split_ifs <;> ring

lemma sumZero_aux (w : ZMod m → ℤ) :
    (fun x => (m : ℤ) * w x - ∑ y, w y) ∈ sumZero ℤ m := by
  rw [mem_sumZero, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [ZMod.card]

lemma defect_pb [Fact m.Prime] (hm : 5 ≤ m) (j : Fin 3) (π : Option (ZMod m))
    (w : ZMod m → ℤ) : defect m *ᵥ pb j π w = 0 := by
  apply eq_zero_of_smul
  rw [← mulVec_smul, smul_pb_eq, mulVec_add, mulVec_smul,
    defect_pb_sumZero hm j π (sumZero_aux w), defect_famVec]
  simp

lemma defect_ext [Fact m.Prime] (hm : 5 ≤ m) (j : Fin 3) (y : Point m → ℤ) :
    defect m *ᵥ Watermark.ext j y = 0 := by
  apply eq_zero_of_smul
  rw [← mulVec_smul, smul_ext_eq_sum_pb_fib, mulVec_sub, mulVec_sum, mulVec_smul,
    defect_famVec]
  simp [defect_pb hm]

omit [NeZero m] in
lemma eq_sum_ext (x : A m) : x = ∑ j, Watermark.ext j (restrict x j) := by
  ext ⟨j, q⟩
  simp [Watermark.ext, restrict, Finset.sum_apply]

lemma defect_eq_zero [Fact m.Prime] (hm : 5 ≤ m) : defect m = 0 := by
  have hx : ∀ x : A m, defect m *ᵥ x = 0 := fun x => by
    rw [eq_sum_ext x, mulVec_sum]
    simp [defect_ext hm]
  ext p q
  have := congrFun (hx (Pi.single q 1)) p
  simpa [mulVec_single_one] using this

end DL1

open DL1

/-- **(DL1.a) The certificate identity.** For `m` prime with `5 ≤ m`,
`G * Y * G = 6m² • G`. -/
theorem gram_mul_ylad_mul_gram (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) :
    gram m * ylad m * gram m = (6 * (m : ℤ) ^ 2) • gram m :=
  sub_eq_zero.mp (defect_eq_zero hm)

namespace DL1

variable {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of the projection `A m → V m` in the standard basis of `A m` and the basis `b`
of `V m`. -/
noncomputable def projMat (b : Module.Basis ι ℤ (V m)) : Matrix ι (Line m) ℤ :=
  LinearMap.toMatrix (Pi.basisFun ℤ (Line m)) b (K m).mkQ

lemma gram_eq_projMat (b : Module.Basis ι ℤ (V m)) :
    gram m = (projMat b)ᵀ * LinearMap.BilinForm.toMatrix b (formV m) * projMat b := by
  have h := LinearMap.toMatrix₂_compl₁₂ b b (Pi.basisFun ℤ (Line m)) (Pi.basisFun ℤ (Line m))
    (formV m) (K m).mkQ (K m).mkQ
  have hc : (formV m).compl₁₂ (K m).mkQ (K m).mkQ = gramForm m := by
    ext x y
    rfl
  rw [hc, LinearMap.toMatrix₂_basisFun, gramForm, LinearMap.toMatrix'_toLinearMap₂'] at h
  exact h

lemma exists_projMat_mul_eq_one (b : Module.Basis ι ℤ (V m)) :
    ∃ Q : Matrix (Line m) ι ℤ, projMat b * Q = 1 := by
  choose x hx using fun i => (K m).mkQ_surjective (b i)
  refine ⟨LinearMap.toMatrix b (Pi.basisFun ℤ (Line m)) (b.constr ℤ x), ?_⟩
  have hs : (K m).mkQ ∘ₗ b.constr ℤ x = LinearMap.id := b.ext fun i => by simp [hx]
  rw [projMat, ← LinearMap.toMatrix_comp, hs, LinearMap.toMatrix_id]

lemma coprime_six [Fact m.Prime] (hm : 5 ≤ m) (N : ℕ) : IsCoprime (6 : ℤ) ((m : ℤ) ^ N) := by
  have hp : m.Prime := Fact.out
  have h : Nat.Coprime 6 m := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    interval_cases m <;> revert h hp <;> decide
  have := (Nat.isCoprime_iff_coprime.mpr h).pow_right (n := N)
  simpa using this

end DL1

/-- **(DL1.b) The exponent, in coordinates.** For `m` prime with `5 ≤ m` and every `ℤ`-basis `b`
of `V m`, the Gram matrix `M` of `formV m` in `b` satisfies `M * X = m² • 1` for some integer
matrix `X`. -/
theorem exists_toMatrix_mul_eq (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℤ (V m)) :
    ∃ X : Matrix ι ι ℤ,
      LinearMap.BilinForm.toMatrix b (formV m) * X = ((m : ℤ) ^ 2) • (1 : Matrix ι ι ℤ) := by
  set M := LinearMap.BilinForm.toMatrix b (formV m) with hMdef
  set P := projMat b
  obtain ⟨Q, hQ⟩ := exists_projMat_mul_eq_one b
  have hQt : Qᵀ * Pᵀ = 1 := by rw [← transpose_mul, hQ, transpose_one]
  have hG := gram_mul_ylad_mul_gram m hm
  rw [gram_eq_projMat b] at hG
  set Z := P * ylad m * Pᵀ with hZ
  have hMZM : M * Z * M = (6 * (m : ℤ) ^ 2) • M := by
    calc M * Z * M = Qᵀ * (Pᵀ * M * P * ylad m * (Pᵀ * M * P)) * Q := by
          simp only [hZ, ← Matrix.mul_assoc]
          rw [hQt, Matrix.mul_assoc _ P Q, hQ, Matrix.one_mul, Matrix.mul_one]
      _ = Qᵀ * ((6 * (m : ℤ) ^ 2) • (Pᵀ * M * P)) * Q := by rw [hG]
      _ = (6 * (m : ℤ) ^ 2) • M := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          congr 1
          simp only [← Matrix.mul_assoc]
          rw [hQt, Matrix.one_mul, Matrix.mul_assoc, hQ, Matrix.mul_one]
  have hdet : M.det = (m : ℤ) ^ (3 * (m - 3) ^ 2) := (watermark_theorem hm).2.2 b
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ (by exact_mod_cast (NeZero.ne m))
  have hMZ : M * Z = (6 * (m : ℤ) ^ 2) • (1 : Matrix ι ι ℤ) := by
    apply smul_right_injective _ hdet0
    have := congrArg (· * adjugate M) hMZM
    simp only at this
    rw [Matrix.mul_assoc, mul_adjugate, Matrix.smul_mul, mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one] at this
    show M.det • (M * Z) = M.det • _
    rw [this, smul_comm]
  have hdZ : M.det • Z = (6 * (m : ℤ) ^ 2) • adjugate M := by
    have := congrArg (adjugate M * ·) hMZ
    simp only at this
    rw [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one] at this
    exact this
  have hdvd : ∀ i j, (6 : ℤ) ∣ Z i j := fun i j => by
    have h := congrFun (congrFun hdZ i) j
    simp only [smul_apply, smul_eq_mul, hdet] at h
    refine (coprime_six hm (3 * (m - 3) ^ 2)).dvd_of_dvd_mul_left ?_
    rw [h]
    exact ⟨(m : ℤ) ^ 2 * adjugate M i j, by ring⟩
  refine ⟨Matrix.of fun i j => Z i j / 6, ?_⟩
  have hX : (6 : ℤ) • (Matrix.of fun i j => Z i j / 6) = Z := by
    ext i j
    simp [Int.mul_ediv_cancel' (hdvd i j)]
  apply smul_right_injective _ (show (6 : ℤ) ≠ 0 by norm_num)
  simp only
  rw [← Matrix.mul_smul, hX, hMZ, smul_smul]

/-- **(DL1.c) The exponent, intrinsically.** For `m` prime with `5 ≤ m`, every `f ∈ Hom(V m, ℤ)`
satisfies `m² • f = formV m v` for some `v ∈ V m`; i.e. `m² V* ⊆ V`. -/
theorem exists_formV_eq_smul (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) (f : Module.Dual ℤ (V m)) :
    ∃ v : V m, ((m : ℤ) ^ 2) • f = formV m v := by
  classical
  let b := Module.Free.chooseBasis ℤ (V m)
  obtain ⟨X, hX⟩ := exists_toMatrix_mul_eq m hm b
  set M := LinearMap.BilinForm.toMatrix b (formV m) with hM
  let c : _ → ℤ := fun i => f (b i)
  refine ⟨∑ i, (X *ᵥ c) i • b i, b.ext fun k => ?_⟩
  have hsym : ∀ i, formV m (b i) (b k) = M k i := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply, formV_isSymm.eq]
  have h1 : formV m (∑ i, (X *ᵥ c) i • b i) (b k) = (M *ᵥ (X *ᵥ c)) k := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hsym, smul_eq_mul,
      mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, mulVec_mulVec, hX, smul_mulVec, one_mulVec]
  simp [c]

end DoubleLadder
