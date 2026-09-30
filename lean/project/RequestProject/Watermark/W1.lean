module

public import RequestProject.Watermark.Defs

@[expose] public section

open Matrix

/-!
# The Watermark Theorem, piece W1: first identities

(W1.a) `Watermark.gram_transpose` is proved in `RequestProject.Watermark.Defs` (it is needed
there to define the induced form on `V`).  This file proves (W1.b) `gram_mulVec_famVec`,
(W1.c) `sum_E_pencil` and (W1.d) `aug_of_mem_K`.
-/

namespace Watermark

variable {m : ℕ}

lemma gram_same_family {p q : Line m} (h : p.1 = q.1) :
    gram m p q = (if p.2.1 = q.2.1 then 1 else 0) + (if p.2.2 = q.2.2 then 1 else 0)
      - (if p.2 = q.2 then (m : ℤ) else 0) := by
  rw [gram_apply, if_pos h.le, gramUpper, if_pos h]
  obtain ⟨_, a, b⟩ := p
  obtain ⟨_, c, d⟩ := q
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]

variable [NeZero m]

lemma mulVec_famVec (j : Fin 3) (p : Line m) :
    (gram m *ᵥ famVec m j) p = ∑ q : Point m, gram m p (j, q) := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type]
  simp [famVec]

lemma sum_line_fst (P : Point m → Prop) [DecidablePred P] (f : ZMod m → ZMod m)
    (h : ∀ q, P q ↔ q.1 = f q.2) : ∑ q, (if P q then 1 else 0 : ℤ) = m := by
  simp only [h]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [ZMod.card]

lemma sum_line_snd (P : Point m → Prop) [DecidablePred P] (f : ZMod m → ZMod m)
    (h : ∀ q, P q ↔ q.2 = f q.1) : ∑ q, (if P q then 1 else 0 : ℤ) = m := by
  simp only [h]
  rw [Fintype.sum_prod_type]
  simp [ZMod.card]

lemma card_line_fst (P : Point m → Prop) [DecidablePred P] (f : ZMod m → ZMod m)
    (h : ∀ q, P q ↔ q.1 = f q.2) : (Finset.univ.filter P).card = m := by
  have := sum_line_fst P f h
  rw [Finset.sum_boole] at this
  exact_mod_cast this

lemma card_line_snd (P : Point m → Prop) [DecidablePred P] (f : ZMod m → ZMod m)
    (h : ∀ q, P q ↔ q.2 = f q.1) : (Finset.univ.filter P).card = m := by
  have := sum_line_snd P f h
  rw [Finset.sum_boole] at this
  exact_mod_cast this

/-- **(W1.b) The family vectors.** `G · N_j = m · 𝟙`. -/
theorem gram_mulVec_famVec (j : Fin 3) : gram m *ᵥ famVec m j = (m : ℤ) • ones m := by
  ext ⟨i, a⟩
  rw [mulVec_famVec]
  simp only [Pi.smul_apply, ones, smul_eq_mul, mul_one]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_congr rfl (fun q _ => gram_same_family (p := (i, a)) (q := (i, q)) rfl)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [card_line_fst _ (fun _ => a.1) (fun _ => eq_comm),
      card_line_snd _ (fun _ => a.2) (fun _ => eq_comm)]
    ring
  · fin_cases i <;> fin_cases j <;> simp [gram_apply, gramUpper] at hij ⊢
    · exact card_line_fst _ (fun l => a.1 - a.2 + l) (fun q => by
        constructor <;> intro h <;> linear_combination -h)
    · exact card_line_fst _ (fun l => a.1 + a.2 + 1 + l) (fun q => by
        constructor <;> intro h <;> linear_combination h)
    · exact card_line_fst _ (fun l => a.1 - a.2 + l) (fun q => by
        constructor <;> intro h <;> linear_combination h)
    · exact card_line_fst _ (fun l => a.1 + a.2 - l) (fun q => by
        constructor <;> intro h <;> linear_combination -h)
    · exact card_line_fst _ (fun l => a.1 - a.2 - 1 - l) (fun q => by
        constructor <;> intro h <;> linear_combination -h)
    · exact card_line_fst _ (fun l => a.1 + a.2 - l) (fun q => by
        constructor <;> intro h <;> linear_combination h)

/-! ### (W1.c) The incidence identity -/

section Incidence

variable [Fact m.Prime]

lemma card_pencils_agree (q p : Point m) :
    (Finset.univ.filter fun π : Option (ZMod m) => pencil π q = pencil π p).card =
      if q = p then m + 1 else 1 := by
  split_ifs with h
  · subst h
    simp [Fintype.card_option, ZMod.card]
  · obtain ⟨a, b⟩ := q
    obtain ⟨c, d⟩ := p
    rw [Finset.card_eq_one]
    by_cases hbd : b = d
    · subst hbd
      have hac : a ≠ c := fun hac => h (by rw [hac])
      refine ⟨none, ?_⟩
      ext π
      cases π with
      | none => simp [pencil]
      | some t => simp [pencil, hac]
    · refine ⟨some ((c - a) / (b - d)), ?_⟩
      have hbd' : b - d ≠ 0 := sub_ne_zero.mpr hbd
      ext π
      cases π with
      | none => simp [pencil, hbd]
      | some t =>
        simp only [pencil, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Option.some.injEq]
        rw [eq_div_iff hbd']
        constructor <;> intro h' <;> linear_combination h'

/-- **(W1.c) The incidence identity (Lemma R.1).**  Summing `E_π u` over the `m + 1` pencils
`π_t` (`t ∈ ZMod m`, encoded as `some t`) and `π_∞` (encoded as `none`) gives
`m · u(p) + Σ_{p'} u(p')`. -/
theorem sum_E_pencil (u : Point m → ℤ) (p : Point m) :
    ∑ π : Option (ZMod m), E (pencil π) u p = m * u p + ∑ q, u q := by
  simp only [E, Finset.sum_filter]
  rw [Finset.sum_comm]
  have key : ∀ q, ∑ π : Option (ZMod m), (if pencil π q = pencil π p then u q else 0) =
      u q + if q = p then (m : ℤ) * u q else 0 := by
    intro q
    rw [← Finset.sum_filter, Finset.sum_const, card_pencils_agree, nsmul_eq_mul]
    split_ifs <;> push_cast <;> ring
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Incidence

/-! ### (W1.d) Augmentation divisibility -/

section Augmentation

lemma sum_aug_restrict (x : A m) :
    aug (restrict x 0) + aug (restrict x 1) + aug (restrict x 2) = ∑ p, x p := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  rfl

/-- `B(N_j, x) = (G N_j) · x = m · Σ_p x(p)`, by (W1.a) and (W1.b). -/
lemma gramForm_famVec (j : Fin 3) (x : A m) : gramForm m (famVec m j) x = m * ∑ p, x p := by
  rw [gramForm_apply, dotProduct_mulVec, ← mulVec_transpose, gram_transpose,
    gram_mulVec_famVec]
  simp [dotProduct, ones, Finset.mul_sum]

/-- First half of (W1.d): the sum of the entries of any `x ∈ K` vanishes. -/
theorem sum_eq_zero_of_mem_K {x : A m} (hx : x ∈ K m) : ∑ p, x p = 0 := by
  have h := gramForm_eq_zero_of_mem_K_right (famVec m 0) hx
  rw [gramForm_famVec] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast NeZero.ne m)

/-- The indicator of the fibre `{(0, k, l) : k + t·l = 0}` of the pencil `π_t` in family 0. -/
def fibre (m : ℕ) (t : ZMod m) : A m :=
  fun p => if p.1 = 0 ∧ p.2.1 + t * p.2.2 = 0 then 1 else 0

lemma mulVec_fibre (t : ZMod m) (p : Line m) :
    (gram m *ᵥ fibre m t) p = ∑ l, gram m p (0, (-t * l, l)) := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
  have h1 : ∀ q : Point m, fibre m t (1, q) = 0 := fun q => by simp [fibre]
  have h2 : ∀ q : Point m, fibre m t (2, q) = 0 := fun q => by simp [fibre]
  have h0 : ∀ q : Point m, fibre m t (0, q) = if q.1 + t * q.2 = 0 then 1 else 0 :=
    fun q => by simp [fibre]
  simp only [h0, h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : ∀ k : ZMod m, (k + t * l = 0) ↔ k = -t * l := fun k => by
    constructor <;> intro h <;> linear_combination h
  simp [this]

omit [NeZero m] in
lemma two_ne_zero_zmod (hm : 5 ≤ m) : (2 : ZMod m) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

omit [NeZero m] in
lemma three_ne_zero_zmod (hm : 5 ≤ m) : (3 : ZMod m) ≠ 0 := by
  intro h
  have : ((3 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

variable [Fact m.Prime]

lemma sum_ite_mul_eq (α β : ZMod m) :
    ∑ l : ZMod m, (if α * l = β then 1 else 0 : ZMod m) = if α = 0 then 0 else 1 := by
  split_ifs with h
  · subst h
    simp only [zero_mul, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]
  · have : ∀ l, α * l = β ↔ l = β / α := fun l => by
      rw [eq_div_iff h, mul_comm]
    simp [this]

lemma gram_fibre_zero {t : ZMod m} (ht : t ≠ 0) (a : Point m) :
    ((gram m *ᵥ fibre m t) (0, a) : ZMod m) = 2 := by
  have h1 : ∀ l : ZMod m, gram m (0, a) (0, (-t * l, l)) =
      (if -t * l = a.1 then 1 else 0) + (if 1 * l = a.2 then 1 else 0)
        - (if a = (-t * l, l) then (m : ℤ) else 0) := fun l => by
    rw [gram_same_family (p := (0, a)) (q := (0, (-t * l, l))) rfl]
    simp only [eq_comm, one_mul]
  rw [mulVec_fibre, Finset.sum_congr rfl fun l _ => h1 l]
  push_cast
  simp only [Finset.sum_add_distrib, sum_ite_mul_eq, neg_eq_zero, ht, one_ne_zero, if_false,
    ZMod.natCast_self, ite_self, sub_zero]
  norm_num

lemma gram_fibre_one (t : ZMod m) (a : Point m) :
    ((gram m *ᵥ fibre m t) (1, a) : ZMod m) = if -(t + 1) = 0 then 0 else 1 := by
  have h1 : ∀ l : ZMod m, gram m (1, a) (0, (-t * l, l)) =
      if -(t + 1) * l = a.1 - a.2 then 1 else 0 := fun l => by
    simp only [gram_apply, gramUpper]
    simp only [Fin.isValue, Fin.reduceLE, if_false, Fin.reduceEq, and_self, if_true, true_and]
    exact if_congr (by constructor <;> intro h <;> linear_combination h) rfl rfl
  rw [mulVec_fibre, Finset.sum_congr rfl fun l _ => h1 l]
  push_cast
  exact sum_ite_mul_eq _ _

lemma gram_fibre_two (t : ZMod m) (a : Point m) :
    ((gram m *ᵥ fibre m t) (2, a) : ZMod m) = if 1 - t = 0 then 0 else 1 := by
  have h1 : ∀ l : ZMod m, gram m (2, a) (0, (-t * l, l)) =
      if (1 - t) * l = a.1 - a.2 - 1 then 1 else 0 := fun l => by
    simp only [gram_apply, gramUpper]
    simp only [Fin.isValue, Fin.reduceLE, if_false, Fin.reduceEq, and_self, if_true, false_and,
      true_and]
    exact if_congr (by constructor <;> intro h <;> linear_combination -h) rfl rfl
  rw [mulVec_fibre, Finset.sum_congr rfl fun l _ => h1 l]
  push_cast
  exact sum_ite_mul_eq _ _

/-- Pairing `x ∈ K` with the fibre indicator of `π_t` (`t ≠ 0`) in family 0, reduced mod `m`. -/
lemma fibre_pairing {t : ZMod m} (ht : t ≠ 0) {x : A m} (hx : x ∈ K m) :
    2 * (aug (restrict x 0) : ZMod m)
      + (if -(t + 1) = 0 then 0 else 1) * (aug (restrict x 1) : ZMod m)
      + (if 1 - t = 0 then 0 else 1) * (aug (restrict x 2) : ZMod m) = 0 := by
  have h := gramForm_eq_zero_of_mem_K_right (fibre m t) hx
  rw [gramForm_comm, gramForm_apply, dotProduct_comm, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_three] at h
  have h' := congrArg (Int.cast : ℤ → ZMod m) h
  push_cast at h'
  simp only [gram_fibre_zero ht, gram_fibre_one, gram_fibre_two] at h'
  simp only [aug, restrict]
  push_cast
  simp only [Finset.mul_sum]
  exact h'

/-- **(W1.d) Augmentation divisibility (Lemma R.2).**  For `m ≥ 5` prime and `x ∈ K`:
`aug(x_0) + aug(x_1) + aug(x_2) = 0`, and `m ∣ aug(x_j)` for every `j`. -/
theorem aug_of_mem_K (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) :
    aug (restrict x 0) + aug (restrict x 1) + aug (restrict x 2) = 0 ∧
      ∀ j : Fin 3, (m : ℤ) ∣ aug (restrict x j) := by
  refine ⟨by rw [sum_aug_restrict, sum_eq_zero_of_mem_K hx], ?_⟩
  have h2 := two_ne_zero_zmod hm
  have h3 := three_ne_zero_zmod hm
  have e1 := fibre_pairing (t := 2) h2 hx
  have e2 := fibre_pairing (t := 1) one_ne_zero hx
  have e3 := fibre_pairing (t := -1) (neg_ne_zero.mpr one_ne_zero) hx
  have c1 : -((2 : ZMod m) + 1) ≠ 0 := by
    rw [neg_ne_zero]; norm_num; exact h3
  have c2 : (1 : ZMod m) - 2 ≠ 0 := by norm_num
  have c3 : -((1 : ZMod m) + 1) ≠ 0 := by
    rw [neg_ne_zero]; norm_num; exact h2
  have c4 : (1 : ZMod m) - (-1) ≠ 0 := by norm_num; exact h2
  simp only [c1, c2, c3, c4, if_false, sub_self, neg_add_cancel, neg_zero, if_true, one_mul,
    zero_mul, add_zero] at e1 e2 e3
  set a0 := (aug (restrict x 0) : ZMod m)
  set a1 := (aug (restrict x 1) : ZMod m)
  set a2 := (aug (restrict x 2) : ZMod m)
  have ha2 : a2 = 0 := by linear_combination e1 - e2
  have ha1 : a1 = 0 := by linear_combination e1 - e3
  have ha0 : a0 = 0 := by
    have : 2 * a0 = 0 := by linear_combination e2 + e3 - e1
    exact (mul_eq_zero.mp this).resolve_left h2
  intro j
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  fin_cases j
  · exact ha0
  · exact ha1
  · exact ha2

end Augmentation

end Watermark
