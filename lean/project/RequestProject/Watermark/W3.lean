module

public import RequestProject.Watermark.W1
public import RequestProject.Watermark.W2

/-!
# The Watermark Theorem, piece W3: `SAT ⊆ K`, and `satMap` is injective over `ℤ`

* (W3.a) `gram_mulVec_satMap`: for every `m ≥ 1` (`[NeZero m]`) and `D ∈ SatSrc ℤ m`,
  `gram m *ᵥ satMap ℤ m D = 0`; hence `SAT_le_K : SAT m ≤ K m`.
* (W3.b) `eq_zero_of_satMap_eq_zero` and `satMap_injOn`: for odd `m`, `satMap ℤ m` is injective
  on `SatSrc ℤ m`.
* (W3.c) `finrank_SAT`: for odd `m`, `Module.finrank ℤ (SAT m) = 9 * m - 7`.
  Along the way, `finrank_satSrc_int : Module.finrank ℤ (SatSrc ℤ m) = 9 * m - 7` for all `m ≥ 1`.

The odd-`m` statements are proved under `Odd m` alone (this covers every odd `m ≥ 3`, and also
`m = 1`).  Helper lemmas live in the namespace `Watermark.W3`: the explicit rows of `G`
(`mulVec_zero`, `mulVec_one`, `mulVec_two`), the shift sums, the parity cancellation (S2)
`sum_two_mul_add_pair`, and the second-difference argument.
-/

@[expose] public section

open Matrix

namespace Watermark

namespace W3

variable {m : ℕ}

section Rows

variable [NeZero m]

lemma sum_ite_line (P : Point m → Prop) [DecidablePred P] (f : ZMod m → ZMod m)
    (h : ∀ q, P q ↔ q.1 = f q.2) (g : Point m → ℤ) :
    ∑ q, (if P q then (1 : ℤ) else 0) * g q = ∑ l, g (f l, l) := by
  simp only [h, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

lemma sum_same_family (x : A m) (j : Fin 3) (k l : ZMod m) :
    ∑ q : Point m, gram m (j, k, l) (j, q) * x (j, q) =
      ∑ l', x (j, k, l') + ∑ k', x (j, k', l) - (m : ℤ) * x (j, k, l) := by
  have hg : ∀ a b : ZMod m, gram m (j, k, l) (j, a, b) = (if k = a then 1 else 0) +
      (if l = b then 1 else 0) - (if k = a then (if l = b then (m : ℤ) else 0) else 0) := by
    intro a b; rw [gram_same_family (p := (j, k, l)) (q := (j, a, b)) rfl]
    by_cases h1 : k = a <;> by_cases h2 : l = b <;> simp [h1, h2]
  rw [Fintype.sum_prod_type]
  simp only [hg, sub_mul, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if k = a then x (j, a, b) else 0),
    Finset.sum_comm (f := fun a b =>
      if k = a then (if l = b then (m : ℤ) * x (j, a, b) else 0) else 0)]
  simp

lemma cross_sum (x : A m) (p : Line m) (j : Fin 3) (P : Point m → Prop) [DecidablePred P]
    (f : ZMod m → ZMod m) (hP : ∀ q, P q ↔ q.1 = f q.2)
    (hg : ∀ q, gram m p (j, q) = if P q then 1 else 0) :
    ∑ q : Point m, gram m p (j, q) * x (j, q) = ∑ l', x (j, f l', l') :=
  (Finset.sum_congr rfl fun q _ => by rw [hg]).trans (sum_ite_line P f hP (fun q => x (j, q)))

lemma mulVec_zero (x : A m) (k l : ZMod m) :
    (gram m *ᵥ x) (0, k, l) =
      ∑ l', x (0, k, l') + ∑ k', x (0, k', l) - (m : ℤ) * x (0, k, l)
      + ∑ l', x (1, k - l + l', l') + ∑ l', x (2, k + l + 1 + l', l') := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three, sum_same_family,
    cross_sum x _ 1 (fun q : Point m => k - l = q.1 - q.2) (fun l' => k - l + l')
      (fun q => by constructor <;> intro h <;> linear_combination -h)
      (fun q => by simp [gram_apply, gramUpper]),
    cross_sum x _ 2 (fun q : Point m => q.1 - q.2 = k + l + 1) (fun l' => k + l + 1 + l')
      (fun q => by constructor <;> intro h <;> linear_combination h)
      (fun q => by simp [gram_apply, gramUpper])]

lemma mulVec_one (x : A m) (k l : ZMod m) :
    (gram m *ᵥ x) (1, k, l) =
      ∑ l', x (1, k, l') + ∑ k', x (1, k', l) - (m : ℤ) * x (1, k, l)
      + ∑ l', x (0, k - l + l', l') + ∑ l', x (2, k + l - l', l') := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three, sum_same_family,
    cross_sum x _ 0 (fun q : Point m => q.1 - q.2 = k - l) (fun l' => k - l + l')
      (fun q => by constructor <;> intro h <;> linear_combination h)
      (fun q => by simp [gram_apply, gramUpper]),
    cross_sum x _ 2 (fun q : Point m => k + l = q.1 + q.2) (fun l' => k + l - l')
      (fun q => by constructor <;> intro h <;> linear_combination -h)
      (fun q => by simp [gram_apply, gramUpper])]
  ring

lemma mulVec_two (x : A m) (k l : ZMod m) :
    (gram m *ᵥ x) (2, k, l) =
      ∑ l', x (2, k, l') + ∑ k', x (2, k', l) - (m : ℤ) * x (2, k, l)
      + ∑ l', x (0, k - l - 1 - l', l') + ∑ l', x (1, k + l - l', l') := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three, sum_same_family,
    cross_sum x _ 0 (fun q : Point m => k - l = q.1 + q.2 + 1) (fun l' => k - l - 1 - l')
      (fun q => by constructor <;> intro h <;> linear_combination -h)
      (fun q => by simp [gram_apply, gramUpper]),
    cross_sum x _ 1 (fun q : Point m => q.1 + q.2 = k + l) (fun l' => k + l - l')
      (fun q => by constructor <;> intro h <;> linear_combination h)
      (fun q => by simp [gram_apply, gramUpper])]
  ring

end Rows

end W3

end Watermark

namespace Watermark
namespace W3
variable {m : ℕ} [NeZero m]

section Sums

variable {R : Type*} [AddCommMonoid R]

lemma sum_comp_add_left (u : ZMod m → R) (c : ZMod m) : ∑ x, u (c + x) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun _ => rfl)

lemma sum_comp_add_right (u : ZMod m → R) (c : ZMod m) : ∑ x, u (x + c) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

lemma sum_comp_sub_left (u : ZMod m → R) (c : ZMod m) : ∑ x, u (c - x) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.subLeft c) _ _ (fun _ => rfl)

lemma sum_comp_sub_right (u : ZMod m → R) (c : ZMod m) : ∑ x, u (x - c) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.subRight c) _ _ (fun _ => rfl)

lemma sum_comp_sub_sub_left (u : ZMod m → R) (c d : ZMod m) :
    ∑ x, u (c - x - d) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.subLeft (c - d)) _ _
    (fun x => by simp only [Equiv.subLeft_apply]; ring_nf)

lemma sum_comp_sub_sub_right (u : ZMod m → R) (c d : ZMod m) :
    ∑ x, u (x - c - d) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.subRight (c + d)) _ _
    (fun x => by simp only [Equiv.subRight_apply]; ring_nf)

lemma sum_zmod_eq_sum_range (f : ZMod m → R) : ∑ x, f x = ∑ n ∈ Finset.range m, f n := by
  symm
  refine Finset.sum_bij' (fun n _ => (n : ZMod m)) (fun x _ => x.val) (fun _ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun n hn => ?_) (fun x _ => ?_)
    (fun _ _ => rfl)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
  · exact ZMod.natCast_zmod_val x

lemma sum_range_pairs (f : ℕ → R) (k : ℕ) :
    ∑ n ∈ Finset.range k, (f (2 * n) + f (2 * n + 1)) = ∑ n ∈ Finset.range (2 * k), f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

/-- (S2) The parity cancellation: `Σ_x u(2x + c) + Σ_x u(2x + c + 1) = 2 Σ u`. -/
lemma sum_two_mul_add_pair (u : ZMod m → R) (c : ZMod m) :
    ∑ x, u (c + x + x) + ∑ x, u (c + 1 + x + x) = 2 • ∑ x, u x := by
  rw [← Finset.sum_add_distrib, sum_zmod_eq_sum_range]
  have := sum_range_pairs (fun n => u (c + n)) m
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at this
  rw [show ∑ n ∈ Finset.range m, (u (c + (n : ZMod m) + n) + u (c + 1 + n + n)) =
      ∑ n ∈ Finset.range m, (u (c + 2 * (n : ZMod m)) + u (c + (2 * n + 1))) from
    Finset.sum_congr rfl fun n _ => by congr 2 <;> ring, this, two_mul, Finset.sum_range_add,
    two_nsmul, sum_zmod_eq_sum_range (fun x => u (c + x)) |>.symm, sum_comp_add_left]
  congr 1
  rw [← sum_comp_add_left u c, sum_zmod_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

/-- (S2), shifted form: two diagonal sums whose offsets differ by an odd amount `2y + 1`. -/
lemma sum_pair_odd (u : ZMod m → R) (c d y : ZMod m) (h : d = c + 2 * y + 1) :
    ∑ x, u (c + x + x) + ∑ x, u (d + x + x) = 2 • ∑ x, u x := by
  rw [← sum_two_mul_add_pair u c]
  congr 1
  rw [← sum_comp_sub_right _ y]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h]; congr 1; ring

lemma sum_comp_lin (u : ZMod m → R) (f : ZMod m → ZMod m) (c e : ZMod m)
    (he : e = 1 ∨ e = -1) (hf : ∀ x, f x = c + e * 2 * x) :
    ∑ x, u (f x) = ∑ x, u (c + x + x) := by
  rcases he with rfl | rfl
  · exact Finset.sum_congr rfl fun x _ => by rw [hf]; congr 1; ring
  · rw [← Fintype.sum_equiv (Equiv.neg (ZMod m)) (fun x => u (f (-x))) _ (fun _ => rfl)]
    exact Finset.sum_congr rfl fun x _ => by rw [hf]; congr 1; ring

/-- (S2), general form: two diagonal sums `Σ_x u(c ± 2x)` and `Σ_x u(c + 2y + 1 ± 2x)`
whose offsets differ by an odd amount. -/
lemma sum_pair_gen (u : ZMod m → R) (f g : ZMod m → ZMod m) (c y e₁ e₂ : ZMod m)
    (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (hf : ∀ x, f x = c + e₁ * 2 * x) (hg : ∀ x, g x = c + 2 * y + 1 + e₂ * 2 * x) :
    ∑ x, u (f x) + ∑ x, u (g x) = 2 • ∑ x, u x := by
  rw [sum_comp_lin u f c e₁ he₁ hf, sum_comp_lin u g _ e₂ he₂ hg]
  exact sum_pair_odd u c _ y rfl

end Sums

lemma gram_mulVec_satMap_zero {D : SatData ℤ m} (hD : D ∈ SatSrc ℤ m) (k l : ZMod m) :
    (gram m *ᵥ satMap ℤ m D) (0, k, l) = 0 := by
  have hs := mem_satSrc.mp hD
  have ha : ∀ j, ∑ x, D.a j x = 0 := fun j => (hs j).1
  have hb : ∀ j, ∑ x, D.b j x = 0 := fun j => (hs j).2.1
  have hw : ∀ j, ∑ x, D.w j x = 0 := fun j => (hs j).2.2
  have hp := sum_pair_gen (D.w 1) (fun x => k - l + x + x) (fun x => k + l + 1 + x + x) (k - l) l
    1 1 (Or.inl rfl) (Or.inl rfl) (fun x => by ring) (fun x => by ring)
  rw [mulVec_zero]
  simp only [satMap_apply_zero, satMap_apply_one, satMap_apply_two, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, add_sub_cancel_right]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, sum_comp_add_left,
    sum_comp_add_right, sum_comp_sub_left, sum_comp_sub_right, ha, hb, hw]
  simp only [hw, smul_zero] at hp
  linear_combination hp

lemma gram_mulVec_satMap_one {D : SatData ℤ m} (hD : D ∈ SatSrc ℤ m) (k l : ZMod m) :
    (gram m *ᵥ satMap ℤ m D) (1, k, l) = 0 := by
  have hs := mem_satSrc.mp hD
  have ha : ∀ j, ∑ x, D.a j x = 0 := fun j => (hs j).1
  have hb : ∀ j, ∑ x, D.b j x = 0 := fun j => (hs j).2.1
  have hw : ∀ j, ∑ x, D.w j x = 0 := fun j => (hs j).2.2
  have hp := sum_pair_gen (D.w 2) (fun x => k - l + x + x) (fun x => k + l - x - x - 1) (k - l)
    (l - 1) 1 (-1) (Or.inl rfl) (Or.inr rfl) (fun x => by ring) (fun x => by ring)
  rw [mulVec_one]
  simp only [satMap_apply_zero, satMap_apply_one, satMap_apply_two, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, add_sub_cancel_right, sub_add_cancel]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, sum_comp_add_left,
    sum_comp_add_right, sum_comp_sub_left, sum_comp_sub_right, ha, hb, hw]
  simp only [hw, smul_zero] at hp
  linear_combination hp

lemma gram_mulVec_satMap_two {D : SatData ℤ m} (hD : D ∈ SatSrc ℤ m) (k l : ZMod m) :
    (gram m *ᵥ satMap ℤ m D) (2, k, l) = 0 := by
  have hs := mem_satSrc.mp hD
  have ha : ∀ j, ∑ x, D.a j x = 0 := fun j => (hs j).1
  have hb : ∀ j, ∑ x, D.b j x = 0 := fun j => (hs j).2.1
  have hw : ∀ j, ∑ x, D.w j x = 0 := fun j => (hs j).2.2
  have hp := sum_pair_gen (D.w 0) (fun x => k - l - 1 - x - x) (fun x => k + l - x - x)
    (k - l - 1) l (-1) (-1) (Or.inr rfl) (Or.inr rfl) (fun x => by ring) (fun x => by ring)
  rw [mulVec_two]
  simp only [satMap_apply_zero, satMap_apply_one, satMap_apply_two, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sub_add_cancel]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, sum_comp_add_left,
    sum_comp_add_right, sum_comp_sub_left, sum_comp_sub_sub_left,
    sum_comp_sub_sub_right, ha, hb, hw]
  simp only [hw, smul_zero] at hp
  linear_combination hp

end W3

/-- **(W3.a) `SAT ⊆ K`.** For every `m ≥ 1` and every admissible integral datum `D`,
`G · satMap(D) = 0`. -/
theorem gram_mulVec_satMap {m : ℕ} [NeZero m] {D : SatData ℤ m} (hD : D ∈ SatSrc ℤ m) :
    gram m *ᵥ satMap ℤ m D = 0 := by
  ext ⟨j, k, l⟩
  fin_cases j
  · exact W3.gram_mulVec_satMap_zero hD k l
  · exact W3.gram_mulVec_satMap_one hD k l
  · exact W3.gram_mulVec_satMap_two hD k l

/-- **(W3.a)** `SAT m ≤ K m`. -/
theorem SAT_le_K (m : ℕ) [NeZero m] : SAT m ≤ K m := by
  rintro _ ⟨D, hD, rfl⟩
  exact mem_K.mpr (gram_mulVec_satMap hD)

/-! ### (W3.b) Injectivity over `ℤ` for odd `m` -/

namespace W3

section Inj

variable {m : ℕ}

/-- The second difference `(Δ²w)(z) = w(z+2) − 2w(z+1) + w(z)` of an integer function. -/
def sd (w : ZMod m → ℤ) (z : ZMod m) : ℤ := w (z + 2) - 2 * w (z + 1) + w z

/-- The mixed difference of a family identity `a(k) + b(l) + w(k − l) + u(k + l) + c = 0`. -/
lemma sd_mixed {a b w u : ZMod m → ℤ} {c : ℤ}
    (h : ∀ k l, a k + b l + w (k - l) + u (k + l) + c = 0) (k l : ZMod m) :
    sd u (k + l) = sd w (k - l - 1) := by
  have h1 := h (k + 1) (l + 1)
  have h2 := h (k + 1) l
  have h3 := h k (l + 1)
  have h4 := h k l
  rw [show k + 1 - (l + 1) = k - l by ring, show k + 1 + (l + 1) = k + l + 2 by ring] at h1
  rw [show k + 1 - l = k - l - 1 + 2 by ring, show k + 1 + l = k + l + 1 by ring] at h2
  rw [show k - (l + 1) = k - l - 1 by ring, show k + (l + 1) = k + l + 1 by ring] at h3
  unfold sd
  rw [show k - l - 1 + 1 = k - l by ring]
  linear_combination h1 - h2 - h3 + h4

/-- For odd `m`, `(k, l) ↦ (k + l, k − l − 1)` is onto, so the two second differences in a family
identity are the same constant. -/
lemma sd_eq_of_odd (hm : Odd m) {a b w u : ZMod m → ℤ} {c : ℤ}
    (h : ∀ k l, a k + b l + w (k - l) + u (k + l) + c = 0) (x y : ZMod m) :
    sd u x = sd w y := by
  obtain ⟨r, rfl⟩ := hm
  have ht : (2 : ZMod (2 * r + 1)) * ((r + 1 : ℕ) : ZMod (2 * r + 1)) = 1 := by
    have : ((2 * r + 1 : ℕ) : ZMod (2 * r + 1)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination this
  set t : ZMod (2 * r + 1) := ((r + 1 : ℕ) : ZMod (2 * r + 1))
  have e := sd_mixed h (t * (x + y + 1)) (t * (x - y - 1))
  rwa [show t * (x + y + 1) + t * (x - y - 1) = x by linear_combination x * ht,
    show t * (x + y + 1) - t * (x - y - 1) - 1 = y by linear_combination (y + 1) * ht] at e

variable [NeZero m]

/-- An integer function on `ZMod m` with constant second difference and sum zero vanishes. -/
lemma eq_zero_of_sd_const {w : ZMod m → ℤ} {d : ℤ} (h : ∀ x, sd w x = d) (hw : ∑ x, w x = 0) :
    w = 0 := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  set e : ZMod m → ℤ := fun x => w (x + 1) - w x with he
  have step : ∀ x, e (x + 1) = e x + d := by
    intro x
    have := h x
    simp only [sd] at this
    simp only [he, show x + 1 + 1 = x + 2 by ring]
    linear_combination this
  have lin : ∀ n : ℕ, e n = e 0 + n * d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, step, ih]; push_cast; ring
  have hd : d = 0 := by
    have := lin m
    rw [ZMod.natCast_self] at this
    have : (m : ℤ) * d = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hm0
  have econst : ∀ x, e x = e 0 := by
    intro x
    have := lin x.val
    rwa [ZMod.natCast_zmod_val, hd, mul_zero, add_zero] at this
  have he0 : e 0 = 0 := by
    have hs : ∑ x, e x = 0 := by
      simp only [he, Finset.sum_sub_distrib, sum_comp_add_right, sub_self]
    rw [Finset.sum_congr rfl fun x _ => econst x, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul] at hs
    exact (mul_eq_zero.mp hs).resolve_left hm0
  have wconst : ∀ n : ℕ, w n = w 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := econst n
      rw [he0] at this
      simp only [he] at this
      rw [Nat.cast_succ]; linarith
  have wx : ∀ x, w x = w 0 := fun x => by
    have := wconst x.val; rwa [ZMod.natCast_zmod_val] at this
  have h0 : w 0 = 0 := by
    rw [Finset.sum_congr rfl fun x _ => wx x, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul] at hw
    exact (mul_eq_zero.mp hw).resolve_left hm0
  funext x
  rw [wx, h0]; rfl

/-- If `a(k) + b(l) + c = 0` for all `k, l` with `a, b` sum-zero, then `a = b = 0` and `c = 0`. -/
lemma axis_eq_zero {a b : ZMod m → ℤ} {c : ℤ} (h : ∀ k l, a k + b l + c = 0)
    (ha : ∑ x, a x = 0) (hb : ∑ x, b x = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hbl : ∀ l, b l + c = 0 := by
    intro l
    have := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => h k l
    simp only [Finset.sum_add_distrib, ha, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, zero_add] at this
    have : (m : ℤ) * (b l + c) = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left hm0
  have hak : ∀ k, a k + c = 0 := by
    intro k
    have := Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => h k l
    simp only [Finset.sum_add_distrib, hb, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, add_zero] at this
    have : (m : ℤ) * (a k + c) = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left hm0
  have hc : c = 0 := by
    have hb' : ∑ x, b x = ∑ x : ZMod m, (-c) :=
      Finset.sum_congr rfl fun x _ => by linear_combination hbl x
    rw [hb, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hb'
    have : (m : ℤ) * c = 0 := by linear_combination hb'
    exact (mul_eq_zero.mp this).resolve_left hm0
  subst hc
  exact ⟨funext fun k => by simpa using hak k, funext fun l => by simpa using hbl l, rfl⟩

end Inj

end W3

/-- **(W3.b) Injectivity.** For odd `m`, an admissible integral datum with `satMap D = 0`
is zero. -/
theorem eq_zero_of_satMap_eq_zero {m : ℕ} [NeZero m] (hm : Odd m) {D : SatData ℤ m}
    (hD : D ∈ SatSrc ℤ m) (h0 : satMap ℤ m D = 0) : D = 0 := by
  have hs := mem_satSrc.mp hD
  have ha : ∀ j, ∑ x, D.a j x = 0 := fun j => (hs j).1
  have hb : ∀ j, ∑ x, D.b j x = 0 := fun j => (hs j).2.1
  have hw : ∀ j, ∑ x, D.w j x = 0 := fun j => (hs j).2.2
  have f0 : ∀ k l, D.a 0 k + D.b 0 l + D.w 0 (k - l) + D.w 2 (k + l) + D.ε₁ = 0 := fun k l => by
    simpa using congrFun h0 (0, k, l)
  have f1 : ∀ k l, D.a 1 k + D.b 1 l + D.w 0 (k - l) + D.w 1 (k + l) + (D.ε₂ - D.ε₁) = 0 :=
    fun k l => by simpa using congrFun h0 (1, k, l)
  have f2 : ∀ k l, D.a 2 k + D.b 2 l + D.w 1 (k + l) + D.w 2 (k - l - 1) - D.ε₂ = 0 :=
    fun k l => by simpa using congrFun h0 (2, k, l)
  have hw0 : D.w 0 = 0 :=
    W3.eq_zero_of_sd_const (fun y => (W3.sd_eq_of_odd hm f0 0 y).symm.trans
      (W3.sd_eq_of_odd hm f0 0 0)) (hw 0)
  have hw2 : D.w 2 = 0 :=
    W3.eq_zero_of_sd_const (fun x => W3.sd_eq_of_odd hm f0 x 0) (hw 2)
  have hw1 : D.w 1 = 0 :=
    W3.eq_zero_of_sd_const (fun x => W3.sd_eq_of_odd hm f1 x 0) (hw 1)
  simp only [hw0, hw1, hw2, Pi.zero_apply, add_zero] at f0 f1 f2
  obtain ⟨ha0, hb0, he1⟩ := W3.axis_eq_zero f0 (ha 0) (hb 0)
  obtain ⟨ha1, hb1, he21⟩ := W3.axis_eq_zero f1 (ha 1) (hb 1)
  obtain ⟨ha2, hb2, -⟩ := W3.axis_eq_zero (c := -D.ε₂) (fun k l => by linear_combination f2 k l)
    (ha 2) (hb 2)
  rw [SatData.ext_iff']
  refine ⟨show D.a = 0 from ?_, show D.b = 0 from ?_, show D.w = 0 from ?_,
    show D.ε₁ = 0 from he1, show D.ε₂ = 0 by linear_combination he21 + he1⟩
  · funext j; fin_cases j <;> simp [ha0, ha1, ha2]
  · funext j; fin_cases j <;> simp [hb0, hb1, hb2]
  · funext j; fin_cases j <;> simp [hw0, hw1, hw2]

/-- **(W3.b)** For odd `m`, `satMap ℤ m` is injective on `SatSrc ℤ m`. -/
theorem satMap_injOn {m : ℕ} [NeZero m] (hm : Odd m) :
    Set.InjOn (satMap ℤ m) (SatSrc ℤ m) := by
  intro D hD E hE h
  have := eq_zero_of_satMap_eq_zero hm (sub_mem hD hE) (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp this

/-! ### (W3.c) The rank of `SAT` -/

namespace W3

variable {m : ℕ} [NeZero m]

lemma satSums_surjective_int : Function.Surjective (satSums ℤ m) := by
  rintro ⟨u, v, s⟩
  refine ⟨SatData.mk (fun j => Pi.single 0 (u j)) (fun j => Pi.single 0 (v j))
    (fun j => Pi.single 0 (s j)) 0 0, ?_⟩
  simp [satSums]

end W3

/-- The admissible integral data form a free `ℤ`-module of rank `9(m − 1) + 2 = 9m − 7`
(for every `m ≥ 1`). -/
theorem finrank_satSrc_int {m : ℕ} [NeZero m] : Module.finrank ℤ (SatSrc ℤ m) = 9 * m - 7 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker (satSums ℤ m))
  rw [(LinearMap.quotKerEquivOfSurjective _ W3.satSums_surjective_int).finrank_eq] at h
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_self] at h
  have h3 : Module.finrank ℤ (Fin 3 → ZMod m → ℤ) = 3 * m := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card, ZMod.card]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [h3] at h
  change Module.finrank ℤ (LinearMap.ker (satSums ℤ m)) = _
  omega

/-- For odd `m`, `satMap ℤ m` restricted to `SatSrc ℤ m` is injective. -/
theorem satMap_domRestrict_injective {m : ℕ} [NeZero m] (hm : Odd m) :
    Function.Injective ((satMap ℤ m).domRestrict (SatSrc ℤ m)) := by
  intro D E h
  exact Subtype.ext (satMap_injOn hm D.2 E.2 h)

/-- **(W3.c) Rank.** For odd `m`, `rank SAT = 9m − 7`. -/
theorem finrank_SAT {m : ℕ} [NeZero m] (hm : Odd m) : Module.finrank ℤ (SAT m) = 9 * m - 7 := by
  rw [SAT, ← LinearMap.range_domRestrict,
    LinearMap.finrank_range_of_inj (satMap_domRestrict_injective hm), finrank_satSrc_int]

end Watermark

