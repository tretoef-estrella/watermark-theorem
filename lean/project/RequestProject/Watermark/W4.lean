module

public import RequestProject.Watermark.W3

/-!
# The Watermark Theorem, piece W4: pullbacks along pencils

* `pb j π u`: the pullback of `u : ZMod m → ℤ` along the pencil `π`, placed on family `j`;
  `fib π y`: the fibre sums of `y : Point m → ℤ` along `π`; `ext j y`: `y` placed on family `j`.
* (W4.a) `sum_pencil_mul_pencil` (`m` prime, `π ≠ π'`) and `sum_pencil_mul_same` (any `m ≥ 1`).
* (W4.b) For `u ∈ sumZero ℤ m`:
  - axis pencils, any `m ≥ 1`: `gram_mulVec_pb_axis_some_zero`, `gram_mulVec_pb_axis_none`;
  - live pencils: `gram_mulVec_pb_live` (`m` prime, `t ∉ {0, 1, −1}`), and the general
    `gram_mulVec_pb_live_of_isUnit` (any `m`, `t`, `t + 1`, `t − 1` units);
  - overlap pencils, any odd `m`: `gram_mulVec_pb_zero_neg_one`, `gram_mulVec_pb_one_neg_one`,
    `gram_mulVec_pb_one_one`, `gram_mulVec_pb_two_one`, `gram_mulVec_pb_zero_one`,
    `gram_mulVec_pb_two_neg_one`.  (`W4.odd_of_prime_of_five_le` turns `m` prime, `m ≥ 5`,
    into `Odd m`.)
* (W4.c) `smul_ext_eq_sum_pb_fib` (`m` prime).

The key computation is `W4.gram_pb_apply`, the entries of `G · pb j π u` read off from the rows of
`G` (W3's `mulVec_zero`, `mulVec_one`, `mulVec_two`).
-/

@[expose] public section

open Matrix

namespace Watermark

/-- The pullback `pb j π u ∈ A` of `u : ZMod m → ℤ` along the pencil `π`, placed on family `j`:
`pb j π u (j', k, l) = if j' = j then u (pencil π (k, l)) else 0`. -/
def pb {m : ℕ} (j : Fin 3) (π : Option (ZMod m)) (u : ZMod m → ℤ) : A m :=
  fun p => if p.1 = j then u (pencil π p.2) else 0

/-- The fibre sums `fib π y v = Σ_{p : pencil π p = v} y p`. -/
def fib {m : ℕ} [NeZero m] (π : Option (ZMod m)) (y : Point m → ℤ) (v : ZMod m) : ℤ :=
  ∑ q ∈ Finset.univ.filter (fun q => pencil π q = v), y q

/-- `ext j y ∈ A`: the function `y : Point m → ℤ` placed on family `j` (zero elsewhere). -/
def ext {m : ℕ} (j : Fin 3) (y : Point m → ℤ) : A m := fun p => if p.1 = j then y p.2 else 0

namespace W4

variable {m : ℕ}

/-- The offset `c` of the incidence set `{k' = c + e l'}` through which a line `(j', k, l)` sees
family `j ≠ j'`. -/
def crossC (j' j : Fin 3) (k l : ZMod m) : ZMod m :=
  match j', j with
  | 0, 1 => k - l
  | 0, 2 => k + l + 1
  | 1, 0 => k - l
  | 1, 2 => k + l
  | 2, 0 => k - l - 1
  | 2, 1 => k + l
  | _, _ => 0

/-- The slope `e` of the incidence set `{k' = c + e l'}` (see `crossC`). -/
def crossE (j' j : Fin 3) : ZMod m :=
  match j', j with
  | 0, 1 => 1
  | 0, 2 => 1
  | 1, 0 => 1
  | 1, 2 => -1
  | 2, 0 => -1
  | 2, 1 => -1
  | _, _ => 0

lemma crossE_cases {j' j : Fin 3} (h : j' ≠ j) :
    crossE (m := m) j' j = 1 ∨ crossE (m := m) j' j = -1 := by
  fin_cases j' <;> fin_cases j <;> simp_all [crossE]

lemma isUnit_two_of_odd (hm : Odd m) : IsUnit (2 : ZMod m) := by
  have : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hm
  simpa using (ZMod.unitOfCoprime 2 this).isUnit

lemma odd_of_prime_of_five_le [Fact m.Prime] (hm : 5 ≤ m) : Odd m :=
  (Fact.out : m.Prime).odd_of_ne_two (by omega)

/-- Two distinct pencils are independent coordinates on `Point m`. -/
lemma pencil_pair_injective [Fact m.Prime] {π π' : Option (ZMod m)} (h : π ≠ π') :
    Function.Injective (fun p : Point m => (pencil π p, pencil π' p)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hp
  simp only [Prod.mk.injEq] at hp
  obtain ⟨h1, h2⟩ := hp
  cases π with
  | none =>
    cases π' with
    | none => exact absurd rfl h
    | some t =>
      simp only [pencil] at h1 h2
      subst h1
      exact Prod.ext (by linear_combination h2) rfl
  | some s =>
    cases π' with
    | none =>
      simp only [pencil] at h1 h2
      subst h2
      exact Prod.ext (by linear_combination h1) rfl
    | some t =>
      simp only [pencil] at h1 h2
      have hst : t - s ≠ 0 := sub_ne_zero.mpr fun e => h (by rw [e])
      have hbd : b = d := by
        have : (t - s) * (b - d) = 0 := by linear_combination h2 - h1
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hst)
      subst hbd
      exact Prod.ext (by linear_combination h1) rfl

variable [NeZero m]

/-- The entries of `G · pb j π u`: on family `j` the row/column sums minus `m · u(π(k, l))`,
and on another family `j'` a sum over the incidence set `{k' = c + e l'}`. -/
lemma gram_pb_apply (j : Fin 3) (π : Option (ZMod m)) (u : ZMod m → ℤ) (j' : Fin 3)
    (k l : ZMod m) :
    (gram m *ᵥ pb j π u) (j', k, l) =
      if j' = j then
        ∑ l', u (pencil π (k, l')) + ∑ k', u (pencil π (k', l)) - (m : ℤ) * u (pencil π (k, l))
      else ∑ x, u (pencil π (crossC j' j k l + crossE j' j * x, x)) := by
  fin_cases j' <;> fin_cases j <;>
    simp [W3.mulVec_zero, W3.mulVec_one, W3.mulVec_two, pb, crossC, crossE] <;>
    refine Finset.sum_congr rfl fun x _ => ?_ <;> ring_nf

lemma sum_affine (u : ZMod m → ℤ) (c : ZMod m) {b : ZMod m} (hb : IsUnit b) :
    ∑ x, u (c + b * x) = ∑ x, u x := by
  refine Fintype.sum_bijective (fun x => c + b * x) ?_ _ _ (fun _ => rfl)
  refine Finite.injective_iff_bijective.mp fun x y hxy => ?_
  exact hb.mul_left_cancel (add_left_cancel hxy)

lemma sum_pencil_some (u : ZMod m → ℤ) (t c e : ZMod m) :
    ∑ x, u (pencil (some t) (c + e * x, x)) = ∑ x, u (c + (e + t) * x) :=
  Finset.sum_congr rfl fun x _ => by simp only [pencil]; ring_nf

lemma cross_unit {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) {t e : ZMod m} (c : ZMod m)
    (h : IsUnit (e + t)) : ∑ x, u (pencil (some t) (c + e * x, x)) = 0 := by
  rw [sum_pencil_some, sum_affine u c h, mem_sumZero.mp hu]

lemma cross_zero (u : ZMod m → ℤ) {t e : ZMod m} (c : ZMod m) (h : e + t = 0) :
    ∑ x, u (pencil (some t) (c + e * x, x)) = m * u c := by
  simp [sum_pencil_some, h, ZMod.card]

lemma cross_none {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) (c e : ZMod m) :
    ∑ x, u (pencil none (c + e * x, x)) = 0 := by
  simpa [pencil] using mem_sumZero.mp hu

lemma same_some {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) {t : ZMod m} (ht : IsUnit t)
    (k l : ZMod m) :
    ∑ l', u (pencil (some t) (k, l')) + ∑ k', u (pencil (some t) (k', l))
      - (m : ℤ) * u (pencil (some t) (k, l)) = -(m : ℤ) * u (k + t * l) := by
  have h1 : ∑ l', u (pencil (some t) (k, l')) = 0 := by
    simp only [pencil]; rw [sum_affine u k ht, mem_sumZero.mp hu]
  have h2 : ∑ k', u (pencil (some t) (k', l)) = 0 := by
    simp only [pencil]; rw [W3.sum_comp_add_right u, mem_sumZero.mp hu]
  rw [h1, h2]; simp [pencil]

end W4

end Watermark

namespace Watermark

open W4

variable {m : ℕ} [NeZero m]

/-- **(W4.b.1) Axis pencil `k`** (`π = some 0`), for every `m ≥ 1`. -/
theorem gram_mulVec_pb_axis_some_zero (j : Fin 3) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb j (some 0) u = 0 := by
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  split_ifs with h
  · simp [pencil, mem_sumZero.mp hu, ZMod.card]
  · rw [cross_unit hu _ (by rcases crossE_cases (m := m) h with h' | h' <;> simp [h'])]; rfl

/-- **(W4.b.1) Axis pencil `l`** (`π = none`), for every `m ≥ 1`. -/
theorem gram_mulVec_pb_axis_none (j : Fin 3) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb j none u = 0 := by
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  split_ifs with h
  · simp [pencil, mem_sumZero.mp hu, ZMod.card]
  · rw [cross_none hu]; rfl

/-- **(W4.b.2) Live non-overlap pencils**, for any `m`, under the hypothesis that `t`, `t + 1`
and `t - 1` are units. -/
theorem gram_mulVec_pb_live_of_isUnit (j : Fin 3) {t : ZMod m} (ht : IsUnit t)
    (ht₁ : IsUnit (1 + t)) (ht₂ : IsUnit (-1 + t)) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb j (some t) u = -(m : ℤ) • pb j (some t) u := by
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  split_ifs with h
  · rw [same_some hu ht]; simp [pb, h, pencil]
  · rw [cross_unit hu _ (by rcases crossE_cases (m := m) h with h' | h' <;> simp [h', ht₁, ht₂])]
    simp [pb, h]

/-- **(W4.b.3) Overlap pencils.** `G · pb 0 (−1) u = −m • pb 0 (−1) u + m • pb 1 (−1) u`, for every odd `m`. -/
theorem gram_mulVec_pb_zero_neg_one (hm : Odd m) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb 0 (some (-1)) u =
      -(m : ℤ) • pb 0 (some (-1)) u + (m : ℤ) • pb 1 (some (-1)) u := by
  have h2 := isUnit_two_of_odd hm
  have ha : IsUnit (1 + 1 : ZMod m) := by rw [one_add_one_eq_two]; exact h2
  have hb : IsUnit (-1 + -1 : ZMod m) := by
    rw [show (-1 + -1 : ZMod m) = -2 by ring]; exact h2.neg
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  fin_cases j' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, ite_true,
    crossC, crossE, Fin.reduceEq, if_false, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pb] <;>
  first
  | (rw [same_some hu isUnit_one.neg]; simp only [pencil]; ring_nf)
  | (rw [cross_zero u _ (by ring)]; simp only [pencil]; ring_nf)
  | (rw [cross_unit hu _ (by assumption)]; ring)

/-- **(W4.b.3) Overlap pencils.** `G · pb 1 (−1) u = −m • pb 1 (−1) u + m • pb 0 (−1) u`, for every odd `m`. -/
theorem gram_mulVec_pb_one_neg_one (hm : Odd m) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb 1 (some (-1)) u =
      -(m : ℤ) • pb 1 (some (-1)) u + (m : ℤ) • pb 0 (some (-1)) u := by
  have h2 := isUnit_two_of_odd hm
  have ha : IsUnit (1 + 1 : ZMod m) := by rw [one_add_one_eq_two]; exact h2
  have hb : IsUnit (-1 + -1 : ZMod m) := by
    rw [show (-1 + -1 : ZMod m) = -2 by ring]; exact h2.neg
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  fin_cases j' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, ite_true,
    crossC, crossE, Fin.reduceEq, if_false, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pb] <;>
  first
  | (rw [same_some hu isUnit_one.neg]; simp only [pencil]; ring_nf)
  | (rw [cross_zero u _ (by ring)]; simp only [pencil]; ring_nf)
  | (rw [cross_unit hu _ (by assumption)]; ring)

/-- **(W4.b.3) Overlap pencils.** `G · pb 1 (1) u = −m • pb 1 (1) u + m • pb 2 (1) u`, for every odd `m`. -/
theorem gram_mulVec_pb_one_one (hm : Odd m) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb 1 (some 1) u =
      -(m : ℤ) • pb 1 (some 1) u + (m : ℤ) • pb 2 (some 1) u := by
  have h2 := isUnit_two_of_odd hm
  have ha : IsUnit (1 + 1 : ZMod m) := by rw [one_add_one_eq_two]; exact h2
  have hb : IsUnit (-1 + -1 : ZMod m) := by
    rw [show (-1 + -1 : ZMod m) = -2 by ring]; exact h2.neg
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  fin_cases j' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, ite_true,
    crossC, crossE, Fin.reduceEq, if_false, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pb] <;>
  first
  | (rw [same_some hu isUnit_one]; simp only [pencil]; ring_nf)
  | (rw [cross_zero u _ (by ring)]; simp only [pencil]; ring_nf)
  | (rw [cross_unit hu _ (by assumption)]; ring)

/-- **(W4.b.3) Overlap pencils.** `G · pb 2 (1) u = −m • pb 2 (1) u + m • pb 1 (1) u`, for every odd `m`. -/
theorem gram_mulVec_pb_two_one (hm : Odd m) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb 2 (some 1) u =
      -(m : ℤ) • pb 2 (some 1) u + (m : ℤ) • pb 1 (some 1) u := by
  have h2 := isUnit_two_of_odd hm
  have ha : IsUnit (1 + 1 : ZMod m) := by rw [one_add_one_eq_two]; exact h2
  have hb : IsUnit (-1 + -1 : ZMod m) := by
    rw [show (-1 + -1 : ZMod m) = -2 by ring]; exact h2.neg
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  fin_cases j' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, ite_true,
    crossC, crossE, Fin.reduceEq, if_false, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pb] <;>
  first
  | (rw [same_some hu isUnit_one]; simp only [pencil]; ring_nf)
  | (rw [cross_zero u _ (by ring)]; simp only [pencil]; ring_nf)
  | (rw [cross_unit hu _ (by assumption)]; ring)

/-- **(W4.b.3) Overlap pencils.** `G · pb 0 (1) u = −m • pb 0 (1) u + m • pb 2 (−1) u⁻` with `u⁻(x) = u(x − 1)`, for every odd `m`. -/
theorem gram_mulVec_pb_zero_one (hm : Odd m) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb 0 (some 1) u =
      -(m : ℤ) • pb 0 (some 1) u + (m : ℤ) • pb 2 (some (-1)) (fun x => u (x - 1)) := by
  have h2 := isUnit_two_of_odd hm
  have ha : IsUnit (1 + 1 : ZMod m) := by rw [one_add_one_eq_two]; exact h2
  have hb : IsUnit (-1 + -1 : ZMod m) := by
    rw [show (-1 + -1 : ZMod m) = -2 by ring]; exact h2.neg
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  fin_cases j' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, ite_true,
    crossC, crossE, Fin.reduceEq, if_false, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pb] <;>
  first
  | (rw [same_some hu isUnit_one]; simp only [pencil]; ring_nf)
  | (rw [cross_zero u _ (by ring)]; simp only [pencil]; ring_nf)
  | (rw [cross_unit hu _ (by assumption)]; ring)

/-- **(W4.b.3) Overlap pencils.** `G · pb 2 (−1) u = −m • pb 2 (−1) u + m • pb 0 (1) u⁺` with `u⁺(x) = u(x + 1)`, for every odd `m`. -/
theorem gram_mulVec_pb_two_neg_one (hm : Odd m) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb 2 (some (-1)) u =
      -(m : ℤ) • pb 2 (some (-1)) u + (m : ℤ) • pb 0 (some 1) (fun x => u (x + 1)) := by
  have h2 := isUnit_two_of_odd hm
  have ha : IsUnit (1 + 1 : ZMod m) := by rw [one_add_one_eq_two]; exact h2
  have hb : IsUnit (-1 + -1 : ZMod m) := by
    rw [show (-1 + -1 : ZMod m) = -2 by ring]; exact h2.neg
  ext ⟨j', k, l⟩
  rw [gram_pb_apply]
  fin_cases j' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, ite_true,
    crossC, crossE, Fin.reduceEq, if_false, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pb] <;>
  first
  | (rw [same_some hu isUnit_one.neg]; simp only [pencil]; ring_nf)
  | (rw [cross_zero u _ (by ring)]; simp only [pencil]; ring_nf)
  | (rw [cross_unit hu _ (by assumption)]; ring)

end Watermark

namespace Watermark

open W4

variable {m : ℕ}

/-- **(W4.b.2) Live non-overlap pencils.** For `m` prime and `t ∉ {0, 1, −1}`,
`G · pb j (t) u = −m • pb j (t) u` for every sum-zero `u`. -/
theorem gram_mulVec_pb_live [Fact m.Prime] (j : Fin 3) {t : ZMod m} (h0 : t ≠ 0) (h1 : t ≠ 1)
    (h2 : t ≠ -1) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    gram m *ᵥ pb j (some t) u = -(m : ℤ) • pb j (some t) u :=
  gram_mulVec_pb_live_of_isUnit j (Ne.isUnit h0)
    (Ne.isUnit fun h => h2 (by linear_combination h))
    (Ne.isUnit fun h => h1 (by linear_combination h)) hu

/-- **(W4.a) Two pencils are independent coordinates.** For `m` prime and `π ≠ π'`,
`Σ_p u(π p) · v(π' p) = (Σ u) · (Σ v)`. -/
theorem sum_pencil_mul_pencil [Fact m.Prime] {π π' : Option (ZMod m)} (h : π ≠ π')
    (u v : ZMod m → ℤ) :
    ∑ p : Point m, u (pencil π p) * v (pencil π' p) = (∑ x, u x) * (∑ x, v x) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.mp (pencil_pair_injective h))
    _ _ (fun _ => rfl)

/-- **(W4.a) One pencil.** For every `m ≥ 1`, `Σ_p u(π p) · v(π p) = m · Σ_x u(x) v(x)`. -/
theorem sum_pencil_mul_same [NeZero m] (π : Option (ZMod m)) (u v : ZMod m → ℤ) :
    ∑ p : Point m, u (pencil π p) * v (pencil π p) = m * ∑ x, u x * v x := by
  rw [Fintype.sum_prod_type]
  cases π with
  | none => simp [pencil, ZMod.card]
  | some t =>
    rw [Finset.sum_comm]
    simp only [pencil]
    simp [W3.sum_comp_add_right (fun x => u x * v x), ZMod.card]

/-- The fibre sum at `pencil π p` is `E_π y p`. -/
lemma fib_pencil [NeZero m] (π : Option (ZMod m)) (y : Point m → ℤ) (p : Point m) :
    fib π y (pencil π p) = E (pencil π) y p := rfl

/-- **(W4.c) Fibre decomposition of one family.** For `m` prime, every `y : Point m → ℤ` and
every family `j`: `m • ext j y = Σ_π pb j π (fib π y) − (Σ_p y p) • N_j`. -/
theorem smul_ext_eq_sum_pb_fib [Fact m.Prime] (j : Fin 3) (y : Point m → ℤ) :
    (m : ℤ) • ext j y = ∑ π : Option (ZMod m), pb j π (fib π y) - (∑ p, y p) • famVec m j := by
  ext ⟨j', q⟩
  simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, ext, pb, famVec, smul_eq_mul]
  split_ifs with h
  · simp only [fib_pencil, sum_E_pencil]; ring
  · simp

end Watermark
