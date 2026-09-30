module

public import RequestProject.Watermark.Defs

/-!
# The Watermark Theorem, piece W2: the saturation lattice `SAT` and Lemma C

* `SatData R m`: a SAT datum over a commutative ring `R` (six axis functions `a_j, b_j`,
  three overlap functions `w_0, w_1, w_2` and two scalars `ε₁, ε₂`).
* `sumZero R m`: the sum-zero functions `ZMod m → R`; `SatSrc R m`: the admissible data
  (all nine functions sum-zero).
* `satMap R m : SatData R m →ₗ[R] (Line m → R)`, and `SAT m := (SatSrc ℤ m).map (satMap ℤ m)`.

Statements: (W2.a) `finrank_sumZero`, `finrank_satSrc`; (W2.b) `satMap_map`, `satMap_red`,
`red_mem_satSrc`, `exists_sumZero_lift`, `exists_satSrc_lift`; (W2.c) Lemma C, `map_ker_satMap_eq`,
`finrank_ker_satMap` and `finrank_range_satMap`.
-/

@[expose] public section

namespace Watermark

/-! ### The data -/

/-- A SAT datum over `R`: `(a, b, w, ε₁, ε₂)` with `a j, b j : ZMod m → R` the two axis pencils
of family `j`, `w i : ZMod m → R` the overlap pencils (`w 0` for the pair (0,1), `w 1` for the
pair (1,2), `w 2` for the pair (0,2)) and two scalars `ε₁, ε₂ : R`. -/
abbrev SatData (R : Type*) (m : ℕ) : Type _ :=
  (Fin 3 → ZMod m → R) × (Fin 3 → ZMod m → R) × (Fin 3 → ZMod m → R) × R × R

namespace SatData

variable {R S : Type*} {m : ℕ}

/-- Build a datum from its components. -/
def mk (a b w : Fin 3 → ZMod m → R) (ε₁ ε₂ : R) : SatData R m := (a, b, w, ε₁, ε₂)

/-- The axis functions `a_j` (pencil `k` of family `j`). -/
def a (D : SatData R m) : Fin 3 → ZMod m → R := D.1
/-- The axis functions `b_j` (pencil `l` of family `j`). -/
def b (D : SatData R m) : Fin 3 → ZMod m → R := D.2.1
/-- The overlap functions `w_i`. -/
def w (D : SatData R m) : Fin 3 → ZMod m → R := D.2.2.1
/-- The scalar `ε₁`. -/
def ε₁ (D : SatData R m) : R := D.2.2.2.1
/-- The scalar `ε₂`. -/
def ε₂ (D : SatData R m) : R := D.2.2.2.2

@[simp] lemma a_mk (a b w : Fin 3 → ZMod m → R) (e₁ e₂ : R) : (mk a b w e₁ e₂).a = a := rfl
@[simp] lemma b_mk (a b w : Fin 3 → ZMod m → R) (e₁ e₂ : R) : (mk a b w e₁ e₂).b = b := rfl
@[simp] lemma w_mk (a b w : Fin 3 → ZMod m → R) (e₁ e₂ : R) : (mk a b w e₁ e₂).w = w := rfl
@[simp] lemma ε₁_mk (a b w : Fin 3 → ZMod m → R) (e₁ e₂ : R) : (mk a b w e₁ e₂).ε₁ = e₁ := rfl
@[simp] lemma ε₂_mk (a b w : Fin 3 → ZMod m → R) (e₁ e₂ : R) : (mk a b w e₁ e₂).ε₂ = e₂ := rfl

lemma ext_iff' {D E : SatData R m} :
    D = E ↔ D.a = E.a ∧ D.b = E.b ∧ D.w = E.w ∧ D.ε₁ = E.ε₁ ∧ D.ε₂ = E.ε₂ := by
  obtain ⟨_, _, _, _, _⟩ := D
  obtain ⟨_, _, _, _, _⟩ := E
  simp [a, b, w, ε₁, ε₂]

section Module

variable [Semiring R]

@[simp] lemma a_add (D E : SatData R m) : (D + E).a = D.a + E.a := rfl
@[simp] lemma b_add (D E : SatData R m) : (D + E).b = D.b + E.b := rfl
@[simp] lemma w_add (D E : SatData R m) : (D + E).w = D.w + E.w := rfl
@[simp] lemma ε₁_add (D E : SatData R m) : (D + E).ε₁ = D.ε₁ + E.ε₁ := rfl
@[simp] lemma ε₂_add (D E : SatData R m) : (D + E).ε₂ = D.ε₂ + E.ε₂ := rfl
@[simp] lemma a_smul (c : R) (D : SatData R m) : (c • D).a = c • D.a := rfl
@[simp] lemma b_smul (c : R) (D : SatData R m) : (c • D).b = c • D.b := rfl
@[simp] lemma w_smul (c : R) (D : SatData R m) : (c • D).w = c • D.w := rfl
@[simp] lemma ε₁_smul (c : R) (D : SatData R m) : (c • D).ε₁ = c • D.ε₁ := rfl
@[simp] lemma ε₂_smul (c : R) (D : SatData R m) : (c • D).ε₂ = c • D.ε₂ := rfl

end Module

/-- Apply a map `f : R → S` to every entry of a datum (used with `f` a ring map, e.g. the
reduction `ℤ → ZMod m`). -/
def map (f : R → S) (D : SatData R m) : SatData S m :=
  mk (fun j x => f (D.a j x)) (fun j x => f (D.b j x)) (fun j x => f (D.w j x))
    (f D.ε₁) (f D.ε₂)

@[simp] lemma a_map (f : R → S) (D : SatData R m) (j : Fin 3) (x : ZMod m) :
    (D.map f).a j x = f (D.a j x) := rfl
@[simp] lemma b_map (f : R → S) (D : SatData R m) (j : Fin 3) (x : ZMod m) :
    (D.map f).b j x = f (D.b j x) := rfl
@[simp] lemma w_map (f : R → S) (D : SatData R m) (j : Fin 3) (x : ZMod m) :
    (D.map f).w j x = f (D.w j x) := rfl
@[simp] lemma ε₁_map (f : R → S) (D : SatData R m) : (D.map f).ε₁ = f D.ε₁ := rfl
@[simp] lemma ε₂_map (f : R → S) (D : SatData R m) : (D.map f).ε₂ = f D.ε₂ := rfl

/-- The reduction mod `m` of an integral datum, `red D`. -/
def red (D : SatData ℤ m) : SatData (ZMod m) m := D.map (Int.cast : ℤ → ZMod m)

end SatData

/-! ### Sum-zero functions and admissible data -/

section SumZero

variable (R : Type*) [CommRing R] (m : ℕ) [NeZero m]

/-- The sum map `f ↦ Σ_{x ∈ ZMod m} f(x)`. -/
def sumMap : (ZMod m → R) →ₗ[R] R where
  toFun f := ∑ x, f x
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- The sum-zero functions `ZMod m → R`. -/
def sumZero : Submodule R (ZMod m → R) := LinearMap.ker (sumMap R m)

variable {R m}

@[simp] lemma sumMap_apply (f : ZMod m → R) : sumMap R m f = ∑ x, f x := rfl

lemma mem_sumZero {f : ZMod m → R} : f ∈ sumZero R m ↔ ∑ x, f x = 0 := Iff.rfl

variable (R m)

/-- The nine sums of a datum: `(Σ a_j, Σ b_j, Σ w_j)`. -/
def satSums : SatData R m →ₗ[R] (Fin 3 → R) × (Fin 3 → R) × (Fin 3 → R) where
  toFun D := (fun j => ∑ x, D.a j x, fun j => ∑ x, D.b j x, fun j => ∑ x, D.w j x)
  map_add' D E := by
    ext j <;> simp [Finset.sum_add_distrib]
  map_smul' c D := by
    ext j <;> simp [Finset.mul_sum]

/-- The admissible data: all nine functions `a_j, b_j, w_j` are sum-zero. -/
def SatSrc : Submodule R (SatData R m) := LinearMap.ker (satSums R m)

variable {R m}

lemma mem_satSrc {D : SatData R m} :
    D ∈ SatSrc R m ↔ ∀ j, D.a j ∈ sumZero R m ∧ D.b j ∈ sumZero R m ∧ D.w j ∈ sumZero R m := by
  simp only [SatSrc, LinearMap.mem_ker, satSums, LinearMap.coe_mk, AddHom.coe_mk, mem_sumZero,
    Prod.ext_iff, funext_iff, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩ j; exact ⟨h1 j, h2 j, h3 j⟩
  · intro h; exact ⟨fun j => (h j).1, fun j => (h j).2.1, fun j => (h j).2.2⟩

end SumZero

/-! ### The map `satMap` and the lattice `SAT` -/

section SatMap

variable (R : Type*) [CommRing R] (m : ℕ)

/-- The value of `satMap D` at the line `(j, k, l)`. -/
def satFun (D : SatData R m) : Line m → R
  | (0, k, l) => D.a 0 k + D.b 0 l + D.w 0 (k - l) + D.w 2 (k + l) + D.ε₁
  | (1, k, l) => D.a 1 k + D.b 1 l + D.w 0 (k - l) + D.w 1 (k + l) + (D.ε₂ - D.ε₁)
  | (2, k, l) => D.a 2 k + D.b 2 l + D.w 1 (k + l) + D.w 2 (k - l - 1) - D.ε₂

/-- The `R`-linear map `satMap : SatData R m → (Line m → R)`. -/
def satMap : SatData R m →ₗ[R] (Line m → R) where
  toFun := satFun R m
  map_add' D E := by
    ext ⟨j, k, l⟩
    fin_cases j <;> simp [satFun] <;> ring
  map_smul' c D := by
    ext ⟨j, k, l⟩
    fin_cases j <;> simp [satFun] <;> ring

variable {R m}

@[simp] lemma satMap_apply_zero (D : SatData R m) (k l : ZMod m) :
    satMap R m D (0, k, l) = D.a 0 k + D.b 0 l + D.w 0 (k - l) + D.w 2 (k + l) + D.ε₁ := rfl
@[simp] lemma satMap_apply_one (D : SatData R m) (k l : ZMod m) :
    satMap R m D (1, k, l) =
      D.a 1 k + D.b 1 l + D.w 0 (k - l) + D.w 1 (k + l) + (D.ε₂ - D.ε₁) := rfl
@[simp] lemma satMap_apply_two (D : SatData R m) (k l : ZMod m) :
    satMap R m D (2, k, l) =
      D.a 2 k + D.b 2 l + D.w 1 (k + l) + D.w 2 (k - l - 1) - D.ε₂ := rfl

variable (m) in
/-- The saturation lattice `SAT m ⊆ A m`: the image of the admissible integral data. -/
noncomputable def SAT [NeZero m] : Submodule ℤ (A m) := (SatSrc ℤ m).map (satMap ℤ m)

end SatMap

/-! ### (W2.a) Dimensions -/

section Finrank

variable {R : Type*} [Field R] {m : ℕ} [NeZero m]

lemma sumMap_surjective : Function.Surjective (sumMap R m) := fun c =>
  ⟨Pi.single 0 c, by simp⟩

/-- **(W2.a)** The sum-zero functions `ZMod m → R` form a space of dimension `m - 1`
(for any field `R`; in particular for `R = ZMod m`, `m` prime). -/
theorem finrank_sumZero : Module.finrank R (sumZero R m) = m - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumMap R m)
  rw [LinearMap.range_eq_top.mpr sumMap_surjective, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, ZMod.card] at h
  rw [sumZero]; omega

lemma satSums_surjective : Function.Surjective (satSums R m) := by
  rintro ⟨u, v, s⟩
  refine ⟨SatData.mk (fun j => Pi.single 0 (u j)) (fun j => Pi.single 0 (v j))
    (fun j => Pi.single 0 (s j)) 0 0, ?_⟩
  simp [satSums]

/-- **(W2.a)** The admissible data form a space of dimension `9(m - 1) + 2 = 9m - 7`. -/
theorem finrank_satSrc : Module.finrank R (SatSrc R m) = 9 * m - 7 := by
  have h := LinearMap.finrank_range_add_finrank_ker (satSums R m)
  rw [LinearMap.range_eq_top.mpr satSums_surjective, finrank_top] at h
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_self] at h
  have h3 : Module.finrank R (Fin 3 → ZMod m → R) = 3 * m := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card, ZMod.card]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [SatSrc]
  omega

end Finrank

/-! ### (W2.b) Compatibility with reduction mod `m` -/

section Compat

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- `satMap` commutes with applying a ring map entrywise. -/
theorem satMap_map (f : R →+* S) (D : SatData R m) :
    (fun p => f (satMap R m D p)) = satMap S m (D.map f) := by
  ext ⟨j, k, l⟩
  fin_cases j <;> simp

/-- **(W2.b)** `red ∘ satMap ℤ D = satMap (ZMod m) (red D)`. -/
theorem satMap_red (D : SatData ℤ m) :
    (fun p => ((satMap ℤ m D p : ℤ) : ZMod m)) = satMap (ZMod m) m D.red :=
  satMap_map (Int.castRingHom (ZMod m)) D

variable [NeZero m]

lemma map_mem_sumZero (f : R →+* S) {g : ZMod m → R} (hg : g ∈ sumZero R m) :
    (fun x => f (g x)) ∈ sumZero S m := by
  rw [mem_sumZero] at *
  rw [← map_sum, hg, map_zero]

/-- Applying a ring map entrywise preserves admissibility. -/
theorem map_mem_satSrc (f : R →+* S) {D : SatData R m} (hD : D ∈ SatSrc R m) :
    D.map f ∈ SatSrc S m := by
  rw [mem_satSrc] at *
  intro j
  exact ⟨map_mem_sumZero f (hD j).1, map_mem_sumZero f (hD j).2.1,
    map_mem_sumZero f (hD j).2.2⟩

/-- **(W2.b)** `red` maps `SatSrc ℤ` into `SatSrc (ZMod m)`. -/
theorem red_mem_satSrc {D : SatData ℤ m} (hD : D ∈ SatSrc ℤ m) : D.red ∈ SatSrc (ZMod m) m :=
  map_mem_satSrc (Int.castRingHom (ZMod m)) hD

/-- The explicit lift of `f : ZMod m → ZMod m`: `x ↦ (f x).val`, corrected at `0` by the
total sum. -/
def sumZeroLift (f : ZMod m → ZMod m) : ZMod m → ℤ :=
  fun x => ((f x).val : ℤ) - if x = 0 then ∑ y, ((f y).val : ℤ) else 0

lemma sumZeroLift_mem (f : ZMod m → ZMod m) : sumZeroLift f ∈ sumZero ℤ m := by
  rw [mem_sumZero]
  simp [sumZeroLift, Finset.sum_sub_distrib]

lemma cast_sumZeroLift {f : ZMod m → ZMod m} (hf : f ∈ sumZero (ZMod m) m) :
    (fun x => ((sumZeroLift f x : ℤ) : ZMod m)) = f := by
  rw [mem_sumZero] at hf
  ext x
  simp only [sumZeroLift, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
  split_ifs
  · push_cast; simp [hf]
  · simp

/-- **(W2.b)** Every sum-zero `f : ZMod m → ZMod m` is the reduction of a sum-zero
`y : ZMod m → ℤ`. -/
theorem exists_sumZero_lift {f : ZMod m → ZMod m} (hf : f ∈ sumZero (ZMod m) m) :
    ∃ y ∈ sumZero ℤ m, (fun x => ((y x : ℤ) : ZMod m)) = f :=
  ⟨sumZeroLift f, sumZeroLift_mem f, cast_sumZeroLift hf⟩

/-- **(W2.b)** `red` maps `SatSrc ℤ` onto `SatSrc (ZMod m)`. -/
theorem exists_satSrc_lift {E : SatData (ZMod m) m} (hE : E ∈ SatSrc (ZMod m) m) :
    ∃ D ∈ SatSrc ℤ m, D.red = E := by
  rw [mem_satSrc] at hE
  refine ⟨SatData.mk (fun j => sumZeroLift (E.a j)) (fun j => sumZeroLift (E.b j))
    (fun j => sumZeroLift (E.w j)) (E.ε₁.val : ℤ) (E.ε₂.val : ℤ), ?_, ?_⟩
  · rw [mem_satSrc]
    intro j
    exact ⟨sumZeroLift_mem _, sumZeroLift_mem _, sumZeroLift_mem _⟩
  · rw [SatData.ext_iff']
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext j x
      exact congrFun (cast_sumZeroLift (hE j).1) x
    · ext j x
      exact congrFun (cast_sumZeroLift (hE j).2.1) x
    · ext j x
      exact congrFun (cast_sumZeroLift (hE j).2.2) x
    · simp [SatData.red]
    · simp [SatData.red]

end Compat

/-! ### (W2.c) Lemma C -/

namespace LemmaC

variable {m : ℕ} [NeZero m]

/-- The second difference `(Δ²w)(x) = w(x+2) − 2w(x+1) + w(x)`. -/
def secondDiff (w : ZMod m → ZMod m) (x : ZMod m) : ZMod m := w (x + 2) - 2 * w (x + 1) + w x

omit [NeZero m] in
/-- Step 1: the mixed difference of a family identity. -/
lemma mixed_diff {a b w u : ZMod m → ZMod m} (h : ∀ k l, a k + b l + w (k - l) + u (k + l) = 0)
    (k l : ZMod m) : secondDiff u (k + l) = secondDiff w (k - l - 1) := by
  have h1 := h (k + 1) (l + 1)
  have h2 := h (k + 1) l
  have h3 := h k (l + 1)
  have h4 := h k l
  rw [show k + 1 - (l + 1) = k - l by ring, show k + 1 + (l + 1) = k + l + 2 by ring] at h1
  rw [show k + 1 - l = k - l - 1 + 2 by ring, show k + 1 + l = k + l + 1 by ring] at h2
  rw [show k - (l + 1) = k - l - 1 by ring, show k + (l + 1) = k + l + 1 by ring] at h3
  unfold secondDiff
  rw [show k - l - 1 + 1 = k - l by ring]
  linear_combination h1 - h2 - h3 + h4

/-- Step 3: a function with constant second difference `2c` is a quadratic. -/
lemma eq_quad_of_secondDiff {w : ZMod m → ZMod m} {c : ZMod m}
    (h : ∀ x, secondDiff w x = 2 * c) (x : ZMod m) :
    w x = c * x ^ 2 + (w 1 - w 0 - c) * x + w 0 := by
  have key : ∀ n : ℕ, w n = c * (n : ZMod m) ^ 2 + (w 1 - w 0 - c) * n + w 0 ∧
      w ((n : ZMod m) + 1) = c * ((n : ZMod m) + 1) ^ 2 + (w 1 - w 0 - c) * (n + 1) + w 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ⟨by rw [Nat.cast_succ]; exact ih.2, ?_⟩
      have hn := h n
      unfold secondDiff at hn
      rw [Nat.cast_succ, show (n : ZMod m) + 1 + 1 = n + 2 by ring]
      linear_combination hn + 2 * ih.2 - ih.1
  have := (key x.val).1
  rwa [ZMod.natCast_zmod_val] at this

variable [Fact m.Prime]

omit [NeZero m] in
lemma two_ne_zero (hm : 5 ≤ m) : (2 : ZMod m) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

omit [NeZero m] in
lemma three_ne_zero (hm : 5 ≤ m) : (3 : ZMod m) ≠ 0 := by
  intro h
  have : ((3 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

omit [NeZero m] in
/-- Step 2: the two second differences occurring in a family identity are one constant. -/
lemma secondDiff_eq {a b w u : ZMod m → ZMod m} (hm : 5 ≤ m)
    (h : ∀ k l, a k + b l + w (k - l) + u (k + l) = 0) (x y : ZMod m) :
    secondDiff u x = secondDiff w y := by
  have h2 := two_ne_zero hm
  have e := mixed_diff h ((x + y + 1) / 2) ((x - y - 1) / 2)
  rwa [show (x + y + 1) / 2 + (x - y - 1) / 2 = x by field_simp; ring,
    show (x + y + 1) / 2 - (x - y - 1) / 2 - 1 = y by field_simp; ring] at e

lemma sum_id_eq_zero (hm : 5 ≤ m) : ∑ x : ZMod m, x = 0 := by
  have := Equiv.sum_comp (Equiv.neg (ZMod m)) (fun x => x)
  simp only [Equiv.neg_apply] at this
  rw [Finset.sum_neg_distrib] at this
  have h' : 2 * ∑ x : ZMod m, x = 0 := by linear_combination -this
  exact (mul_eq_zero.mp h').resolve_left (two_ne_zero hm)

lemma sum_sq_eq_zero (hm : 5 ≤ m) : ∑ x : ZMod m, x ^ 2 = 0 := by
  have := Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod m) (two_ne_zero hm)) (fun x => x ^ 2)
  simp only [Equiv.mulLeft₀_apply, mul_pow] at this
  rw [← Finset.mul_sum] at this
  have h' : 3 * ∑ x : ZMod m, x ^ 2 = 0 := by linear_combination this
  exact (mul_eq_zero.mp h').resolve_left (three_ne_zero hm)

/-- Step 5: a quadratic on `ZMod m` is sum-zero when `m ≥ 5` is prime. -/
lemma quad_mem_sumZero (hm : 5 ≤ m) (c α β : ZMod m) :
    (fun x : ZMod m => c * x ^ 2 + α * x + β) ∈ sumZero (ZMod m) m := by
  rw [mem_sumZero, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_id_eq_zero hm, sum_sq_eq_zero hm]
  simp [Finset.card_univ, ZMod.card]

/-- The axis functions `a_j` of the 12-parameter family (see `param`). -/
def paramA (v : Fin 12 → ZMod m) : Fin 3 → ZMod m → ZMod m
  | 0, k => -2 * v 0 * k ^ 2 - (v 1 + v 3) * k + v 9
  | 1, k => -2 * v 0 * k ^ 2 - (v 1 + v 2) * k + v 10
  | 2, k => -2 * v 0 * k ^ 2 - (v 2 + v 3 - 2 * v 0) * k + v 11

/-- The axis functions `b_j` of the 12-parameter family (see `param`). -/
def paramB (v : Fin 12 → ZMod m) : Fin 3 → ZMod m → ZMod m
  | 0, l => -2 * v 0 * l ^ 2 - (v 3 - v 1) * l - (v 9 + v 4 + v 6 + v 7)
  | 1, l => -2 * v 0 * l ^ 2 - (v 2 - v 1) * l - (v 10 + v 4 + v 5 + (v 8 - v 7))
  | 2, l => -2 * v 0 * l ^ 2 - (v 2 - v 3 + 2 * v 0) * l - (v 11 + v 0 + v 5 + v 6 - v 3 - v 8)

/-- The overlap functions `w_i(x) = c x² + α_i x + β_i` of the 12-parameter family. -/
def paramW (v : Fin 12 → ZMod m) : Fin 3 → ZMod m → ZMod m
  | 0, x => v 0 * x ^ 2 + v 1 * x + v 4
  | 1, x => v 0 * x ^ 2 + v 2 * x + v 5
  | 2, x => v 0 * x ^ 2 + v 3 * x + v 6

/-- The 12-parameter family of kernel elements, with parameters
`v = (c, α₀, α₁, α₂, β₀, β₁, β₂, ε₁, ε₂, t₀, t₁, t₂)`: `w_i(x) = c x² + α_i x + β_i`,
`a_j(0) = t_j`, and `a_j, b_j` determined by the three family identities. -/
def param : (Fin 12 → ZMod m) →ₗ[ZMod m] SatData (ZMod m) m where
  toFun v := SatData.mk (paramA v) (paramB v) (paramW v) (v 7) (v 8)
  map_add' v v' := by
    rw [SatData.ext_iff']
    refine ⟨?_, ?_, ?_, rfl, rfl⟩ <;>
    · funext j x
      fin_cases j <;> simp [paramA, paramB, paramW] <;> ring
  map_smul' c v := by
    rw [SatData.ext_iff']
    refine ⟨?_, ?_, ?_, rfl, rfl⟩ <;>
    · funext j x
      fin_cases j <;> simp [paramA, paramB, paramW] <;> ring

/-- Reading the parameters off a datum (a left inverse of `param`). -/
noncomputable def readOff (D : SatData (ZMod m) m) : Fin 12 → ZMod m :=
  let c := (D.w 0 1 + D.w 0 (-1) - 2 * D.w 0 0) / 2
  ![c, D.w 0 1 - D.w 0 0 - c, D.w 1 1 - D.w 1 0 - c, D.w 2 1 - D.w 2 0 - c,
    D.w 0 0, D.w 1 0, D.w 2 0, D.ε₁, D.ε₂, D.a 0 0, D.a 1 0, D.a 2 0]

omit [NeZero m] in
lemma readOff_param (hm : 5 ≤ m) (v : Fin 12 → ZMod m) : readOff (param v) = v := by
  have h2 := two_ne_zero hm
  funext i
  fin_cases i <;> simp [readOff, param, paramW, paramA] <;> field_simp <;> ring

omit [NeZero m] in
lemma param_injective (hm : 5 ≤ m) : Function.Injective (param (m := m)) :=
  Function.LeftInverse.injective (readOff_param hm)

lemma param_mem_satSrc (hm : 5 ≤ m) (v : Fin 12 → ZMod m) : param v ∈ SatSrc (ZMod m) m := by
  rw [mem_satSrc]
  intro j
  fin_cases j <;> refine ⟨?_, ?_, ?_⟩ <;> rw [mem_sumZero] <;>
    simp [param, paramA, paramB, paramW, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_sq_eq_zero hm, Finset.card_univ] <;>
    rw [← Finset.mul_sum, sum_id_eq_zero hm, mul_zero]

omit [NeZero m] in
lemma satMap_param (v : Fin 12 → ZMod m) : satMap (ZMod m) m (param v) = 0 := by
  ext ⟨j, k, l⟩
  fin_cases j <;> simp [param, paramA, paramB, paramW] <;> ring

lemma param_readOff (hm : 5 ≤ m) {D : SatData (ZMod m) m} (hD : satMap (ZMod m) m D = 0) :
    param (readOff D) = D := by
  have h2 := two_ne_zero hm
  have hr : ∀ j k l, satMap (ZMod m) m D (j, k, l) = 0 := fun j k l => congrFun hD (j, k, l)
  have h0 : ∀ k l, (D.a 0 k + D.ε₁) + D.b 0 l + D.w 0 (k - l) + D.w 2 (k + l) = 0 := by
    intro k l; have := hr 0 k l; rw [satMap_apply_zero] at this; linear_combination this
  have h1 : ∀ k l, (D.a 1 k + (D.ε₂ - D.ε₁)) + D.b 1 l + D.w 0 (k - l) + D.w 1 (k + l) = 0 := by
    intro k l; have := hr 1 k l; rw [satMap_apply_one] at this; linear_combination this
  set c := (D.w 0 1 + D.w 0 (-1) - 2 * D.w 0 0) / 2 with hc
  have hsd : secondDiff (D.w 0) (-1) = 2 * c := by
    rw [hc, secondDiff, show (-1 : ZMod m) + 2 = 1 by ring, show (-1 : ZMod m) + 1 = 0 by ring]
    field_simp; ring
  have sd0 : ∀ x, secondDiff (D.w 0) x = 2 * c := fun x => by
    rw [← secondDiff_eq hm h0 0 x, secondDiff_eq hm h0 0 (-1), hsd]
  have sd2 : ∀ x, secondDiff (D.w 2) x = 2 * c := fun x => by
    rw [secondDiff_eq hm h0 x (-1), hsd]
  have sd1 : ∀ x, secondDiff (D.w 1) x = 2 * c := fun x => by
    rw [secondDiff_eq hm h1 x (-1), hsd]
  have q0 := eq_quad_of_secondDiff sd0
  have q1 := eq_quad_of_secondDiff sd1
  have q2 := eq_quad_of_secondDiff sd2
  have g0 : ∀ k l, satMap (ZMod m) m D (0, k, l) = 0 := hr 0
  have g1 : ∀ k l, satMap (ZMod m) m D (1, k, l) = 0 := hr 1
  have g2 : ∀ k l, satMap (ZMod m) m D (2, k, l) = 0 := hr 2
  simp only [satMap_apply_zero, satMap_apply_one, satMap_apply_two] at g0 g1 g2
  rw [SatData.ext_iff']
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · funext j k
    fin_cases j <;> simp [param, paramA, readOff, ← hc]
    · have e1 := g0 k 0; have e0 := g0 0 0
      simp only [sub_zero, add_zero] at e1 e0
      linear_combination -e1 + e0 + q0 k + q2 k
    · have e1 := g1 k 0; have e0 := g1 0 0
      simp only [sub_zero, add_zero] at e1 e0
      linear_combination -e1 + e0 + q0 k + q1 k
    · have e1 := g2 k 0; have e0 := g2 0 0
      simp only [sub_zero, add_zero, zero_sub] at e1 e0
      linear_combination -e1 + e0 + q1 k + q2 (k - 1) - q2 (-1)
  · funext j l
    fin_cases j <;> simp [param, paramB, readOff, ← hc]
    · have e1 := g0 0 l
      simp only [zero_sub, zero_add] at e1
      linear_combination -e1 + q0 (-l) + q2 l
    · have e1 := g1 0 l
      simp only [zero_sub, zero_add] at e1
      linear_combination -e1 + q0 (-l) + q1 l
    · have e1 := g2 0 l
      simp only [zero_sub, zero_add] at e1
      linear_combination -e1 + q1 l + q2 (-l - 1)
  · funext j x
    fin_cases j <;> simp [param, paramW, readOff, ← hc]
    · linear_combination -q0 x
    · linear_combination -q1 x
    · linear_combination -q2 x

end LemmaC

section LemmaCMain

variable {m : ℕ} [Fact m.Prime]

open LemmaC in
/-- **(W2.c) Lemma C**, the description of the kernel: for `m ≥ 5` prime, the kernel of
`satMap` on the admissible data is exactly the image of the injective map `param` from `F^12`. -/
theorem map_ker_satMap_eq (hm : 5 ≤ m) :
    (LinearMap.ker ((satMap (ZMod m) m).domRestrict (SatSrc (ZMod m) m))).map
      (SatSrc (ZMod m) m).subtype = LinearMap.range (param (m := m)) := by
  ext D
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply,
    Submodule.coe_subtype, LinearMap.mem_range]
  constructor
  · rintro ⟨D', hD', rfl⟩
    exact ⟨readOff D', param_readOff hm hD'⟩
  · rintro ⟨v, rfl⟩
    exact ⟨⟨param v, param_mem_satSrc hm v⟩, satMap_param v, rfl⟩

/-- **(W2.c) Lemma C.** For `m ≥ 5` prime, the kernel of `satMap` restricted to the admissible
data over `ZMod m` has dimension `12`. -/
theorem finrank_ker_satMap (hm : 5 ≤ m) :
    Module.finrank (ZMod m)
      (LinearMap.ker ((satMap (ZMod m) m).domRestrict (SatSrc (ZMod m) m))) = 12 := by
  rw [(Submodule.equivMapOfInjective _ (SatSrc (ZMod m) m).injective_subtype _).finrank_eq,
    map_ker_satMap_eq hm, LinearMap.finrank_range_of_inj (LemmaC.param_injective hm),
    Module.finrank_fin_fun]

/-- **(W2.c) Lemma C.** For `m ≥ 5` prime, the image of the admissible data under `satMap` over
`ZMod m` has dimension `9m - 19`. -/
theorem finrank_range_satMap (hm : 5 ≤ m) :
    Module.finrank (ZMod m)
      (LinearMap.range ((satMap (ZMod m) m).domRestrict (SatSrc (ZMod m) m))) = 9 * m - 19 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((satMap (ZMod m) m).domRestrict (SatSrc (ZMod m) m))
  rw [finrank_ker_satMap hm, finrank_satSrc] at h
  omega

end LemmaCMain

end Watermark
