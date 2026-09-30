module

public import Mathlib

/-!
# The Watermark Theorem, piece W1: definitions

The line configuration `I = Fin 3 × ZMod m × ZMod m`, its Gram matrix `G`, the lattice
`A = I → ℤ`, the kernel `K = ker G`, the quotient `V = A ⧸ K` with the induced bilinear form,
the family vectors `N_j`, the augmentation, and the pencils `π` with their operators `E_π`.

Everything is stated for an arbitrary natural number `m`; wherever a finite sum over the lines
is needed we assume `[NeZero m]` (so that `ZMod m` is a `Fintype`).
-/

@[expose] public section

open Matrix

namespace Watermark

/-- The set `P = ZMod m × ZMod m` of points `(k, l)`. -/
abbrev Point (m : ℕ) : Type := ZMod m × ZMod m

/-- The set `I = Fin 3 × P` of lines `(j, k, l)`; `j = 0, 1, 2` stands for families 1, 2, 3. -/
abbrev Line (m : ℕ) : Type := Fin 3 × Point m

/-- The Gram entry `G p p'` in the cases `j ≤ j'` (upper block triangle), as in the Setting:
same family, families `(0,1)`, `(1,2)` and `(0,2)`.  For `j > j'` it returns `0`, but it is
never used there (see `gram`). -/
def gramUpper (m : ℕ) (p q : Line m) : ℤ :=
  if p.1 = q.1 then
    (if p.2 = q.2 then 2 - (m : ℤ)
     else if p.2.1 = q.2.1 ∨ p.2.2 = q.2.2 then 1 else 0)
  else if p.1 = 0 ∧ q.1 = 1 then
    (if p.2.1 - p.2.2 = q.2.1 - q.2.2 then 1 else 0)
  else if p.1 = 1 ∧ q.1 = 2 then
    (if p.2.1 + p.2.2 = q.2.1 + q.2.2 then 1 else 0)
  else if p.1 = 0 ∧ q.1 = 2 then
    (if q.2.1 - q.2.2 = p.2.1 + p.2.2 + 1 then 1 else 0)
  else 0

/-- The Gram matrix `G : Matrix I I ℤ`.  For `j ≤ j'` it is given by `gramUpper`, and for
`j > j'` it is defined by symmetry: `G p p' := G p' p`. -/
def gram (m : ℕ) : Matrix (Line m) (Line m) ℤ :=
  Matrix.of fun p q => if p.1 ≤ q.1 then gramUpper m p q else gramUpper m q p

/-- The lattice `A = I → ℤ`. -/
abbrev A (m : ℕ) : Type := Line m → ℤ

/-- `G` acting on `A`: `(G x)(p) = Σ_{p'} G p p' · x(p')`. -/
noncomputable def gramLin (m : ℕ) [NeZero m] : A m →ₗ[ℤ] A m :=
  (gram m).mulVecLin

/-- The kernel `K = ker G`, a `ℤ`-submodule of `A`. -/
noncomputable def K (m : ℕ) [NeZero m] : Submodule ℤ (A m) :=
  LinearMap.ker (gramLin m)

/-- The quotient lattice `V = A ⧸ K`. -/
abbrev V (m : ℕ) [NeZero m] : Type := A m ⧸ K m

/-- The bilinear form `B(x, y) = Σ_{p,p'} x(p) · G p p' · y(p')` on `A`. -/
noncomputable def gramForm (m : ℕ) [NeZero m] : LinearMap.BilinForm ℤ (A m) :=
  Matrix.toLinearMap₂' ℤ (gram m)

/-- The indicator `N_j ∈ A` of family `j`. -/
def famVec (m : ℕ) (j : Fin 3) : A m := fun p => if p.1 = j then 1 else 0

/-- The all-ones vector `𝟙 ∈ A`. -/
def ones (m : ℕ) : A m := fun _ => 1

/-- The restriction `x_j : P → ℤ` of `x ∈ A` to family `j`. -/
def restrict {m : ℕ} (x : A m) (j : Fin 3) : Point m → ℤ := fun q => x (j, q)

/-- The augmentation `aug(u) = Σ_{(k,l) ∈ P} u(k,l)` of a function `u : P → ℤ`;
for `x ∈ A`, `aug(x_j)` is `aug (restrict x j)`. -/
def aug {m : ℕ} [NeZero m] (u : Point m → ℤ) : ℤ := ∑ q, u q

/-- The `m + 1` pencils, indexed by `Option (ZMod m)`: `some t` is `π_t(k, l) = k + t·l` and
`none` is `π_∞(k, l) = l`. -/
def pencil {m : ℕ} : Option (ZMod m) → Point m → ZMod m
  | some t => fun q => q.1 + t * q.2
  | none => fun q => q.2

/-- For a pencil (or any map) `π : P → ZMod m` and `u : P → ℤ`,
`(E_π u)(p) = Σ_{p' ∈ P, π(p') = π(p)} u(p')`. -/
def E {m : ℕ} [NeZero m] (π : Point m → ZMod m) (u : Point m → ℤ) (p : Point m) : ℤ :=
  ∑ q ∈ Finset.univ.filter (fun q => π q = π p), u q

/-! ### Basic API -/

section API

variable {m : ℕ}

lemma gram_apply (p q : Line m) :
    gram m p q = if p.1 ≤ q.1 then gramUpper m p q else gramUpper m q p := rfl

lemma gramUpper_same_family {p q : Line m} (h : p.1 = q.1) :
    gramUpper m p q = gramUpper m q p := by
  unfold gramUpper
  rw [if_pos h, if_pos h.symm]
  by_cases h2 : p.2 = q.2
  · rw [if_pos h2, if_pos h2.symm]
  · rw [if_neg h2, if_neg (Ne.symm h2)]
    simp only [eq_comm]

/-- **(W1.a) Symmetry.** `Gᵀ = G`. -/
theorem gram_transpose : (gram m)ᵀ = gram m := by
  ext p q
  simp only [transpose_apply, gram_apply]
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · rw [if_neg (not_le.mpr h), if_pos h.le]
  · rw [if_pos h.le, if_pos h.ge, gramUpper_same_family h.symm]
  · rw [if_pos h.le, if_neg (not_le.mpr h)]

lemma gram_symm (p q : Line m) : gram m p q = gram m q p := by
  conv_rhs => rw [← gram_transpose]
  rfl

variable [NeZero m]

lemma gramLin_apply (x : A m) : gramLin m x = gram m *ᵥ x := rfl

lemma mem_K {x : A m} : x ∈ K m ↔ gram m *ᵥ x = 0 := Iff.rfl

lemma gramForm_apply (x y : A m) : gramForm m x y = x ⬝ᵥ (gram m *ᵥ y) :=
  Matrix.toLinearMap₂'_apply' _ _ _

lemma gramForm_apply_sum (x y : A m) :
    gramForm m x y = ∑ p, ∑ q, x p * gram m p q * y q := by
  rw [gramForm, Matrix.toLinearMap₂'_apply]
  simp only [smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma gramForm_comm (x y : A m) : gramForm m x y = gramForm m y x := by
  rw [gramForm_apply, gramForm_apply, dotProduct_mulVec, ← mulVec_transpose, gram_transpose,
    dotProduct_comm]

lemma gramForm_isSymm : (gramForm m).IsSymm := ⟨gramForm_comm⟩

lemma gramForm_eq_zero_of_mem_K_right (x : A m) {y : A m} (hy : y ∈ K m) :
    gramForm m x y = 0 := by
  rw [gramForm_apply, mem_K.mp hy, dotProduct_zero]

lemma gramForm_eq_zero_of_mem_K_left {x : A m} (hx : x ∈ K m) (y : A m) :
    gramForm m x y = 0 := by
  rw [gramForm_comm, gramForm_eq_zero_of_mem_K_right y hx]

end API

/-- `B` with the second argument descended to `V`. -/
noncomputable def gramFormAux (m : ℕ) [NeZero m] : V m →ₗ[ℤ] A m →ₗ[ℤ] ℤ :=
  (K m).liftQ (gramForm m).flip (fun y hy => LinearMap.ext fun x => by
    simp [gramForm_eq_zero_of_mem_K_right x hy])

lemma gramFormAux_mk {m : ℕ} [NeZero m] (x y : A m) :
    gramFormAux m (Submodule.Quotient.mk y) x = gramForm m x y := rfl

/-- The symmetric bilinear form on `V = A ⧸ K` induced by `B`. -/
noncomputable def formV (m : ℕ) [NeZero m] : LinearMap.BilinForm ℤ (V m) :=
  (K m).liftQ (gramFormAux m).flip (fun x hx => by
    refine Submodule.linearMap_qext _ ?_
    ext y
    simp [gramFormAux_mk, gramForm_eq_zero_of_mem_K_left hx])

section FormV

variable {m : ℕ} [NeZero m]

@[simp] lemma formV_mk (x y : A m) :
    formV m (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = gramForm m x y := rfl

lemma formV_mkQ (x y : A m) :
    formV m ((K m).mkQ x) ((K m).mkQ y) = gramForm m x y := rfl

/-- The induced form on `V` is symmetric. -/
theorem formV_isSymm : (formV m).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => simp only [formV_mk, gramForm_comm]

end FormV

end Watermark
