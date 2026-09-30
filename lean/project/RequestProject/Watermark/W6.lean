module

public import RequestProject.Watermark.W5

/-!
# The Watermark Theorem, piece W6: the sublattice `F`, its Gram matrix, and `[A : F + K]`

Throughout, `m` is prime (`[Fact m.Prime]`) and `m ≥ 5`.

* `blk j π`: the block of pencil `π` on family `j`, the image of `sumZero ℤ m` under
  `u ↦ pb j π u` (`pbLin j π` is `pb j π` as a linear map).
* `FIdx m`: the index set of the `3(m − 3) + 3` spanning blocks of `F`: `inl (j, t)` for a family
  `j` and a live non-overlap slope `t` (`LiveT m`), and `inr 0, inr 1, inr 2` for the overlap
  members `blk 0 (−1)`, `blk 1 (1)`, `blk 0 (1)`.  `β.fam` and `β.pen` are the family and pencil.
* `F m`: the sum of the blocks `blk β.fam β.pen` and of `ℤ · famVec m 0`.
* `Lfam m ⊆ (Point m → ℤ)`: the span of `1` and of all `u ∘ pencil π`, `u ∈ sumZero ℤ m`;
  `L m = {x | ∀ j, restrict x j ∈ Lfam m}`.

Indices are stated as `(N).toAddSubgroup.index` for a `ℤ`-submodule `N`.

Statements: (W6.a) `gramForm_pb_pb_of_ne`, `gramForm_famVec_pb`, `gramForm_pb_pb_self`,
`gramForm_famVec_self`; (W6.b) `F_inf_K`, `finrank_F`; (W6.c) `index_Lfam`;
(W6.d) `F_sup_SAT`, `index_F_sup_SAT`; (W6.e) `index_F_sup_K`.
-/

@[expose] public section

open Matrix

namespace Watermark

/-! ### Definitions -/

section Defs

variable {m : ℕ}

/-- `u ↦ pb j π u` as a `ℤ`-linear map `(ZMod m → ℤ) → A m`. -/
def pbLin (j : Fin 3) (π : Option (ZMod m)) : (ZMod m → ℤ) →ₗ[ℤ] A m where
  toFun := pb j π
  map_add' u v := by
    ext p; simp only [pb, Pi.add_apply]; split_ifs <;> simp
  map_smul' c u := by
    ext p; simp only [pb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

@[simp] lemma pbLin_apply (j : Fin 3) (π : Option (ZMod m)) (u : ZMod m → ℤ) :
    pbLin j π u = pb j π u := rfl

variable (m) in
/-- The block of the pencil `π` on family `j`: the image of `sumZero ℤ m` under
`u ↦ pb j π u`. -/
def blk [NeZero m] (j : Fin 3) (π : Option (ZMod m)) : Submodule ℤ (A m) :=
  (sumZero ℤ m).map (pbLin j π)

variable (m) in
/-- The live non-overlap slopes `t ∉ {0, 1, −1}`. -/
abbrev LiveT : Type := {t : ZMod m // t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1}

variable (m) in
/-- The index set of the spanning blocks of `F`: `inl (j, t)` is `blk j (some t)` for a live
non-overlap slope `t`; `inr 0`, `inr 1`, `inr 2` are `blk 0 (some (−1))`, `blk 1 (some 1)`,
`blk 0 (some 1)`. -/
abbrev FIdx : Type := (Fin 3 × LiveT m) ⊕ Fin 3

/-- The family of a spanning block. -/
def FIdx.fam : FIdx m → Fin 3
  | .inl (j, _) => j
  | .inr i => ![0, 1, 0] i

/-- The pencil of a spanning block. -/
def FIdx.pen : FIdx m → Option (ZMod m)
  | .inl (_, t) => some t.1
  | .inr i => ![some (-1), some 1, some 1] i

variable (m) in
/-- The sublattice `F`: the sum of the `3(m − 3) + 3` spanning blocks and of `ℤ · famVec m 0`. -/
def F [NeZero m] : Submodule ℤ (A m) :=
  (⨆ β : FIdx m, blk m β.fam β.pen) ⊔ Submodule.span ℤ {famVec m 0}

variable (m) in
/-- `Lfam m`: the span of the constant function `1` and of all `u ∘ pencil π`, for
`π : Option (ZMod m)` and `u ∈ sumZero ℤ m`. -/
def Lfam [NeZero m] : Submodule ℤ (Point m → ℤ) :=
  Submodule.span ℤ
    (insert (fun _ => 1) {f | ∃ π : Option (ZMod m), ∃ u ∈ sumZero ℤ m, f = u ∘ pencil π})

variable (m) in
/-- `L m = {x ∈ A m | ∀ j, restrict x j ∈ Lfam m}`. -/
def L [NeZero m] : Submodule ℤ (A m) where
  carrier := {x | ∀ j, restrict x j ∈ Lfam m}
  add_mem' hx hy j := (Lfam m).add_mem (hx j) (hy j)
  zero_mem' _ := (Lfam m).zero_mem
  smul_mem' c _ hx j := (Lfam m).smul_mem c (hx j)

lemma mem_L [NeZero m] {x : A m} : x ∈ L m ↔ ∀ j, restrict x j ∈ Lfam m := Iff.rfl

end Defs

/-! ### (W6.a) The Gram matrix of `F` -/

namespace W6

variable {m : ℕ}

lemma dotProduct_pb_pb [NeZero m] (j j' : Fin 3) (π π' : Option (ZMod m)) (u v : ZMod m → ℤ) :
    pb j π u ⬝ᵥ pb j' π' v =
      if j = j' then ∑ q : Point m, u (pencil π q) * v (pencil π' q) else 0 := by
  simp only [dotProduct, pb, Fintype.sum_prod_type, ite_mul, mul_ite, mul_zero, zero_mul]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  · refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun q _ => ?_
    by_cases h1 : b = j
    · subst h1; simp [h]
    · simp [h1]

lemma dotProduct_pb_pb_of_ne [Fact m.Prime] {j j' : Fin 3} {π π' : Option (ZMod m)}
    (h : (j, π) ≠ (j', π')) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) (v : ZMod m → ℤ) :
    pb j π u ⬝ᵥ pb j' π' v = 0 := by
  rw [dotProduct_pb_pb]
  split_ifs with hj
  · subst hj
    have hπ : π ≠ π' := fun hπ => h (by rw [hπ])
    rw [sum_pencil_mul_pencil hπ, mem_sumZero.mp hu, zero_mul]
  · rfl

lemma dotProduct_pb_pb_self [NeZero m] (j : Fin 3) (π : Option (ZMod m)) (u v : ZMod m → ℤ) :
    pb j π u ⬝ᵥ pb j π v = m * ∑ x, u x * v x := by
  rw [dotProduct_pb_pb, if_pos rfl, sum_pencil_mul_same]

lemma one_ne_neg_one (hm : 5 ≤ m) : (1 : ZMod m) ≠ -1 := fun h =>
  two_ne_zero_zmod hm (by linear_combination h)

lemma FIdx.pen_inr (i : Fin 3) :
    FIdx.pen (m := m) (.inr i) = some 1 ∨ FIdx.pen (m := m) (.inr i) = some (-1) := by
  fin_cases i <;> simp [FIdx.pen]

/-- Distinct spanning blocks have distinct (family, pencil). -/
lemma FIdx.pos_injective (hm : 5 ≤ m) {β β' : FIdx m} (h : β ≠ β') :
    (β.fam, β.pen) ≠ (β'.fam, β'.pen) := by
  have h1 := one_ne_neg_one hm
  intro he
  simp only [Prod.mk.injEq] at he
  obtain ⟨hf, hp⟩ := he
  rcases β with ⟨j, t, ht⟩ | i <;> rcases β' with ⟨j', t', ht'⟩ | i'
  · simp only [FIdx.fam, FIdx.pen, Option.some.injEq] at hf hp
    subst hf; subst hp; exact h rfl
  · rcases FIdx.pen_inr (m := m) i' with h' | h' <;> rw [h'] at hp <;>
      simp only [FIdx.pen, Option.some.injEq] at hp
    · exact ht.2.1 hp
    · exact ht.2.2 hp
  · rcases FIdx.pen_inr (m := m) i with h' | h' <;> rw [h'] at hp <;>
      simp only [FIdx.pen, Option.some.injEq] at hp
    · exact ht'.2.1 hp.symm
    · exact ht'.2.2 hp.symm
  · fin_cases i <;> fin_cases i' <;> simp [FIdx.fam, FIdx.pen] at hf hp h ⊢ <;>
      first | exact h1 hp | exact h1 hp.symm

/-- For a spanning block, `G · pb β v = −m • pb β v + m • pb j' π' v'` with `(j', π')` not
the position of any spanning block. -/
lemma gram_mulVec_pb_FIdx (hm : 5 ≤ m) [Fact m.Prime] (β : FIdx m) {v : ZMod m → ℤ}
    (hv : v ∈ sumZero ℤ m) :
    ∃ j' π' v', (∀ β' : FIdx m, (β'.fam, β'.pen) ≠ (j', π')) ∧ v' ∈ sumZero ℤ m ∧
      gram m *ᵥ pb β.fam β.pen v = -(m : ℤ) • pb β.fam β.pen v + (m : ℤ) • pb j' π' v' := by
  have hodd := W4.odd_of_prime_of_five_le hm
  have h1 := one_ne_neg_one hm
  rcases β with ⟨j, t, ht⟩ | i
  · refine ⟨j, none, 0, fun β' => ?_, (sumZero ℤ m).zero_mem, ?_⟩
    · rcases β' with ⟨_, _⟩ | i <;> [simp [FIdx.pen]; fin_cases i <;> simp [FIdx.pen]]
    · have hz : pb (m := m) j none 0 = 0 := by ext p; simp [pb]
      rw [hz, smul_zero, add_zero]
      exact gram_mulVec_pb_live j ht.1 ht.2.1 ht.2.2 hv
  · fin_cases i
    · refine ⟨1, some (-1), v, fun β' => ?_, hv, gram_mulVec_pb_zero_neg_one hodd hv⟩
      rcases β' with ⟨_, t, ht⟩ | i
      · simp [FIdx.pen, ht.2.2]
      · fin_cases i <;> simp [FIdx.fam, FIdx.pen, h1]
    · refine ⟨2, some 1, v, fun β' => ?_, hv, gram_mulVec_pb_one_one hodd hv⟩
      rcases β' with ⟨_, t, ht⟩ | i
      · simp [FIdx.pen, ht.2.1]
      · fin_cases i <;> simp [FIdx.fam, FIdx.pen]
    · refine ⟨2, some (-1), fun x => v (x - 1), fun β' => ?_, ?_,
        gram_mulVec_pb_zero_one hodd hv⟩
      · rcases β' with ⟨_, t, ht⟩ | i
        · simp [FIdx.pen, ht.2.2]
        · fin_cases i <;> simp [FIdx.fam, FIdx.pen]
      · rw [mem_sumZero, W3.sum_comp_sub_right v 1]; exact mem_sumZero.mp hv

end W6

open W6

variable {m : ℕ} [Fact m.Prime]

/-- **(W6.a.1)** Two different spanning blocks of `F` are `B`-orthogonal. -/
theorem gramForm_pb_pb_of_ne (hm : 5 ≤ m) {β β' : FIdx m} (h : β ≠ β') {u v : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) (hv : v ∈ sumZero ℤ m) :
    gramForm m (pb β.fam β.pen u) (pb β'.fam β'.pen v) = 0 := by
  obtain ⟨j', π', v', hpos, hv', he⟩ := gram_mulVec_pb_FIdx hm β' hv
  rw [gramForm_apply, he, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_pb_pb_of_ne (FIdx.pos_injective hm h) hu,
    dotProduct_pb_pb_of_ne (hpos β) hu]
  simp

/-- **(W6.a.1)** `B(famVec m 0, pb j π u) = 0` for every sum-zero `u` (every `j`, `π`). -/
theorem gramForm_famVec_pb (j : Fin 3) (π : Option (ZMod m)) {u : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) : gramForm m (famVec m 0) (pb j π u) = 0 := by
  rw [gramForm_famVec]
  have h : ∑ p, pb j π u p = pb j π u ⬝ᵥ pb j π (fun _ => 1) := by
    simp only [dotProduct, pb]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [h, dotProduct_pb_pb_self]
  simp [mem_sumZero.mp hu]

/-- **(W6.a.2)** Inside one spanning block, `B(pb u, pb v) = −m² · Σ_x u(x) v(x)`. -/
theorem gramForm_pb_pb_self (hm : 5 ≤ m) (β : FIdx m) {u v : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) (hv : v ∈ sumZero ℤ m) :
    gramForm m (pb β.fam β.pen u) (pb β.fam β.pen v) = -(m : ℤ) ^ 2 * ∑ x, u x * v x := by
  obtain ⟨j', π', v', hpos, hv', he⟩ := gram_mulVec_pb_FIdx hm β hv
  rw [gramForm_apply, he, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_pb_pb_self, dotProduct_pb_pb_of_ne (hpos β) hu]
  simp only [smul_eq_mul]
  ring

/-- **(W6.a.3)** `B(famVec m 0, famVec m 0) = m³`. -/
theorem gramForm_famVec_self : gramForm m (famVec m 0) (famVec m 0) = (m : ℤ) ^ 3 := by
  rw [gramForm_famVec, Fintype.sum_prod_type, Finset.sum_eq_single (0 : Fin 3)
    (fun b _ hb => by simp [famVec, hb]) (by simp)]
  simp [famVec, ZMod.card]
  ring

/-! ### (W6.b) `F ∩ K = 0` and the rank of `F` -/

namespace W6

omit [Fact m.Prime] in
lemma pb_zero (j : Fin 3) (π : Option (ZMod m)) : pb j π (0 : ZMod m → ℤ) = 0 := by
  ext p; simp [pb]

/-- The parametrisation of `F`: `(u, c) ↦ Σ_β pb β (u β) + c • famVec m 0`. -/
noncomputable def paramF : (FIdx m → sumZero ℤ m) × ℤ →ₗ[ℤ] A m :=
  (∑ β : FIdx m, (pbLin β.fam β.pen).comp
      ((sumZero ℤ m).subtype.comp ((LinearMap.proj β).comp (LinearMap.fst ℤ _ ℤ)))) +
    (LinearMap.snd ℤ (FIdx m → sumZero ℤ m) ℤ).smulRight (famVec m 0)

lemma paramF_apply (x : (FIdx m → sumZero ℤ m) × ℤ) :
    paramF x = ∑ β, pb β.fam β.pen (x.1 β) + x.2 • famVec m 0 := by
  simp [paramF]

lemma range_paramF : LinearMap.range (paramF (m := m)) = F m := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [paramF_apply]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun β _ => ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_iSup_of_mem β ⟨x.1 β, (x.1 β).2, rfl⟩)
    · exact Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
  · refine sup_le (iSup_le fun β => ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨(Pi.single β ⟨u, hu⟩, 0), ?_⟩
      rw [paramF_apply, Finset.sum_eq_single β
        (fun b _ hb => by simp [hb, pb_zero]) (by simp)]
      simp
    · rw [Submodule.span_le]
      rintro _ rfl
      exact ⟨(0, 1), by simp [paramF_apply, pb_zero]⟩

lemma gramForm_pb_paramF (hm : 5 ≤ m) (x : (FIdx m → sumZero ℤ m) × ℤ) (β : FIdx m) :
    gramForm m (pb β.fam β.pen (x.1 β)) (paramF x) =
      -(m : ℤ) ^ 2 * ∑ y, (x.1 β : ZMod m → ℤ) y * (x.1 β : ZMod m → ℤ) y := by
  rw [paramF_apply, map_add, map_sum, map_zsmul, gramForm_comm _ (famVec m 0),
    gramForm_famVec_pb _ _ (x.1 β).2, smul_zero, add_zero,
    Finset.sum_eq_single β (fun b _ hb => gramForm_pb_pb_of_ne hm (Ne.symm hb) (x.1 β).2
      (x.1 b).2) (by simp), gramForm_pb_pb_self hm β (x.1 β).2 (x.1 β).2]

lemma eq_zero_of_paramF_mem_K (hm : 5 ≤ m) {x : (FIdx m → sumZero ℤ m) × ℤ}
    (hx : paramF x ∈ K m) : x = 0 := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have h1 : x.1 = 0 := by
    funext β
    have h := gramForm_eq_zero_of_mem_K_right (pb β.fam β.pen (x.1 β)) hx
    rw [gramForm_pb_paramF hm] at h
    have hs : ∑ y, (x.1 β : ZMod m → ℤ) y * (x.1 β : ZMod m → ℤ) y = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (neg_eq_zero.mp h) (pow_ne_zero 2 hm0)
      · exact h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_self_nonneg _)] at hs
    exact Subtype.ext (funext fun y => mul_self_eq_zero.mp (hs y (Finset.mem_univ _)))
  have h2 : x.2 = 0 := by
    have h := gramForm_eq_zero_of_mem_K_right (famVec m 0) hx
    rw [paramF_apply, h1] at h
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero, pb_zero, Finset.sum_const_zero,
      zero_add, map_zsmul, gramForm_famVec_self, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 3 hm0)
  exact Prod.ext h1 h2

lemma paramF_injective (hm : 5 ≤ m) : Function.Injective (paramF (m := m)) := by
  intro x y h
  have : paramF (x - y) ∈ K m := by
    rw [map_sub, h, sub_self]; exact (K m).zero_mem
  exact sub_eq_zero.mp (eq_zero_of_paramF_mem_K hm this)

lemma finrank_sumZero_int : Module.finrank ℤ (sumZero ℤ m) = m - 1 := by
  have hs : Function.Surjective (sumMap ℤ m) := fun c => ⟨Pi.single 0 c, by simp⟩
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker (sumMap ℤ m))
  rw [(LinearMap.quotKerEquivOfSurjective _ hs).finrank_eq, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, ZMod.card] at h
  change Module.finrank ℤ (LinearMap.ker (sumMap ℤ m)) = _
  omega

lemma card_LiveT (hm : 5 ≤ m) : Fintype.card (LiveT m) = m - 3 := by
  rw [Fintype.card_subtype]
  have e : (Finset.univ.filter fun t : ZMod m => t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1) =
      Finset.univ \ {0, 1, -1} := by
    ext t; simp
  have h3 : ({0, 1, -1} : Finset (ZMod m)).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨0, 1, -1, zero_ne_one, ?_, one_ne_neg_one hm, rfl⟩
    intro h; exact one_ne_zero (neg_eq_zero.mp h.symm)
  rw [e, Finset.card_univ_diff, h3, ZMod.card]

lemma card_FIdx (hm : 5 ≤ m) : Fintype.card (FIdx m) = 3 * (m - 3) + 3 := by
  simp [Fintype.card_sum, Fintype.card_prod, card_LiveT hm]

end W6

/-- **(W6.b)** `F ⊓ K = ⊥`. -/
theorem F_inf_K (hm : 5 ≤ m) : F m ⊓ K m = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyF, hyK⟩
  rw [← range_paramF] at hyF
  obtain ⟨x, rfl⟩ := hyF
  rw [eq_zero_of_paramF_mem_K hm hyK, map_zero]
  exact (⊥ : Submodule ℤ (A m)).zero_mem

/-- **(W6.b)** `rank F = 3(m − 1)(m − 2) + 1`. -/
theorem finrank_F (hm : 5 ≤ m) : Module.finrank ℤ (F m) = 3 * (m - 1) * (m - 2) + 1 := by
  rw [← range_paramF, LinearMap.finrank_range_of_inj (paramF_injective hm),
    Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self]
  simp only [finrank_sumZero_int, Finset.sum_const, Finset.card_univ, card_FIdx hm, smul_eq_mul]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  rw [show n + 5 - 3 = n + 2 by omega, show n + 5 - 1 = n + 4 by omega,
    show n + 5 - 2 = n + 3 by omega]
  ring

/-! ### (W6.c) The index of `Lfam` -/

namespace W6

omit [Fact m.Prime] in
lemma comp_pencil_mem_Lfam [NeZero m] (π : Option (ZMod m)) {u : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) : u ∘ pencil π ∈ Lfam m :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨π, u, hu, rfl⟩)

omit [Fact m.Prime] in
lemma one_mem_Lfam [NeZero m] : (fun _ => 1 : Point m → ℤ) ∈ Lfam m :=
  Submodule.subset_span (Set.mem_insert _ _)

omit [Fact m.Prime] in
lemma even_exp : 2 ∣ m ^ 2 + m + 2 := by
  have : Even (m * (m + 1)) := Nat.even_mul_succ_self m
  obtain ⟨k, hk⟩ := this
  exact ⟨k + 1, by nlinarith⟩


variable (m) in
/-- Index set of the basis of `Lfam`: the constant `1`, and `(x, π)` with `x ≠ 0`. -/
abbrev BIdx : Type := Unit ⊕ ({x : ZMod m // x ≠ 0} × Option (ZMod m))

/-- The function `δ_x − δ_0 : ZMod m → ℤ`. -/
def dd (x : ZMod m) : ZMod m → ℤ := fun y => (if y = x then 1 else 0) - (if y = 0 then 1 else 0)

/-- The basis vectors of `Lfam`: `1` and `(δ_x − δ_0) ∘ pencil π` (`x ≠ 0`). -/
def bvec : BIdx m → Point m → ℤ
  | .inl _ => fun _ => 1
  | .inr (x, π) => dd x.1 ∘ pencil π

/-- The standard Gram matrix of the basis vectors. -/
def gramL : Matrix (BIdx m) (BIdx m) ℤ := Matrix.of fun i j => ∑ q, bvec i q * bvec j q

lemma sum_dd (x : ZMod m) : ∑ z, dd x z = 0 := by
  simp [dd, Finset.sum_sub_distrib]

lemma sum_dd_mul {x y : ZMod m} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∑ z, dd x z * dd y z = (if x = y then 1 else 0) + 1 := by
  simp only [dd, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp [hx, hy, eq_comm]

lemma gramL_eq : gramL (m := m) = Matrix.fromBlocks (Matrix.of fun _ _ => (m : ℤ) ^ 2) 0 0
    (Matrix.blockDiagonal fun _ => (m : ℤ) • (1 + Matrix.of fun _ _ => 1)) := by
  ext (i | ⟨x, π⟩) (j | ⟨y, π'⟩)
  · simp [gramL, bvec, ZMod.card]; ring
  · have := sum_pencil_mul_same π' (dd y.1) (fun _ => 1)
    simp only [mul_one] at this
    simp only [gramL, bvec, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, Function.comp_apply,
      one_mul, Matrix.zero_apply]
    rw [this, sum_dd, mul_zero]
  · have := sum_pencil_mul_same π (dd x.1) (fun _ => 1)
    simp only [mul_one] at this
    simp only [gramL, bvec, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Function.comp_apply,
      mul_one, Matrix.zero_apply]
    rw [this, sum_dd, mul_zero]
  · simp only [gramL, bvec, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.blockDiagonal_apply, Function.comp_apply]
    split_ifs with h
    · subst h
      rw [sum_pencil_mul_same, sum_dd_mul x.2 y.2]
      simp [Matrix.one_apply, Subtype.ext_iff]
    · rw [sum_pencil_mul_pencil h, sum_dd, zero_mul]

lemma card_ne_zero : Fintype.card {x : ZMod m // x ≠ 0} = m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]

lemma det_gramL : (gramL (m := m)).det = (m : ℤ) ^ (m ^ 2 + m + 2) := by
  rw [gramL_eq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_blockDiagonal]
  have hJ : (Matrix.of fun _ _ => 1 : Matrix {x : ZMod m // x ≠ 0} {x : ZMod m // x ≠ 0} ℤ) =
      Matrix.replicateCol Unit (fun _ => (1 : ℤ)) * Matrix.replicateRow Unit (fun _ => (1 : ℤ)) := by
    ext a b; simp [Matrix.mul_apply]
  have hdet : ((m : ℤ) • (1 + Matrix.of fun _ _ => 1 :
      Matrix {x : ZMod m // x ≠ 0} {x : ZMod m // x ≠ 0} ℤ)).det = (m : ℤ) ^ m := by
    rw [Matrix.det_smul, hJ, Matrix.det_one_add_replicateCol_mul_replicateRow, card_ne_zero]
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, card_ne_zero,
      nsmul_eq_mul]
    have h1 : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
    rw [Nat.cast_sub h1, Nat.cast_one, show (1 : ℤ) + ((m : ℤ) - 1) = m by ring,
      ← pow_succ, Nat.sub_add_cancel h1]
  simp only [hdet, Finset.prod_const, Finset.card_univ, Fintype.card_option, ZMod.card,
    Matrix.of_apply]
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

lemma card_BIdx : Fintype.card (BIdx m) = Fintype.card (Point m) := by
  rw [Fintype.card_sum, Fintype.card_prod, card_ne_zero, Fintype.card_option, Fintype.card_unit,
    Fintype.card_prod, ZMod.card]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.ne m; omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- An enumeration of `Point m` by `BIdx m` (both have `m²` elements). -/
noncomputable def epsB : BIdx m ≃ Point m := Fintype.equivOfCardEq card_BIdx

/-- The square matrix of the basis vectors in the coordinates of `Point m ≃ BIdx m`. -/
noncomputable def matB : Matrix (BIdx m) (BIdx m) ℤ := Matrix.of fun i k => bvec i (epsB k)

lemma gramL_eq_mul : gramL (m := m) = matB * matBᵀ := by
  ext i j
  simp only [gramL, matB, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact (Equiv.sum_comp epsB (fun q => bvec i q * bvec j q)).symm

lemma bvec_linearIndependent : LinearIndependent ℤ (bvec (m := m)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : ∀ q, ∑ i, c i * bvec i q = 0 := fun q => by
    have := congrFun hc q
    simpa [Finset.sum_apply] using this
  have hv : c ᵥ* gramL = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, gramL, Matrix.of_apply, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun q _ => ?_
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hq, zero_mul]
  have hdet : (gramL (m := m)).det ≠ 0 := by
    rw [det_gramL]; exact pow_ne_zero _ (by exact_mod_cast NeZero.ne m)
  exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv) i

lemma sum_mul_dd {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) (v : ZMod m) :
    ∑ x : {x : ZMod m // x ≠ 0}, u x * dd x v = u v := by
  have h1 : ∑ x : {x : ZMod m // x ≠ 0}, u x * dd x v =
      ∑ x ∈ Finset.univ.erase 0, u x * dd x v :=
    (Finset.sum_subtype (Finset.univ.erase 0) (fun x => by simp)
      (fun x => u x * dd x v)).symm
  rw [h1, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp [dd, mul_sub, Finset.sum_sub_distrib, mem_sumZero.mp hu]

lemma span_bvec : Submodule.span ℤ (Set.range (bvec (m := m))) = Lfam m := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | ⟨x, π⟩, rfl⟩
    · exact one_mem_Lfam
    · exact comp_pencil_mem_Lfam π (mem_sumZero.mpr (sum_dd x.1))
  · rw [Lfam, Submodule.span_le]
    rintro f (rfl | ⟨π, u, hu, rfl⟩)
    · exact Submodule.subset_span ⟨.inl (), rfl⟩
    · have e : u ∘ pencil π = ∑ x : {x : ZMod m // x ≠ 0}, u x • bvec (.inr (x, π)) := by
        funext q
        simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, bvec, smul_eq_mul]
        exact (sum_mul_dd hu _).symm
      rw [e]
      exact Submodule.sum_mem _ fun x _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- A `ℤ`-basis of `Lfam m`, indexed by `BIdx m`. -/
noncomputable def basisL : Module.Basis (BIdx m) ℤ (Lfam m) :=
  (Module.Basis.span bvec_linearIndependent).map (LinearEquiv.ofEq _ _ span_bvec)

lemma basisL_apply (i : BIdx m) : (basisL i : Point m → ℤ) = bvec i := by
  simp [basisL, Module.Basis.span_apply]

end W6

/-- **(W6.c)** `[Point m → ℤ : Lfam m] = m ^ ((m² + m + 2)/2)`.  This holds for every prime `m`
(the hypothesis `m ≥ 5` is not needed).  Proof: `W6.basisL` is a basis of `Lfam m` (the constant
`1` and the `(δ_x − δ_0) ∘ pencil π`, `x ≠ 0`); the index is `|det|` of its matrix `W6.matB`, and
`det(matB)² = det(matB · matBᵀ) = m^(m² + m + 2)` (`W6.det_gramL`: the standard Gram matrix is
block diagonal with blocks `m²` and `m · (I + J)`). -/
theorem index_Lfam : (Lfam m).toAddSubgroup.index = m ^ ((m ^ 2 + m + 2) / 2) := by
  set bE := (Pi.basisFun ℤ (Point m)).reindex epsB.symm
  have h := Submodule.natAbs_det_basis_change bE (Lfam m) basisL
  have hdet : bE.det ((↑) ∘ basisL) = (matB (m := m)).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp [bE, Module.Basis.toMatrix_apply, basisL_apply, matB]
  change Nat.card (_ ⧸ Lfam m) = _
  rw [← h, hdet]
  have hsq : (matB (m := m)).det * (matB (m := m)).det = (m : ℤ) ^ (m ^ 2 + m + 2) := by
    rw [← det_gramL, gramL_eq_mul, Matrix.det_mul, Matrix.det_transpose]
  have hX : m ^ (m ^ 2 + m + 2) = (m ^ ((m ^ 2 + m + 2) / 2)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    obtain ⟨k, hk⟩ := even_exp (m := m)
    rw [hk]
    omega
  refine Nat.pow_left_injective two_ne_zero ?_
  simp only
  rw [← hX, ← Int.natAbs_pow, sq, hsq, Int.natAbs_pow, Int.natAbs_natCast]

/-! ### (W6.d) `F + SAT = L` -/

namespace W6

omit [Fact m.Prime] in
lemma restrict_pb (j j' : Fin 3) (π : Option (ZMod m)) (u : ZMod m → ℤ) :
    restrict (pb j π u) j' = if j' = j then u ∘ pencil π else 0 := by
  funext q; simp only [restrict, pb]; split_ifs <;> rfl

omit [Fact m.Prime] in
lemma pb_mem_L [NeZero m] (j : Fin 3) (π : Option (ZMod m)) {u : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) : pb j π u ∈ L m := fun j' => by
  rw [restrict_pb]; split_ifs
  · exact comp_pencil_mem_Lfam π hu
  · exact (Lfam m).zero_mem

omit [Fact m.Prime] in
lemma famVec_mem_L [NeZero m] (j : Fin 3) : famVec m j ∈ L m := fun j' => by
  have : restrict (famVec m j) j' = if j' = j then (fun _ => (1 : ℤ)) else (0 : Point m → ℤ) := by
    funext q; simp only [restrict, famVec]; split_ifs <;> rfl
  rw [this]; split_ifs
  · exact one_mem_Lfam
  · exact (Lfam m).zero_mem

lemma F_le_L : F m ≤ L m := by
  refine sup_le (iSup_le fun β => ?_) ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact pb_mem_L _ _ hu
  · rw [Submodule.span_le]
    rintro _ rfl
    exact famVec_mem_L 0

omit [Fact m.Prime] in
lemma SAT_le_L [NeZero m] : SAT m ≤ L m := by
  rintro _ ⟨D, hD, rfl⟩ j
  have hD' := mem_satSrc.mp hD
  have hc : ∀ c : ℤ, c • (fun _ => 1 : Point m → ℤ) ∈ Lfam m := fun c =>
    (Lfam m).smul_mem c one_mem_Lfam
  have hsh : (fun x => D.w 2 (x - 1)) ∈ sumZero ℤ m := by
    rw [mem_sumZero, W3.sum_comp_sub_right (D.w 2) 1]; exact (hD' 2).2.2
  fin_cases j
  · have e : restrict (satMap ℤ m D) 0 = D.a 0 ∘ pencil (some 0) + D.b 0 ∘ pencil none +
        D.w 0 ∘ pencil (some (-1)) + D.w 2 ∘ pencil (some 1) + D.ε₁ • (fun _ => 1) := by
      funext ⟨k, l⟩; simp [restrict, pencil, sub_eq_add_neg]
    rw [Fin.zero_eta, e]
    exact add_mem (add_mem (add_mem (add_mem (comp_pencil_mem_Lfam _ (hD' 0).1)
      (comp_pencil_mem_Lfam _ (hD' 0).2.1)) (comp_pencil_mem_Lfam _ (hD' 0).2.2))
      (comp_pencil_mem_Lfam _ (hD' 2).2.2)) (hc _)
  · have e : restrict (satMap ℤ m D) 1 = D.a 1 ∘ pencil (some 0) + D.b 1 ∘ pencil none +
        D.w 0 ∘ pencil (some (-1)) + D.w 1 ∘ pencil (some 1) +
          (D.ε₂ - D.ε₁) • (fun _ => 1) := by
      funext ⟨k, l⟩; simp [restrict, pencil, sub_eq_add_neg]
    rw [Fin.mk_one, e]
    exact add_mem (add_mem (add_mem (add_mem (comp_pencil_mem_Lfam _ (hD' 1).1)
      (comp_pencil_mem_Lfam _ (hD' 1).2.1)) (comp_pencil_mem_Lfam _ (hD' 0).2.2))
      (comp_pencil_mem_Lfam _ (hD' 1).2.2)) (hc _)
  · have e : restrict (satMap ℤ m D) 2 = D.a 2 ∘ pencil (some 0) + D.b 2 ∘ pencil none +
        D.w 1 ∘ pencil (some 1) + (fun x => D.w 2 (x - 1)) ∘ pencil (some (-1)) +
          (-D.ε₂) • (fun _ => 1) := by
      funext ⟨k, l⟩; simp [restrict, pencil, sub_eq_add_neg]
    rw [show ((⟨2, by norm_num⟩ : Fin 3)) = 2 from rfl, e]
    exact add_mem (add_mem (add_mem (add_mem (comp_pencil_mem_Lfam _ (hD' 2).1)
      (comp_pencil_mem_Lfam _ (hD' 2).2.1)) (comp_pencil_mem_Lfam _ (hD' 1).2.2))
      (comp_pencil_mem_Lfam _ hsh)) (hc _)

omit [Fact m.Prime] in
lemma satMap_mem_SAT [NeZero m] {D : SatData ℤ m} (hD : D ∈ SatSrc ℤ m) :
    satMap ℤ m D ∈ SAT m := ⟨D, hD, rfl⟩

omit [Fact m.Prime] in
lemma single_mem_sumZero [NeZero m] {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) (j j' : Fin 3) :
    (Pi.single j u : Fin 3 → ZMod m → ℤ) j' ∈ sumZero ℤ m := by
  by_cases h : j' = j
  · subst h; simpa using hu
  · simp [h, (sumZero ℤ m).zero_mem]

omit [Fact m.Prime] in
lemma mk_mem_satSrc [NeZero m] {a b w : Fin 3 → ZMod m → ℤ}
    (ha : ∀ j, a j ∈ sumZero ℤ m) (hb : ∀ j, b j ∈ sumZero ℤ m) (hw : ∀ j, w j ∈ sumZero ℤ m)
    (e₁ e₂ : ℤ) : SatData.mk a b w e₁ e₂ ∈ SatSrc ℤ m :=
  mem_satSrc.mpr fun j => ⟨ha j, hb j, hw j⟩

omit [Fact m.Prime] in
lemma zero_fun_mem [NeZero m] (j : Fin 3) : (0 : Fin 3 → ZMod m → ℤ) j ∈ sumZero ℤ m :=
  (sumZero ℤ m).zero_mem

lemma pb_FIdx_mem_F (β : FIdx m) {u : ZMod m → ℤ} (hu : u ∈ sumZero ℤ m) :
    pb β.fam β.pen u ∈ F m :=
  Submodule.mem_sup_left (Submodule.mem_iSup_of_mem β ⟨u, hu, rfl⟩)

lemma pb_mem_F_sup_SAT (hm : 5 ≤ m) (j : Fin 3) (π : Option (ZMod m)) {u : ZMod m → ℤ}
    (hu : u ∈ sumZero ℤ m) : pb j π u ∈ F m ⊔ SAT m := by
  have h1 := one_ne_neg_one hm
  rcases π with _ | t
  · -- axis pencil `∞`
    have hD := mk_mem_satSrc zero_fun_mem (single_mem_sumZero hu j) zero_fun_mem 0 0
    have e : satMap ℤ m (SatData.mk 0 (Pi.single j u) 0 0 0) = pb j none u := by
      ext ⟨j', k, l⟩; fin_cases j' <;> fin_cases j <;> simp [pb, pencil]
    exact Submodule.mem_sup_right (e ▸ satMap_mem_SAT hD)
  by_cases h0 : t = 0
  · -- axis pencil `0`
    subst h0
    have hD := mk_mem_satSrc (single_mem_sumZero hu j) zero_fun_mem zero_fun_mem 0 0
    have e : satMap ℤ m (SatData.mk (Pi.single j u) 0 0 0 0) = pb j (some 0) u := by
      ext ⟨j', k, l⟩; fin_cases j' <;> fin_cases j <;> simp [pb, pencil]
    exact Submodule.mem_sup_right (e ▸ satMap_mem_SAT hD)
  by_cases ht1 : t = 1
  · subst ht1
    fin_cases j
    · exact Submodule.mem_sup_left (pb_FIdx_mem_F (.inr 2) hu)
    · exact Submodule.mem_sup_left (pb_FIdx_mem_F (.inr 1) hu)
    · have hD := mk_mem_satSrc zero_fun_mem zero_fun_mem (single_mem_sumZero hu 1) 0 0
      have e : pb 2 (some 1) u =
          satMap ℤ m (SatData.mk 0 0 (Pi.single 1 u) 0 0) - pb 1 (some 1) u := by
        ext ⟨j', k, l⟩; fin_cases j' <;> simp [pb, pencil]
      change pb 2 (some 1) u ∈ _
      rw [e]
      exact sub_mem (Submodule.mem_sup_right (satMap_mem_SAT hD))
        (Submodule.mem_sup_left (pb_FIdx_mem_F (.inr 1) hu))
  by_cases ht2 : t = -1
  · subst ht2
    fin_cases j
    · exact Submodule.mem_sup_left (pb_FIdx_mem_F (.inr 0) hu)
    · have hD := mk_mem_satSrc zero_fun_mem zero_fun_mem (single_mem_sumZero hu 0) 0 0
      have e : pb 1 (some (-1)) u =
          satMap ℤ m (SatData.mk 0 0 (Pi.single 0 u) 0 0) - pb 0 (some (-1)) u := by
        ext ⟨j', k, l⟩; fin_cases j' <;> simp [pb, pencil, sub_eq_add_neg]
      change pb 1 (some (-1)) u ∈ _
      rw [e]
      exact sub_mem (Submodule.mem_sup_right (satMap_mem_SAT hD))
        (Submodule.mem_sup_left (pb_FIdx_mem_F (.inr 0) hu))
    · have hu' : (fun x => u (x + 1)) ∈ sumZero ℤ m := by
        rw [mem_sumZero, W3.sum_comp_add_right u 1]; exact mem_sumZero.mp hu
      have hD := mk_mem_satSrc zero_fun_mem zero_fun_mem (single_mem_sumZero hu' 2) 0 0
      have e : pb 2 (some (-1)) u =
          satMap ℤ m (SatData.mk 0 0 (Pi.single 2 (fun x => u (x + 1))) 0 0) -
            pb 0 (some 1) (fun x => u (x + 1)) := by
        ext ⟨j', k, l⟩; fin_cases j' <;> simp [pb, pencil, sub_eq_add_neg]
      change pb 2 (some (-1)) u ∈ _
      rw [e]
      exact sub_mem (Submodule.mem_sup_right (satMap_mem_SAT hD))
        (Submodule.mem_sup_left (pb_FIdx_mem_F (.inr 2) hu'))
  · exact Submodule.mem_sup_left (pb_FIdx_mem_F (.inl (j, ⟨t, h0, ht1, ht2⟩)) hu)

lemma famVec_mem_F_sup_SAT (j : Fin 3) : famVec m j ∈ F m ⊔ SAT m := by
  have h0 : famVec m 0 ∈ F m ⊔ SAT m :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span rfl))
  have hD1 := mk_mem_satSrc (m := m) zero_fun_mem zero_fun_mem zero_fun_mem 1 0
  have hD2 := mk_mem_satSrc (m := m) zero_fun_mem zero_fun_mem zero_fun_mem 0 1
  have e1 : famVec m 1 = famVec m 0 - satMap ℤ m (SatData.mk 0 0 0 1 0) := by
    ext ⟨j', k, l⟩; fin_cases j' <;> simp [famVec]
  have e2 : famVec m 2 = famVec m 1 - satMap ℤ m (SatData.mk 0 0 0 0 1) := by
    ext ⟨j', k, l⟩; fin_cases j' <;> simp [famVec]
  have h1 : famVec m 1 ∈ F m ⊔ SAT m := by
    rw [e1]; exact sub_mem h0 (Submodule.mem_sup_right (satMap_mem_SAT hD1))
  fin_cases j
  · exact h0
  · exact h1
  · change famVec m 2 ∈ _
    rw [e2]; exact sub_mem h1 (Submodule.mem_sup_right (satMap_mem_SAT hD2))

omit [Fact m.Prime] in
lemma ext_add (j : Fin 3) (y z : Point m → ℤ) : ext j (y + z) = ext j y + ext j z := by
  ext p; simp only [ext, Pi.add_apply]; split_ifs <;> simp

omit [Fact m.Prime] in
lemma ext_smul (j : Fin 3) (c : ℤ) (y : Point m → ℤ) : ext j (c • y) = c • ext j y := by
  ext p; simp only [ext, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

omit [Fact m.Prime] in
lemma ext_zero (j : Fin 3) : ext j (0 : Point m → ℤ) = 0 := by
  ext p; simp [ext]

lemma ext_mem_F_sup_SAT (hm : 5 ≤ m) (j : Fin 3) {y : Point m → ℤ} (hy : y ∈ Lfam m) :
    ext j y ∈ F m ⊔ SAT m := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨π, u, hu, rfl⟩
    · exact famVec_mem_F_sup_SAT j
    · exact pb_mem_F_sup_SAT hm j π hu
  | zero => rw [ext_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [ext_add]; exact add_mem hy hz
  | smul c y _ hy => rw [ext_smul]; exact Submodule.smul_mem _ c hy

omit [Fact m.Prime] in
lemma sum_ext_restrict (x : A m) : ∑ j, ext j (restrict x j) = x := by
  ext ⟨j', q⟩
  simp [ext, restrict, Finset.sum_apply]

/-- `x ↦ ([x_0], [x_1], [x_2])`, from `A m` to three copies of `(Point m → ℤ) ⧸ Lfam m`. -/
noncomputable def quotL : A m →ₗ[ℤ] (Fin 3 → (Point m → ℤ) ⧸ Lfam m) :=
  LinearMap.pi fun j => (Lfam m).mkQ ∘ₗ LinearMap.funLeft ℤ ℤ (fun q : Point m => (j, q))

lemma ker_quotL : LinearMap.ker (quotL (m := m)) = L m := by
  ext x
  simp only [LinearMap.mem_ker, quotL, funext_iff, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
  rfl

lemma quotL_surjective : Function.Surjective (quotL (m := m)) := by
  intro f
  choose g hg using fun j => Submodule.Quotient.mk_surjective (Lfam m) (f j)
  refine ⟨fun p => g p.1 p.2, funext fun j => ?_⟩
  simp only [quotL, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply]
  rw [← hg j]; rfl

lemma index_L : (L m).toAddSubgroup.index = (Lfam m).toAddSubgroup.index ^ 3 := by
  change Nat.card (A m ⧸ L m) = Nat.card ((Point m → ℤ) ⧸ Lfam m) ^ 3
  rw [← ker_quotL, Nat.card_congr (LinearMap.quotKerEquivOfSurjective _
    quotL_surjective).toEquiv, Nat.card_fun]
  simp

end W6

/-- **(W6.d)** `F + SAT = L`. -/
theorem F_sup_SAT (hm : 5 ≤ m) : F m ⊔ SAT m = L m := by
  refine le_antisymm (sup_le F_le_L SAT_le_L) fun x hx => ?_
  rw [← sum_ext_restrict x]
  exact Submodule.sum_mem _ fun j _ => ext_mem_F_sup_SAT hm j (hx j)

/-- **(W6.d)** `[A : F + SAT] = m ^ (3(m² + m + 2)/2)`. -/
theorem index_F_sup_SAT (hm : 5 ≤ m) :
    (F m ⊔ SAT m).toAddSubgroup.index = m ^ (3 * (m ^ 2 + m + 2) / 2) := by
  rw [F_sup_SAT hm, index_L, index_Lfam, ← pow_mul]
  obtain ⟨k, hk⟩ := even_exp (m := m)
  rw [hk]
  congr 1
  omega

/-! ### (W6.e) The index `[A : F + K]` -/

/-- **(W6.e)** `[A : F + K] = m ^ (3(m² + m + 2)/2 − 12)`. -/
theorem index_F_sup_K (hm : 5 ≤ m) :
    (F m ⊔ K m).toAddSubgroup.index = m ^ (3 * (m ^ 2 + m + 2) / 2 - 12) := by
  set H := (F m ⊔ SAT m).toAddSubgroup
  have hle : H ≤ (F m ⊔ K m).toAddSubgroup := sup_le_sup_left (SAT_le_K m) (F m)
  have hmul := AddSubgroup.relIndex_mul_index hle
  have hsup : (F m ⊔ K m).toAddSubgroup = (K m).toAddSubgroup ⊔ H := by
    have e : F m ⊔ K m = K m ⊔ (F m ⊔ SAT m) := le_antisymm
      (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
      (sup_le le_sup_right (sup_le le_sup_left ((SAT_le_K m).trans le_sup_right)))
    rw [e, Submodule.sup_toAddSubgroup]
  have hrel : H.relIndex (F m ⊔ K m).toAddSubgroup = m ^ 12 := by
    rw [hsup, AddSubgroup.relIndex_sup_right, AddSubgroup.relIndex, ← index_SAT hm]
    congr 1
    ext ⟨k, hk⟩
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, H,
      Submodule.mem_comap]
    constructor
    · intro h
      obtain ⟨f, hf, s, hs, rfl⟩ := Submodule.mem_sup.mp h
      have hfK : f ∈ K m := by
        have := sub_mem hk (SAT_le_K m hs)
        simpa using this
      have hf0 : f = 0 := by
        have : f ∈ F m ⊓ K m := ⟨hf, hfK⟩
        rw [F_inf_K hm] at this
        exact this
      simpa [hf0] using hs
    · intro h; exact Submodule.mem_sup_right h
  rw [hrel, index_F_sup_SAT hm] at hmul
  set n := 3 * (m ^ 2 + m + 2) / 2
  have hn : 12 ≤ n := by
    have : 25 ≤ m ^ 2 := by nlinarith
    omega
  have hpos : 0 < m ^ 12 := pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) 12
  rw [show n = 12 + (n - 12) by omega, pow_add] at hmul
  exact Nat.eq_of_mul_eq_mul_left hpos hmul

end Watermark
