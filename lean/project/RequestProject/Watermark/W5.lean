module

public import RequestProject.Watermark.W4

/-!
# The Watermark Theorem, piece W5: the kernel census, `mK ⊆ SAT`, and `[K : SAT] = m¹²`

Throughout, `m` is prime (`[Fact m.Prime]`), and `m ≥ 5` where needed.

* (W5.a) Census: `fib_live_const` (for `t ∉ {0, 1, −1}`, `fib (some t) x_j` is constant; this
  needs only `m` prime), `fib_overlap_zero_one`, `fib_overlap_one_two`, `fib_overlap_zero_two`.
* (W5.b) `smul_mem_SAT`: `(m : ℤ) • x ∈ SAT m` for `x ∈ K m`.  The datum is `W5.satD x`, with
  `W5.satMap_satD : satMap ℤ m (satD x) = m • x`.
* (W5.c) `finrank_K`: `Module.finrank ℤ (K m) = 9 * m - 7`.
* (W5.d) `index_SAT`: `((SAT m).comap (K m).subtype).toAddSubgroup.index = m ^ 12`.

For (W5.d), `W5.redK : K m → (Line m → ZMod m)` is reduction mod `m`, `W5.Kbar` its image (an
`F_m`-subspace of dimension `9m − 7`, `W5.finrank_Kbar`) and `W5.Sbar` the image of the admissible
data over `ZMod m` (dimension `9m − 19`, Lemma C).  `W5.mem_SAT_iff` shows that `SAT` is the full
preimage of `S̄` in `K`, so `[K : SAT] = |K̄ / S̄| = m ^ 12`.
-/

@[expose] public section

open Matrix

namespace Watermark

namespace W5

variable {m : ℕ} [NeZero m]

/-- For `x ∈ K`, `x ⬝ G v = 0` for every `v` (symmetry of `G`). -/
lemma dotProduct_gram_mulVec_eq_zero {x : A m} (hx : x ∈ K m) (v : A m) :
    x ⬝ᵥ (gram m *ᵥ v) = 0 := by
  rw [dotProduct_mulVec, ← gram_transpose, vecMul_transpose, mem_K.mp hx,
    zero_dotProduct]

/-- The fibre sums of `y` along a pencil add up to `aug y`. -/
lemma sum_fib (π : Option (ZMod m)) (y : Point m → ℤ) : ∑ v, fib π y v = aug y := by
  unfold fib aug
  exact Finset.sum_fiberwise _ _ _

/-- `x ⬝ pb j π u = Σ_v u(v) · fib π x_j (v)`. -/
lemma dotProduct_pb (x : A m) (j : Fin 3) (π : Option (ZMod m)) (u : ZMod m → ℤ) :
    x ⬝ᵥ pb j π u = ∑ v, u v * fib π (restrict x j) v := by
  have h1 : x ⬝ᵥ pb j π u = ∑ q : Point m, restrict x j q * u (pencil π q) := by
    simp only [dotProduct, pb, Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp [restrict]
  rw [h1]
  simp only [fib, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ (pencil π) (fun q => restrict x j q * u (pencil π q))]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun q hq => ?_
  rw [(Finset.mem_filter.mp hq).2, mul_comm]

/-- A function orthogonal to every sum-zero function is constant. -/
lemma const_of_orth {f : ZMod m → ℤ} (h : ∀ u ∈ sumZero ℤ m, ∑ v, u v * f v = 0) :
    ∃ c : ℤ, ∀ v, f v = c := by
  refine ⟨f 0, fun v => ?_⟩
  have hu : (Pi.single v 1 - Pi.single 0 1 : ZMod m → ℤ) ∈ sumZero ℤ m := by
    rw [mem_sumZero]; simp [Finset.sum_sub_distrib]
  have := h _ hu
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

/-- A constant sum-zero integer function vanishes. -/
lemma eq_zero_of_const {f : ZMod m → ℤ} (hf : f ∈ sumZero ℤ m) {c : ℤ} (hc : ∀ v, f v = c) :
    f = 0 := by
  rw [mem_sumZero] at hf
  simp only [hc, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hf
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hc0 : c = 0 := (mul_eq_zero.mp hf).resolve_left hm
  funext v; rw [hc, hc0]; rfl

/-- If `G · pb j π u = -m • pb j π u + m • pb j' π' u'`, then
`Σ u · fib π x_j = Σ u' · fib π' x_j'` for `x ∈ K`. -/
lemma orth_of_gram_pb {x : A m} (hx : x ∈ K m) {j j' : Fin 3} {π π' : Option (ZMod m)}
    {u u' : ZMod m → ℤ}
    (h : gram m *ᵥ pb j π u = -(m : ℤ) • pb j π u + (m : ℤ) • pb j' π' u') :
    ∑ v, u v * fib π (restrict x j) v = ∑ v, u' v * fib π' (restrict x j') v := by
  have e := dotProduct_gram_mulVec_eq_zero hx (pb j π u)
  rw [h, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_pb, dotProduct_pb,
    smul_eq_mul, smul_eq_mul] at e
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have : (m : ℤ) * (∑ v, u' v * fib π' (restrict x j') v - ∑ v, u v * fib π (restrict x j) v)
    = 0 := by linear_combination e
  linarith [(mul_eq_zero.mp this).resolve_left hm]

end W5

open W5

variable {m : ℕ} [Fact m.Prime]

/-- **(W5.a.1) Census, live pencils.** For `m ≥ 5` prime, `x ∈ K`, every family `j` and
every `t ∉ {0, 1, −1}`, the fibre sums `fib (some t) x_j` are constant. -/
theorem fib_live_const {x : A m} (hx : x ∈ K m) (j : Fin 3) {t : ZMod m} (h0 : t ≠ 0)
    (h1 : t ≠ 1) (h2 : t ≠ -1) : ∃ c : ℤ, ∀ v, fib (some t) (restrict x j) v = c := by
  refine const_of_orth fun u hu => ?_
  have := orth_of_gram_pb (j' := j) (π' := some t) (u' := 0) hx
    (by
      have hpb : pb j (some t) (0 : ZMod m → ℤ) = 0 := funext fun p => by simp [pb]
      rw [gram_mulVec_pb_live j h0 h1 h2 hu, hpb, smul_zero, add_zero])
  simpa using this

/-- **(W5.a.2) Census, overlap `(0,1)` at pencil `−1`.** -/
theorem fib_overlap_zero_one (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) :
    ∃ c : ℤ, ∀ v, fib (some (-1)) (restrict x 0) v - fib (some (-1)) (restrict x 1) v = c := by
  refine const_of_orth fun u hu => ?_
  have := orth_of_gram_pb hx (gram_mulVec_pb_zero_neg_one (W4.odd_of_prime_of_five_le hm) hu)
  simp only [mul_sub, Finset.sum_sub_distrib, this, sub_self]

/-- **(W5.a.2) Census, overlap `(1,2)` at pencil `1`.** -/
theorem fib_overlap_one_two (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) :
    ∃ c : ℤ, ∀ v, fib (some 1) (restrict x 1) v - fib (some 1) (restrict x 2) v = c := by
  refine const_of_orth fun u hu => ?_
  have := orth_of_gram_pb hx (gram_mulVec_pb_one_one (W4.odd_of_prime_of_five_le hm) hu)
  simp only [mul_sub, Finset.sum_sub_distrib, this, sub_self]

/-- **(W5.a.2) Census, overlap `(0,2)`**: `v ↦ fib (some 1) x_0 v − fib (some (−1)) x_2 (v + 1)`
is constant. -/
theorem fib_overlap_zero_two (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) :
    ∃ c : ℤ, ∀ v, fib (some 1) (restrict x 0) v - fib (some (-1)) (restrict x 2) (v + 1) = c := by
  refine const_of_orth fun u hu => ?_
  have := orth_of_gram_pb hx (gram_mulVec_pb_zero_one (W4.odd_of_prime_of_five_le hm) hu)
  have e : ∑ v, u (v - 1) * fib (some (-1)) (restrict x 2) v
      = ∑ v, u v * fib (some (-1)) (restrict x 2) (v + 1) :=
    (Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun v => by simp)).symm
  simp only [mul_sub, Finset.sum_sub_distrib, this, e, sub_self]

namespace W5

variable {m : ℕ} [Fact m.Prime]

/-- `μ_j = aug(x_j) / m`. -/
def mu (x : A m) (j : Fin 3) : ℤ := aug (restrict x j) / m

/-- `f̃_{j,π} = fib π x_j − μ_j`. -/
def ft (x : A m) (j : Fin 3) (π : Option (ZMod m)) (v : ZMod m) : ℤ :=
  fib π (restrict x j) v - mu x j

lemma aug_eq_mul_mu (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) (j : Fin 3) :
    aug (restrict x j) = m * mu x j :=
  (Int.mul_ediv_cancel' ((aug_of_mem_K hm hx).2 j)).symm

lemma sum_mu (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) : mu x 0 + mu x 1 + mu x 2 = 0 := by
  have h := (aug_of_mem_K hm hx).1
  rw [aug_eq_mul_mu hm hx 0, aug_eq_mul_mu hm hx 1, aug_eq_mul_mu hm hx 2] at h
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have : (m : ℤ) * (mu x 0 + mu x 1 + mu x 2) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left hm0

lemma ft_mem (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) (j : Fin 3) (π : Option (ZMod m)) :
    ft x j π ∈ sumZero ℤ m := by
  rw [mem_sumZero]
  simp only [ft, Finset.sum_sub_distrib, sum_fib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, aug_eq_mul_mu hm hx j, sub_self]

lemma ft_live (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) (j : Fin 3) {t : ZMod m} (h0 : t ≠ 0)
    (h1 : t ≠ 1) (h2 : t ≠ -1) : ft x j (some t) = 0 := by
  obtain ⟨c, hc⟩ := fib_live_const hx j h0 h1 h2
  exact eq_zero_of_const (ft_mem hm hx j _) (c := c - mu x j) (fun v => by simp [ft, hc])

lemma ft_zero_one (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) :
    ft x 0 (some (-1)) = ft x 1 (some (-1)) := by
  obtain ⟨c, hc⟩ := fib_overlap_zero_one hm hx
  refine sub_eq_zero.mp (eq_zero_of_const (Submodule.sub_mem _ (ft_mem hm hx 0 _)
    (ft_mem hm hx 1 _)) (c := c - mu x 0 + mu x 1) (fun v => ?_))
  simp only [Pi.sub_apply, ft]; linarith [hc v]

lemma ft_one_two (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) :
    ft x 1 (some 1) = ft x 2 (some 1) := by
  obtain ⟨c, hc⟩ := fib_overlap_one_two hm hx
  refine sub_eq_zero.mp (eq_zero_of_const (Submodule.sub_mem _ (ft_mem hm hx 1 _)
    (ft_mem hm hx 2 _)) (c := c - mu x 1 + mu x 2) (fun v => ?_))
  simp only [Pi.sub_apply, ft]; linarith [hc v]

lemma ft_zero_two (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) (y : ZMod m) :
    ft x 2 (some (-1)) y = ft x 0 (some 1) (y - 1) := by
  obtain ⟨c, hc⟩ := fib_overlap_zero_two hm hx
  have hmem : (fun v => ft x 0 (some 1) v - ft x 2 (some (-1)) (v + 1)) ∈ sumZero ℤ m := by
    rw [mem_sumZero, Finset.sum_sub_distrib, W3.sum_comp_add_right (ft x 2 (some (-1))),
      mem_sumZero.mp (ft_mem hm hx _ _), mem_sumZero.mp (ft_mem hm hx _ _), sub_zero]
  have := congrFun (eq_zero_of_const hmem (c := c - mu x 0 + mu x 2)
    (fun v => by simp only [ft]; linarith [hc v])) (y - 1)
  simp only [sub_add_cancel, Pi.zero_apply] at this
  linarith

/-- The pointwise decomposition `m · x(j, k, l) = Σ_π f̃_{j,π}(π(k, l)) + μ_j`, with only the
pencils `0, ∞, 1, −1` surviving. -/
lemma smul_apply_eq (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) (j : Fin 3) (k l : ZMod m) :
    (m : ℤ) * x (j, k, l) = ft x j (some 0) k + ft x j none l + ft x j (some 1) (k + l)
      + ft x j (some (-1)) (k - l) + mu x j := by
  have h := sum_E_pencil (restrict x j) (k, l)
  simp only [← fib_pencil] at h
  have hfib : ∀ π, fib π (restrict x j) (pencil π (k, l)) = ft x j π (pencil π (k, l)) + mu x j :=
    fun π => by simp [ft]
  simp only [hfib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_option, ZMod.card, nsmul_eq_mul] at h
  rw [Fintype.sum_option] at h
  have hsub : ∑ t : ZMod m, ft x j (some t) (pencil (some t) (k, l)) =
      ∑ t ∈ ({0, 1, -1} : Finset (ZMod m)), ft x j (some t) (pencil (some t) (k, l)) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun t _ ht => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    rw [ft_live hm hx j ht.1 ht.2.1 ht.2.2]; rfl
  have h2 := two_ne_zero_zmod (m := m) hm
  have h01 : (0 : ZMod m) ∉ ({1, -1} : Finset (ZMod m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, fun h => one_ne_zero (neg_eq_zero.mp h.symm)⟩
  have h11 : (1 : ZMod m) ∉ ({-1} : Finset (ZMod m)) := by
    simp only [Finset.mem_singleton]
    intro h; apply h2; linear_combination h
  have ha : ∑ q, restrict x j q = m * mu x j := aug_eq_mul_mu hm hx j
  rw [hsub, Finset.sum_insert h01, Finset.sum_insert h11, Finset.sum_singleton, ha] at h
  simp only [pencil, zero_mul, add_zero, one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  change _ = (m : ℤ) * x (j, k, l) + _ at h
  push_cast at h
  linarith

/-- The datum `D` of the proof of (W5.b). -/
def satD (x : A m) : SatData ℤ m :=
  SatData.mk (fun j => ft x j (some 0)) (fun j => ft x j none)
    ![ft x 0 (some (-1)), ft x 1 (some 1), ft x 0 (some 1)] (mu x 0) (-mu x 2)

lemma satD_mem (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) : satD x ∈ SatSrc ℤ m := by
  rw [mem_satSrc]
  intro j
  refine ⟨ft_mem hm hx _ _, ft_mem hm hx _ _, ?_⟩
  fin_cases j
  · exact ft_mem hm hx _ _
  · exact ft_mem hm hx _ _
  · exact ft_mem hm hx _ _

lemma satMap_satD (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) :
    satMap ℤ m (satD x) = (m : ℤ) • x := by
  have hμ := sum_mu hm hx
  ext ⟨j, k, l⟩
  rw [Pi.smul_apply, smul_eq_mul, smul_apply_eq hm hx]
  fin_cases j
  · simp only [Fin.zero_eta, satMap_apply_zero, satD, SatData.a_mk, SatData.b_mk, SatData.w_mk,
      SatData.ε₁_mk]
    simp
    ring
  · simp only [Fin.mk_one, satMap_apply_one, satD, SatData.a_mk, SatData.b_mk, SatData.w_mk,
      SatData.ε₁_mk, SatData.ε₂_mk]
    simp [ft_zero_one hm hx]
    linarith
  · simp only [Fin.reduceFinMk, satMap_apply_two, satD, SatData.a_mk, SatData.b_mk,
      SatData.w_mk, SatData.ε₂_mk]
    simp [ft_one_two hm hx, ft_zero_two hm hx (k - l)]

end W5

open W5

variable {m : ℕ} [Fact m.Prime]

/-- **(W5.b) `mK ⊆ SAT`.** For `m ≥ 5` prime and `x ∈ K`, `m • x ∈ SAT`. -/
theorem smul_mem_SAT (hm : 5 ≤ m) {x : A m} (hx : x ∈ K m) : (m : ℤ) • x ∈ SAT m :=
  ⟨satD x, satD_mem hm hx, satMap_satD hm hx⟩

end Watermark

namespace Watermark

open Module

variable {m : ℕ} [Fact m.Prime]

/-- **(W5.c) Rank.** For `m ≥ 5` prime, `rank K = 9m − 7`. -/
theorem finrank_K (hm : 5 ≤ m) : Module.finrank ℤ (K m) = 9 * m - 7 := by
  have hodd := W4.odd_of_prime_of_five_le hm
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [← finrank_SAT hodd]
  refine le_antisymm ?_ (Submodule.finrank_mono (SAT_le_K m))
  let f : K m →ₗ[ℤ] SAT m :=
    ((m : ℤ) • (K m).subtype).codRestrict (SAT m) (fun x => smul_mem_SAT hm x.2)
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x y h => ?_
  have h' : (m : ℤ) • (x : A m) = (m : ℤ) • (y : A m) := congrArg Subtype.val h
  exact Subtype.ext (smul_right_injective _ hm0 h')

namespace W5

/-- Reduction mod `m` of the kernel, `K → (Line m → ZMod m)`. -/
def redK : K m →ₗ[ℤ] (Line m → ZMod m) where
  toFun x p := ((x : A m) p : ZMod m)
  map_add' x y := by ext p; simp
  map_smul' c x := by ext p; simp

lemma redK_apply (x : K m) (p : Line m) : redK x p = ((x : A m) p : ZMod m) := rfl

/-- The image `K̄` of `K` in `Line m → ZMod m`, an `F_m`-subspace. -/
def Kbar : Submodule (ZMod m) (Line m → ZMod m) where
  carrier := Set.range (redK (m := m))
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    refine ⟨((c.val : ℤ)) • x, ?_⟩
    ext p
    simp [redK_apply]

/-- The image `S̄` of the admissible data over `ZMod m`. -/
def Sbar : Submodule (ZMod m) (Line m → ZMod m) :=
  LinearMap.range ((satMap (ZMod m) m).domRestrict (SatSrc (ZMod m) m))

/-- `K ∩ m A = m K`. -/
lemma exists_smul_of_redK_eq_zero {x : K m} (h : redK x = 0) :
    ∃ z ∈ K m, (x : A m) = (m : ℤ) • z := by
  have hdvd : ∀ p, (m : ℤ) ∣ (x : A m) p := fun p =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun h p)
  refine ⟨fun p => (x : A m) p / m, ?_, ?_⟩
  · have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
    have e : (m : ℤ) • (fun p => (x : A m) p / m) = (x : A m) :=
      funext fun p => Int.mul_ediv_cancel' (hdvd p)
    have hx := mem_K.mp x.2
    rw [← e, mulVec_smul] at hx
    exact mem_K.mpr (smul_right_injective _ hm0 (hx.trans (smul_zero _).symm))
  · exact funext fun p => (Int.mul_ediv_cancel' (hdvd p)).symm

lemma redK_satMap {D : SatData ℤ m} (hD : D ∈ SatSrc ℤ m) :
    redK ⟨satMap ℤ m D, SAT_le_K m ⟨D, hD, rfl⟩⟩ = satMap (ZMod m) m D.red := by
  rw [← satMap_red]; rfl

lemma mem_SAT_iff (hm : 5 ≤ m) (x : K m) : (x : A m) ∈ SAT m ↔ redK x ∈ Sbar (m := m) := by
  constructor
  · rintro ⟨D, hD, hx⟩
    refine ⟨⟨D.red, red_mem_satSrc hD⟩, ?_⟩
    have : x = ⟨satMap ℤ m D, SAT_le_K m ⟨D, hD, rfl⟩⟩ := Subtype.ext hx.symm
    rw [this, redK_satMap hD]; rfl
  · rintro ⟨⟨E, hE⟩, hxE⟩
    obtain ⟨D, hD, rfl⟩ := exists_satSrc_lift hE
    set s : K m := ⟨satMap ℤ m D, SAT_le_K m ⟨D, hD, rfl⟩⟩
    have h0 : redK (x - s) = 0 := by
      rw [map_sub, redK_satMap hD, ← hxE, sub_eq_zero]; rfl
    obtain ⟨z, hz, hxz⟩ := exists_smul_of_redK_eq_zero h0
    have : (x : A m) = satMap ℤ m D + (m : ℤ) • z := by
      rw [← hxz]; simp [s]
    rw [this]
    exact Submodule.add_mem _ ⟨D, hD, rfl⟩ (smul_mem_SAT hm hz)

lemma Sbar_le_Kbar : Sbar (m := m) ≤ Kbar := by
  rintro _ ⟨⟨E, hE⟩, rfl⟩
  obtain ⟨D, hD, rfl⟩ := exists_satSrc_lift hE
  exact ⟨_, redK_satMap hD⟩

lemma finrank_Kbar (hm : 5 ≤ m) : finrank (ZMod m) (Kbar (m := m)) = 9 * m - 7 := by
  let b := Module.finBasis ℤ (K m)
  let v : Fin (finrank ℤ (K m)) → (Line m → ZMod m) := fun i => redK (b i)
  have hspan : Kbar (m := m) = Submodule.span (ZMod m) (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod m)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, rfl⟩
  have hli : LinearIndependent (ZMod m) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    set y : K m := ∑ i, ((g i).val : ℤ) • b i with hy_def
    have hy : redK y = 0 := by
      rw [hy_def, map_sum, ← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod m)]
      simp [v]
    obtain ⟨z, hz, hyz⟩ := exists_smul_of_redK_eq_zero hy
    have hyz' : y = (m : ℤ) • (⟨z, hz⟩ : K m) := Subtype.ext hyz
    have hrep : b.repr y i = ((g i).val : ℤ) := by
      simp [y, map_sum, Finsupp.single_apply]
    have h2 : ((g i).val : ℤ) = m * b.repr ⟨z, hz⟩ i := by
      rw [← hrep, hyz', map_zsmul]; simp
    have h3 := congrArg (fun t : ℤ => (t : ZMod m)) h2
    simpa using h3
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin, finrank_K hm]

lemma finrank_quot (hm : 5 ≤ m) :
    finrank (ZMod m) ((Kbar (m := m)) ⧸ (Sbar (m := m)).comap (Kbar (m := m)).subtype) = 12 := by
  have h := Submodule.finrank_quotient_add_finrank ((Sbar (m := m)).comap (Kbar (m := m)).subtype)
  have hS : finrank (ZMod m) (Sbar (m := m)) = 9 * m - 19 := finrank_range_satMap hm
  rw [(Submodule.comapSubtypeEquivOfLe Sbar_le_Kbar).finrank_eq, finrank_Kbar hm, hS] at h
  omega

end W5

open W5

/-- **(W5.d) Index.** For `m ≥ 5` prime, `[K : SAT] = m ^ 12`. -/
theorem index_SAT (hm : 5 ≤ m) :
    ((SAT m).comap (K m).subtype).toAddSubgroup.index = m ^ 12 := by
  let f : K m →+ Kbar (m := m) :=
    { toFun := fun x => ⟨redK x, x, rfl⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have hf : Function.Surjective f := by
    rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩
  have hcomap : ((SAT m).comap (K m).subtype).toAddSubgroup =
      ((Sbar (m := m)).comap (Kbar (m := m)).subtype).toAddSubgroup.comap f := by
    ext x
    exact mem_SAT_iff hm x
  rw [hcomap, AddSubgroup.index_comap_of_surjective _ hf]
  change Nat.card ((Kbar (m := m)) ⧸ (Sbar (m := m)).comap (Kbar (m := m)).subtype) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod m), Nat.card_zmod]
  rw [finrank_quot hm]

end Watermark
