module

public import RequestProject.DoubleLadder.DL2

/-!
# The Double Ladder Theorem, piece DL3: the assembly

We compute the discriminant group `D m = V* ⧸ V` of the lattice `V m` of lines on the Fermat
surface of degree `m`.

* `DoubleLadder.equiv_of_card` (DL3.group): a finite abelian group killed by `p²` is determined
  by `|H|` and `|H ⧸ pH|`.
* `DoubleLadder.double_ladder_theorem` (DL3.main): for `m` prime, `7 ≤ m`,
  `D m ≃+ (ℤ/m)^(3m² − 24m + 59) × (ℤ/m²)^(3m − 16)`.
* `DoubleLadder.double_ladder_five` (DL3.five): `D 5 ≃+ (ℤ/5)^10 × ℤ/25`.
-/

@[expose] public section

open Matrix Watermark Pointwise

namespace DoubleLadder

/-- The discriminant group `V* ⧸ V` of the lattice `V m`. -/
abbrev D (m : ℕ) [NeZero m] : Type := Module.Dual ℤ (V m) ⧸ LinearMap.range (formV m)

namespace DL3

/-! ### (DL3.group) Finite abelian groups of exponent dividing `p²` -/

theorem ker_castHom_eq (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    (ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p)).toAddMonoidHom.ker =
      (p • ⊤ : AddSubgroup (ZMod (p ^ e))) := by
  have hd : p ∣ p ^ e := dvd_pow_self p (by omega)
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ext x
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ZMod (p ^ e)) = x := ⟨x.val, ZMod.natCast_zmod_val x⟩
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_smul_pointwise_iff_exists]
  have hf : (ZMod.castHom hd (ZMod p)).toAddMonoidHom n = (n : ZMod p) :=
    map_natCast (ZMod.castHom hd (ZMod p)) n
  rw [hf]
  constructor
  · intro hx
    rw [ZMod.natCast_eq_zero_iff] at hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨(k : ZMod (p ^ e)), trivial, ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← hk]
  · rintro ⟨y, -, hy⟩
    rw [← hf, ← hy, map_nsmul]
    simp

theorem exists_equiv_pi {H : Type*} [AddCommGroup H] [Finite H] (p : ℕ) [hp : Fact p.Prime]
    (hH : ∀ x : H, p ^ 2 • x = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ), (∀ i, e i = 1 ∨ e i = 2) ∧
      Nonempty (H ≃+ ((i : ι) → ZMod (p ^ e i))) := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' H
  let g : H ≃+ ((i : ι) → ZMod (n i)) :=
    f.trans (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (n i))).toAddEquiv
  have key : ∀ i, ∃ k, (k = 1 ∨ k = 2) ∧ n i = p ^ k := by
    intro i
    have h1 := hH (g.symm (Pi.single i 1))
    have h2 : (p ^ 2 • (Pi.single i 1 : (i : ι) → ZMod (n i))) i = 0 := by
      rw [← map_nsmul g.symm, g.symm.map_eq_zero_iff] at h1
      rw [h1]; rfl
    rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one,
      ZMod.natCast_eq_zero_iff] at h2
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 h2
    refine ⟨k, ?_, hk'⟩
    have := hn i
    rcases k with _ | _ | _ | k
    · simp at hk'; omega
    · simp
    · simp
    · omega
  choose e he hne using key
  exact ⟨ι, hι, e, he, ⟨g.trans (AddEquiv.piCongrRight fun i =>
    (ZMod.ringEquivCongr (hne i)).toAddEquiv)⟩⟩

theorem pi_split (p : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (he : ∀ i, e i = 1 ∨ e i = 2) :
    Nonempty (((i : ι) → ZMod (p ^ e i)) ≃+ ((Fin (Fintype.card {i // e i = 1}) → ZMod p) ×
      (Fin (Fintype.card {i // ¬ e i = 1}) → ZMod (p ^ 2)))) := by
  let s : ((i : ι) → ZMod (p ^ e i)) ≃+ (((i : {i // e i = 1}) → ZMod (p ^ e i)) ×
      ((i : {i // ¬ e i = 1}) → ZMod (p ^ e i))) :=
    { Equiv.piEquivPiSubtypeProd (fun i => e i = 1) (fun i => ZMod (p ^ e i)) with
      map_add' := fun _ _ => rfl }
  have h1 : ∀ i : {i // e i = 1}, p ^ e i = p := fun i => by rw [i.2, pow_one]
  have h2 : ∀ i : {i // ¬ e i = 1}, p ^ e i = p ^ 2 := fun i => by
    rw [(he i).resolve_left i.2]
  exact ⟨s.trans (AddEquiv.prodCongr
    ((AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (h1 i)).toAddEquiv).trans
      (LinearEquiv.funCongrLeft ℤ (ZMod p) (Fintype.equivFin _).symm).toAddEquiv)
    ((AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (h2 i)).toAddEquiv).trans
      (LinearEquiv.funCongrLeft ℤ (ZMod (p ^ 2)) (Fintype.equivFin _).symm).toAddEquiv))⟩

theorem card_pi (p : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (he : ∀ i, e i = 1 ∨ e i = 2) :
    Nat.card ((i : ι) → ZMod (p ^ e i)) =
      p ^ (Fintype.card {i // e i = 1} + 2 * Fintype.card {i // ¬ e i = 1}) := by
  rw [Nat.card_pi]
  simp only [Nat.card_zmod]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => e i = 1)]
  rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2),
    Finset.sum_congr rfl (fun i hi => (he i).resolve_left (Finset.mem_filter.1 hi).2)]
  simp [Fintype.card_subtype, mul_comm]

theorem index_pi (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (e : ι → ℕ)
    (he : ∀ i, e i = 1 ∨ e i = 2) :
    (p • ⊤ : AddSubgroup ((i : ι) → ZMod (p ^ e i))).index = p ^ Fintype.card ι := by
  have : (p • ⊤ : AddSubgroup ((i : ι) → ZMod (p ^ e i))) =
      AddSubgroup.pi Set.univ (fun i => p • ⊤) := by
    ext x
    simp only [AddSubgroup.mem_smul_pointwise_iff_exists, AddSubgroup.mem_top, true_and,
      AddSubgroup.mem_pi, Set.mem_univ, forall_const]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, rfl⟩
    · intro h
      choose y hy using h
      exact ⟨y, funext hy⟩
  have he1 : ∀ i, 1 ≤ e i := fun i => by rcases he i with h | h <;> omega
  let F : ((i : ι) → ZMod (p ^ e i)) →+ (ι → ZMod p) :=
    { toFun := fun x i => ZMod.castHom (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp (he1 i))) (ZMod p) (x i)
      map_zero' := by ext i; simp
      map_add' := fun x y => funext fun i => map_add _ _ _ }
  have hker : F.ker = AddSubgroup.pi Set.univ (fun i => p • ⊤) := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_pi, Set.mem_univ, forall_const]
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    rw [← ker_castHom_eq p (e i) (he1 i)]
    rfl
  have hsurj : Function.Surjective F := by
    intro y
    choose x hx using fun i =>
      ZMod.ringHom_surjective (ZMod.castHom (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp (he1 i)))
        (ZMod p)) (y i)
    exact ⟨x, funext hx⟩
  rw [this, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj,
    AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

theorem index_smul_top_equiv {H H' : Type*} [AddCommGroup H] [AddCommGroup H'] (f : H ≃+ H')
    (p : ℕ) : (p • ⊤ : AddSubgroup H).index = (p • ⊤ : AddSubgroup H').index := by
  rw [← AddSubgroup.index_comap_of_surjective (p • ⊤ : AddSubgroup H')
    (f := f.toAddMonoidHom) f.surjective]
  congr 1
  ext x
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_smul_pointwise_iff_exists,
    AddSubgroup.mem_top, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨f y, by simp⟩
  · rintro ⟨y, hy⟩
    exact ⟨f.symm y, by apply f.injective; simpa using hy⟩

end DL3

open DL3

/-- **(DL3.group)** A finite abelian group `H` with `p² H = 0`, `|H| = p ^ N` and
`|H ⧸ pH| = p ^ c` satisfies `c ≤ N ≤ 2c` and is isomorphic to
`(ℤ/p)^(2c − N) × (ℤ/p²)^(N − c)`. -/
theorem equiv_of_card {H : Type*} [AddCommGroup H] [Finite H] (p : ℕ) [hp : Fact p.Prime]
    (N c : ℕ) (hH : ∀ x : H, p ^ 2 • x = 0) (hN : Nat.card H = p ^ N)
    (hc : Nat.card (H ⧸ (p • ⊤ : AddSubgroup H)) = p ^ c) :
    c ≤ N ∧ N ≤ 2 * c ∧
      Nonempty (H ≃+ ((Fin (2 * c - N) → ZMod p) × (Fin (N - c) → ZMod (p ^ 2)))) := by
  classical
  obtain ⟨ι, hι, e, he, ⟨f⟩⟩ := exists_equiv_pi p hH
  obtain ⟨g⟩ := pi_split p e he
  have hp1 : 1 < p := hp.out.one_lt
  have h1 : Fintype.card {i // e i = 1} + 2 * Fintype.card {i // ¬ e i = 1} = N := by
    apply Nat.pow_right_injective hp1
    simp only
    rw [← card_pi p e he, ← hN]
    exact (Nat.card_congr f.toEquiv).symm
  have h2 : Fintype.card {i // e i = 1} + Fintype.card {i // ¬ e i = 1} = c := by
    apply Nat.pow_right_injective hp1
    simp only
    rw [Fintype.card_subtype_compl, ← hc]
    have : Fintype.card {i // e i = 1} ≤ Fintype.card ι := Fintype.card_subtype_le _
    rw [Nat.add_sub_cancel' this, ← index_pi p e he, ← index_smul_top_equiv f p]
    rfl
  refine ⟨by omega, by omega, ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, Fintype.card {i // e i = 1} = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, Fintype.card {i // ¬ e i = 1} = b := ⟨_, rfl⟩
  rw [ha, hb] at g
  have ha' : 2 * c - N = a := by omega
  have hb' : N - c = b := by omega
  rw [ha', hb']
  exact ⟨f.trans g⟩

namespace DL3

/-! ### Integer matrices: order of the cokernel and of its reduction mod `m` -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mulVecLin_injective (M : Matrix ι ι ℤ) (h : M.det ≠ 0) :
    Function.Injective M.mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have : M.adjugate *ᵥ (M *ᵥ v) = M.det • v := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [show M *ᵥ v = 0 from hv, mulVec_zero] at this
  exact (smul_eq_zero.mp this.symm).resolve_left h

/-- The cokernel of a nonsingular integer matrix has order `|det M|`. -/
theorem card_coker (M : Matrix ι ι ℤ) (h : M.det ≠ 0) :
    Nat.card ((ι → ℤ) ⧸ LinearMap.range M.mulVecLin) = M.det.natAbs := by
  rw [← Submodule.natAbs_det_equiv (LinearMap.range M.mulVecLin)
    (LinearEquiv.ofInjective M.mulVecLin (mulVecLin_injective M h))]
  congr 1
  rw [← LinearMap.det_toLin' M]
  congr 1

/-- If `Q` is the cokernel of `M`, then `Q ⧸ mQ` has order `m ^ (n − rank (M mod m))`. -/
theorem card_coker_quot_smul (M : Matrix ι ι ℤ) (m : ℕ) [Fact m.Prime] :
    Nat.card (((ι → ℤ) ⧸ LinearMap.range M.mulVecLin) ⧸
      (m • ⊤ : AddSubgroup ((ι → ℤ) ⧸ LinearMap.range M.mulVecLin))) =
      m ^ (Fintype.card ι - (M.map (Int.castRingHom (ZMod m))).rank) := by
  set Mb := M.map (Int.castRingHom (ZMod m))
  set R := LinearMap.range M.mulVecLin
  set Rb := LinearMap.range Mb.mulVecLin
  let cst : (ι → ℤ) →+ (ι → ZMod m) := (Int.castAddHom (ZMod m)).compLeft ι
  let ψ : (ι → ℤ) →ₗ[ℤ] ((ι → ZMod m) ⧸ Rb) := (Rb.mkQ.toAddMonoidHom.comp cst).toIntLinearMap
  have hcst : ∀ v : ι → ℤ, cst (M *ᵥ v) = Mb *ᵥ cst v := fun v => by
    ext i
    exact RingHom.map_mulVec (Int.castRingHom (ZMod m)) M v i
  have hle : R ≤ LinearMap.ker ψ := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    change Rb.mkQ (cst (M *ᵥ v)) = 0
    rw [hcst, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨_, rfl⟩
  let φ := R.liftQ ψ hle
  have hker : φ.toAddMonoidHom.ker = (m • ⊤ : AddSubgroup ((ι → ℤ) ⧸ R)) := by
    ext x
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_smul_pointwise_iff_exists]
    change Submodule.Quotient.mk (cst f) = (0 : (ι → ZMod m) ⧸ Rb) ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨cb, hcb⟩
      let c : ι → ℤ := fun i => ((cb i).val : ℤ)
      have hc : cst c = cb := by ext i; simp [c, cst]
      change Mb *ᵥ cb = cst f at hcb
      have hdiv : ∀ i, (m : ℤ) ∣ (f - M *ᵥ c) i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have := congrFun (hcst c) i
        rw [hc] at this
        simp only [Pi.sub_apply, Int.cast_sub]
        have h3 : ((f i : ℤ) : ZMod m) = cst f i := rfl
        have h4 : (((M *ᵥ c) i : ℤ) : ZMod m) = cst (M *ᵥ c) i := rfl
        rw [h3, h4, this, ← hcb, sub_self]
      choose g hg using hdiv
      refine ⟨Submodule.Quotient.mk g, trivial, ?_⟩
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
      have : f - m • g = M *ᵥ c := by
        ext i
        have := hg i
        simp only [Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at this ⊢
        linarith
      rw [this]
      exact ⟨c, rfl⟩
    · rintro ⟨y, -, hy⟩
      have : φ (Submodule.Quotient.mk f) = 0 := by
        rw [← hy, map_nsmul]
        obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        change m • Submodule.Quotient.mk (cst g) = (0 : (ι → ZMod m) ⧸ Rb)
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        refine ⟨0, ?_⟩
        ext i
        simp
      change Submodule.Quotient.mk (cst f) = (0 : (ι → ZMod m) ⧸ Rb) at this
      rwa [Submodule.Quotient.mk_eq_zero] at this
  have hsurj : Function.Surjective φ := by
    intro t
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨Submodule.Quotient.mk (fun i => ((u i).val : ℤ)), ?_⟩
    change Submodule.Quotient.mk (cst _) = Submodule.Quotient.mk u
    congr 1
    funext i
    simp [cst]
  change (m • ⊤ : AddSubgroup ((ι → ℤ) ⧸ R)).index = _
  rw [← hker, AddSubgroup.index_ker,
    (AddMonoidHom.range_eq_top (f := φ.toAddMonoidHom)).mpr hsurj, AddSubgroup.card_top,
    Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod m), ZMod.card,
    Submodule.finrank_quotient, Module.finrank_fintype_fun_eq_card]
  rfl

end Matrix

/-! ### The discriminant group as a matrix cokernel -/

/-- **Step 1.** For a basis `b` of `V m`, `D m` is the cokernel of the Gram matrix of `formV m`
in `b`. -/
noncomputable def discrEquiv {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (V m)) :
    D m ≃ₗ[ℤ] (ι → ℤ) ⧸ LinearMap.range (LinearMap.BilinForm.toMatrix b (formV m)).mulVecLin :=
  Submodule.Quotient.equiv _ _ (b.constr (M' := ℤ) ℤ).symm (by
    set M := LinearMap.BilinForm.toMatrix b (formV m)
    have h : (b.constr (M' := ℤ) ℤ).symm.toLinearMap ∘ₗ formV m =
        M.mulVecLin ∘ₗ (b.equivFun : V m →ₗ[ℤ] (ι → ℤ)) := by
      refine b.ext fun j => ?_
      ext i
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Module.Basis.constr_symm_apply, Matrix.mulVecLin_apply,
        M]
      rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single,
        mulVec_single_one, col_apply, LinearMap.BilinForm.toMatrix_apply]
      exact formV_isSymm.eq _ _
    rw [← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top]
    exact LinearEquiv.range _)

/-- **Step 3.** `m² • D m = 0`. -/
theorem sq_smul_discr_eq_zero (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) (x : D m) :
    m ^ 2 • x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, hv⟩ := exists_formV_eq_smul m hm f
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    show (m ^ 2 : ℕ) • f = ((m : ℤ) ^ 2) • f by rw [← natCast_zsmul]; push_cast; rfl, hv]
  exact ⟨v, rfl⟩

/-- The assembly, given the rank of the Gram matrix modulo `m` in every basis. -/
theorem discr_equiv_of_rank (m : ℕ) [Fact m.Prime] (hm : 5 ≤ m) (k : ℕ)
    (hk : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ (V m)),
      ((LinearMap.BilinForm.toMatrix b (formV m)).map (Int.castRingHom (ZMod m))).rank = k) :
    Nonempty (D m ≃+
      ((Fin (2 * (3 * (m - 1) * (m - 2) + 1 - k) - 3 * (m - 3) ^ 2) → ZMod m) ×
        (Fin (3 * (m - 3) ^ 2 - (3 * (m - 1) * (m - 2) + 1 - k)) → ZMod (m ^ 2)))) := by
  classical
  obtain ⟨hfree, hrank, hdet⟩ := watermark_theorem hm
  let b := Module.Free.chooseBasis ℤ (V m)
  set M := LinearMap.BilinForm.toMatrix b (formV m)
  let e := (discrEquiv b).toAddEquiv
  have hmpos : 0 < m := (Fact.out : m.Prime).pos
  have hdetM : M.det = (m : ℤ) ^ (3 * (m - 3) ^ 2) := hdet b
  have hcard : Nat.card ((Module.Free.ChooseBasisIndex ℤ (V m) → ℤ) ⧸
      LinearMap.range M.mulVecLin) = m ^ (3 * (m - 3) ^ 2) := by
    rw [card_coker M (by rw [hdetM]; positivity), hdetM, Int.natAbs_pow, Int.natAbs_natCast]
  haveI : Finite ((Module.Free.ChooseBasisIndex ℤ (V m) → ℤ) ⧸
      LinearMap.range M.mulVecLin) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hkill : ∀ x : (Module.Free.ChooseBasisIndex ℤ (V m) → ℤ) ⧸
      LinearMap.range M.mulVecLin, m ^ 2 • x = 0 := fun x => by
    rw [← e.apply_symm_apply x, ← map_nsmul, sq_smul_discr_eq_zero m hm, map_zero]
  have hc := card_coker_quot_smul M m
  rw [← Module.finrank_eq_card_chooseBasisIndex, hrank, hk b] at hc
  obtain ⟨-, -, ⟨g⟩⟩ := equiv_of_card m _ _ hkill hcard hc
  exact ⟨e.trans g⟩

theorem rank_toMatrix_map_five {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (V 5)) :
    ((LinearMap.BilinForm.toMatrix b (formV 5)).map (Int.castRingHom (ZMod 5))).rank = 26 := by
  obtain ⟨Q, hQ⟩ := DL1.exists_projMat_mul_eq_one b
  have hG := DL1.gram_eq_projMat b
  set P := DL1.projMat b
  set M := LinearMap.BilinForm.toMatrix b (formV 5)
  have hM : M = Qᵀ * gram 5 * Q := by
    rw [hG, show Qᵀ * (Pᵀ * M * P) * Q = (P * Q)ᵀ * M * (P * Q) by
      simp only [transpose_mul, Matrix.mul_assoc], hQ]
    simp
  set f := Int.castRingHom (ZMod 5)
  have hG' : (gram 5).map f = (P.map f)ᵀ * M.map f * P.map f := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, transpose_map]
  have hM' : M.map f = (Q.map f)ᵀ * (gram 5).map f * Q.map f := by
    rw [hM, Matrix.map_mul, Matrix.map_mul, transpose_map]
  rw [← rank_gram_map_five]
  refine le_antisymm ?_ ?_
  · rw [hM']
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · rw [hG']
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

end DL3

open DL3

/-- **(DL3.main) The Double Ladder Theorem.** For every prime `m ≥ 7`, the discriminant group
`V* ⧸ V` of the lattice of lines on the Fermat surface of degree `m` is
`(ℤ/m)^(3m² − 24m + 59) × (ℤ/m²)^(3m − 16)`. -/
theorem double_ladder_theorem (m : ℕ) [Fact m.Prime] (hm : 7 ≤ m) :
    Nonempty (D m ≃+ ((Fin (3 * m ^ 2 + 59 - 24 * m) → ZMod m) ×
      (Fin (3 * m - 16) → ZMod (m ^ 2)))) := by
  have h := discr_equiv_of_rank m (by omega) (12 * (m - 3)) (fun b => rank_toMatrix_map m hm b)
  have e1 : 2 * (3 * (m - 1) * (m - 2) + 1 - 12 * (m - 3)) - 3 * (m - 3) ^ 2 =
      3 * m ^ 2 + 59 - 24 * m ∧
      3 * (m - 3) ^ 2 - (3 * (m - 1) * (m - 2) + 1 - 12 * (m - 3)) = 3 * m - 16 := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 7 := ⟨m - 7, by omega⟩
    have h1 : n + 7 - 1 = n + 6 := by omega
    have h2 : n + 7 - 2 = n + 5 := by omega
    have h3 : n + 7 - 3 = n + 4 := by omega
    rw [h1, h2, h3]
    ring_nf
    constructor <;> omega
  rwa [e1.1, e1.2] at h

/-- **(DL3.five)** For `m = 5` the discriminant group is `(ℤ/5)^10 × ℤ/25`. -/
theorem double_ladder_five : Nonempty (D 5 ≃+ ((Fin 10 → ZMod 5) × ZMod 25)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g⟩ := discr_equiv_of_rank 5 le_rfl 26 (fun b => rank_toMatrix_map_five b)
  have e1 : 2 * (3 * (5 - 1) * (5 - 2) + 1 - 26) - 3 * (5 - 3) ^ 2 = 10 := by norm_num
  have e2 : 3 * (5 - 3) ^ 2 - (3 * (5 - 1) * (5 - 2) + 1 - 26) = 1 := by norm_num
  rw [e1, e2] at g
  exact ⟨g.trans (AddEquiv.prodCongr (AddEquiv.refl _)
    ((AddEquiv.piUnique fun _ : Fin 1 => ZMod (5 ^ 2)).trans
      (ZMod.ringEquivCongr (by norm_num)).toAddEquiv))⟩

end DoubleLadder
