/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Sylow reduction of a finite torsion module

Let `G` be a profinite group, `ℓ` a prime and `M` a finite `ℓ`-primary discrete `G`-module. The
kernel of the action of `G` on `M` is open and normal; the inverse image `K` of an `ℓ`-Sylow
subgroup of the finite quotient is an open subgroup of index prime to `ℓ` acting on `M` through
an `ℓ`-group. Such an action has a nonzero fixed vector killed by `ℓ` on every nonzero
`ℓ`-primary finite module, by the congruence `#Mᴾ ≡ #M (mod ℓ)`; hence `M|_K` has a filtration
with trivial `𝔽_ℓ` quotients.

## Main statements

- `exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup`: the fixed vector.
- `DiscreteModule.exists_isOpen_not_dvd_index_pow_mem`: the open subgroup `K`.
- `exists_filtration_of_isPGroup`: the filtration for an action through an `ℓ`-group.
- `DiscreteModule.exists_isOpen_not_dvd_index_filtration`: the filtration.
-/

@[expose] public section

universe w u

open CategoryTheory

section FixedPoints

variable {K : Type*} [Group K] {A : Type*} [AddCommGroup A] [DistribMulAction K A]

/-- The action of `K ⧸ N` on `A` when `N` acts trivially. -/
@[reducible]
def mulActionQuotientOfForall (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a) :
    MulAction (K ⧸ N) A where
  smul q a := Quotient.liftOn' q (· • a) fun x y h ↦ by
    rw [QuotientGroup.leftRel_apply] at h
    conv_rhs => rw [show y = x * (x⁻¹ * y) by group, mul_smul, hN _ h a]
  one_smul a := one_smul K a
  mul_smul q r a := Quotient.inductionOn₂' q r fun x y ↦ mul_smul x y a

lemma natCard_dvd_of_forall_pow_nsmul (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A] [Nontrivial A]
    (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0) : ℓ ∣ Nat.card A := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨j, hj⟩ := hA a
  obtain ⟨i, hi, hia⟩ := (Nat.dvd_prime_pow hℓ.out).1 (addOrderOf_dvd_of_nsmul_eq_zero hj)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact ha (AddMonoid.addOrderOf_eq_one_iff.1 (by simpa using hia))
  exact (dvd_pow_self ℓ hi0).trans (hia ▸ addOrderOf_dvd_natCard a)

/-- **Fixed vectors of an `ℓ`-group.** Let `K` act on a finite nonzero `ℓ`-primary abelian group
`A` through an `ℓ`-group: a normal subgroup `N` acts trivially and every element of `K` has an
`ℓ`-power in `N`. Then `A` has a nonzero `K`-fixed element killed by `ℓ`: the nontrivial orbits
have cardinality divisible by `ℓ`, so `#Aᴷ ≡ #A ≡ 0 (mod ℓ)`. -/
theorem exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A]
    [Nontrivial A] (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a)
    (hK : ∀ k : K, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0) :
    ∃ a : A, a ≠ 0 ∧ ℓ • a = 0 ∧ ∀ k : K, k • a = a := by
  let := mulActionQuotientOfForall N hN
  have hP : IsPGroup ℓ (K ⧸ N) := fun q ↦ Quotient.inductionOn' q fun k ↦ by
    obtain ⟨j, hj⟩ := hK k
    exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩
  have hcong := hP.card_modEq_card_fixedPoints A
  let F : AddSubgroup A :=
    { carrier := {a | ∀ k : K, k • a = a}
      zero_mem' := fun k ↦ smul_zero k
      add_mem' := fun ha hb k ↦ by rw [smul_add, ha k, hb k]
      neg_mem' := fun ha k ↦ by rw [smul_neg, ha k] }
  have hF : Nat.card F = Nat.card (MulAction.fixedPoints (K ⧸ N) A) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ ?_)
    exact ⟨fun h q ↦ Quotient.inductionOn' q fun k ↦ h k, fun h k ↦ h (QuotientGroup.mk k)⟩
  have hdvd : ℓ ∣ Nat.card F := by
    rw [hF, ← Nat.modEq_zero_iff_dvd]
    exact hcong.symm.trans ((Nat.modEq_zero_iff_dvd).2 (natCard_dvd_of_forall_pow_nsmul ℓ hA))
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ hdvd
  refine ⟨x.1, fun h ↦ ?_, ?_, x.2⟩
  · have : x = 0 := Subtype.ext h
    rw [this, addOrderOf_zero] at hx
    exact hℓ.out.one_lt.ne hx
  · have := addOrderOf_nsmul_eq_zero x
    rw [hx] at this
    exact congrArg Subtype.val this


/-- The action of `K` on the quotient of `A` by a `K`-stable subgroup. -/
@[reducible]
def distribMulActionQuotient (B : AddSubgroup A) (hB : ∀ k : K, ∀ b ∈ B, k • b ∈ B) :
    DistribMulAction K (A ⧸ B) where
  smul k := QuotientAddGroup.map B B (DistribSMul.toAddMonoidHom A k) fun b hb ↦ hB k b hb
  one_smul q := QuotientAddGroup.induction_on q fun a ↦ by
    change QuotientAddGroup.mk ((1 : K) • a) = _
    rw [one_smul]
  mul_smul k k' q := QuotientAddGroup.induction_on q fun a ↦ by
    change QuotientAddGroup.mk ((k * k') • a) = QuotientAddGroup.mk (k • k' • a)
    rw [mul_smul]
  smul_zero k := map_zero _
  smul_add k := map_add _

/-- **Filtration of a module over an `ℓ`-group.** Let `K` act on a finite `ℓ`-primary abelian
group `A` through an `ℓ`-group, and let `B` be a `K`-stable subgroup. Then there is a finite
increasing chain of `K`-stable subgroups from `B` to `A` whose successive quotients are killed
by `ℓ` and have trivial `K`-action. -/
theorem exists_filtration_of_isPGroup_of_le (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A]
    (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a)
    (hK : ∀ k : K, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0)
    (B : AddSubgroup A) (hB : ∀ k : K, ∀ b ∈ B, k • b ∈ B) :
    ∃ (n : ℕ) (F : ℕ → AddSubgroup A), F 0 = B ∧ F n = ⊤ ∧ Monotone F ∧
      (∀ i, ∀ k : K, ∀ x ∈ F i, k • x ∈ F i) ∧ (∀ i, ∀ x ∈ F (i + 1), ℓ • x ∈ F i) ∧
      (∀ i, ∀ k : K, ∀ x ∈ F (i + 1), k • x - x ∈ F i) := by
  induction B using WellFoundedGT.induction with
  | _ B ih =>
  by_cases htop : B = ⊤
  · refine ⟨0, fun _ ↦ B, rfl, htop, monotone_const, fun _ ↦ hB, fun _ x _ ↦ ?_,
      fun _ k x _ ↦ ?_⟩
    · rw [htop]
      exact AddSubgroup.mem_top _
    · rw [htop]
      exact AddSubgroup.mem_top _
  let := distribMulActionQuotient B hB
  have : Nontrivial (A ⧸ B) := by
    obtain ⟨a, ha⟩ : ∃ a, a ∉ B := by
      by_contra! h
      exact htop (eq_top_iff.2 fun a _ ↦ h a)
    exact ⟨⟨QuotientAddGroup.mk a, 0, fun h ↦ ha ((QuotientAddGroup.eq_zero_iff a).1 h)⟩⟩
  have : Finite (A ⧸ B) := Finite.of_surjective _ (QuotientAddGroup.mk_surjective (s := B))
  obtain ⟨q, hq0, hqℓ, hqK⟩ := exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup (A := A ⧸ B) ℓ N
    (fun n hn q ↦ QuotientAddGroup.induction_on q fun a ↦ congrArg QuotientAddGroup.mk
      (hN n hn a))
    hK (fun q ↦ QuotientAddGroup.induction_on q fun a ↦ by
      obtain ⟨j, hj⟩ := hA a
      exact ⟨j, by rw [← QuotientAddGroup.mk_nsmul, hj, QuotientAddGroup.mk_zero]⟩)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hxB : x ∉ B := fun h ↦ hq0 ((QuotientAddGroup.eq_zero_iff x).2 h)
  have hxℓ : ℓ • x ∈ B := (QuotientAddGroup.eq_zero_iff _).1 (by
    rw [QuotientAddGroup.mk_nsmul]; exact hqℓ)
  have hxK (k : K) : k • x - x ∈ B := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hqK k
  let B' := B ⊔ AddSubgroup.zmultiples x
  have hmem {y : A} (hy : y ∈ B') : ∃ b ∈ B, ∃ m : ℤ, b + m • x = y := by
    obtain ⟨b, hb, z, ⟨m, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.1 hy
    exact ⟨b, hb, m, rfl⟩
  have hB' : ∀ k : K, ∀ y ∈ B', k • y ∈ B' := by
    intro k y hy
    obtain ⟨b, hb, m, rfl⟩ := hmem hy
    rw [smul_add, smul_comm, show k • x = (k • x - x) + x by abel, smul_add, ← add_assoc]
    refine add_mem (AddSubgroup.mem_sup_left (add_mem (hB k b hb) (zsmul_mem (hxK k) m)))
      (AddSubgroup.mem_sup_right (zsmul_mem (AddSubgroup.mem_zmultiples x) m))
  have hlt : B < B' := lt_of_le_of_ne le_sup_left fun h ↦
    hxB (h ▸ AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x))
  obtain ⟨n, F, hF0, hFn, hFm, hFK, hFℓ, hFt⟩ := ih B' hlt hB'
  refine ⟨n + 1, fun i ↦ Nat.casesOn i B F, rfl, hFn, monotone_nat_of_le_succ fun i ↦ ?_,
    fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · cases i with
    | zero =>
      change B ≤ F 0
      exact hF0 ▸ hlt.le
    | succ i => exact hFm i.le_succ
  · cases i with
    | zero => exact hB
    | succ i => exact hFK i
  · cases i with
    | zero =>
      intro y hy
      obtain ⟨b, hb, m, rfl⟩ := hmem (show y ∈ B' from hF0 ▸ hy)
      change _ ∈ B
      rw [smul_add, smul_comm]
      exact add_mem (nsmul_mem hb ℓ) (zsmul_mem hxℓ m)
    | succ i => exact hFℓ i
  · cases i with
    | zero =>
      intro k y hy
      obtain ⟨b, hb, m, rfl⟩ := hmem (show y ∈ B' from hF0 ▸ hy)
      change _ ∈ B
      rw [smul_add, smul_comm, show k • b + m • k • x - (b + m • x) =
        (k • b - b) + m • (k • x - x) by rw [zsmul_sub]; abel]
      exact add_mem (sub_mem (hB k b hb) hb) (zsmul_mem (hxK k) m)
    | succ i => exact hFt i

/-- The filtration of `exists_filtration_of_isPGroup_of_le` starting from `0`. -/
theorem exists_filtration_of_isPGroup (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [Finite A]
    (N : Subgroup K) [N.Normal] (hN : ∀ n ∈ N, ∀ a : A, n • a = a)
    (hK : ∀ k : K, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (hA : ∀ a : A, ∃ j : ℕ, ℓ ^ j • a = 0) :
    ∃ (n : ℕ) (F : ℕ → AddSubgroup A), F 0 = ⊥ ∧ F n = ⊤ ∧ Monotone F ∧
      (∀ i, ∀ k : K, ∀ x ∈ F i, k • x ∈ F i) ∧ (∀ i, ∀ x ∈ F (i + 1), ℓ • x ∈ F i) ∧
      (∀ i, ∀ k : K, ∀ x ∈ F (i + 1), k • x - x ∈ F i) :=
  exists_filtration_of_isPGroup_of_le ℓ N hN hK hA ⊥ fun k b hb ↦ by
    rw [(AddSubgroup.mem_bot).1 hb, smul_zero]
    exact zero_mem _


end FixedPoints

/-- The action of `G` on the underlying group of an `Action`, as a `DistribMulAction`. -/
@[reducible]
def Action.distribMulAction {G : Type*} [Group G] (M : Action AddCommGrpCat.{w} G) :
    DistribMulAction G M.V where
  smul g x := (M.ρ g).asHom.hom x
  one_smul := Action.ρ_one_apply M
  mul_smul a b x := Action.ρ_mul_apply M a b x
  smul_zero _ := map_zero _
  smul_add _ := map_add _

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The kernel of the action of `G` on a discrete `G`-module. -/
def actionKernel (M : DiscreteModule.{w} G) : Subgroup G :=
  ⨅ x : M.obj.V, M.obj.stabilizer x

variable (M : DiscreteModule.{w} G)

omit [IsTopologicalGroup G] in
lemma mem_actionKernel {g : G} : g ∈ actionKernel M ↔ ∀ x, (M.obj.ρ g).asHom.hom x = x := by
  simp [actionKernel, Subgroup.mem_iInf]

instance : (actionKernel M).Normal where
  conj_mem n hn g := by
    rw [mem_actionKernel] at hn ⊢
    intro x
    simp [hn]

omit [IsTopologicalGroup G] in
lemma isOpen_actionKernel [Finite M.obj.V] : IsOpen (actionKernel M : Set G) := by
  rw [actionKernel, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun x ↦ M.isOpen_stabilizer x

/-- Let `M` be a finite discrete module over a compact group `G` and `ℓ` a prime. There is an
open subgroup `K` of index prime to `ℓ`, containing the kernel `N` of the action, such that
every element of `K` has an `ℓ`-power in `N`: the inverse image of an `ℓ`-Sylow subgroup of the
finite group `G ⧸ N`. -/
theorem exists_isOpen_not_dvd_index_pow_mem [CompactSpace G] (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite M.obj.V] :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ¬ ℓ ∣ K.index ∧ actionKernel M ≤ K ∧
      ∀ k ∈ K, ∃ j : ℕ, k ^ ℓ ^ j ∈ actionKernel M := by
  set N := actionKernel M
  have hN := isOpen_actionKernel M
  have : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (G ⧸ N)) := inferInstance
  refine ⟨(P : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N), ?_, ?_, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (fun g hg ↦ ?_) hN
    change QuotientGroup.mk' N g ∈ P
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact one_mem _
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact P.not_dvd_index
  · intro g hg
    change QuotientGroup.mk' N g ∈ P
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact one_mem _
  · intro k hk
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨_, hk⟩
    refine ⟨j, (QuotientGroup.eq_one_iff _).1 ?_⟩
    simpa using congrArg Subtype.val hj


/-- **Sylow reduction of a finite torsion module.** Let `G` be a profinite (more generally,
compact) group, `ℓ` a prime and `M` a finite `ℓ`-primary discrete `G`-module. There is an open
subgroup `K` of index prime to `ℓ` and a finite filtration `0 = F₀ ≤ F₁ ≤ ⋯ ≤ Fₙ = M` by
`K`-stable subgroups whose successive quotients `Fᵢ₊₁ / Fᵢ` are trivial `𝔽_ℓ`-modules: they are
killed by `ℓ` and `K` acts trivially on them.
(blueprint: `theorem-cohomology-curves`) -/
theorem exists_isOpen_not_dvd_index_filtration [CompactSpace G] (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite M.obj.V] (hM : ∀ x : M.obj.V, ∃ j : ℕ, ℓ ^ j • x = 0) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ¬ ℓ ∣ K.index ∧
      ∃ (n : ℕ) (F : ℕ → AddSubgroup M.obj.V), F 0 = ⊥ ∧ F n = ⊤ ∧ Monotone F ∧
        (∀ i, ∀ k ∈ K, ∀ x ∈ F i, (M.obj.ρ k).asHom.hom x ∈ F i) ∧
        (∀ i, ∀ x ∈ F (i + 1), ℓ • x ∈ F i) ∧
        (∀ i, ∀ k ∈ K, ∀ x ∈ F (i + 1), (M.obj.ρ k).asHom.hom x - x ∈ F i) := by
  obtain ⟨K, hKo, hKℓ, -, hpow⟩ := exists_isOpen_not_dvd_index_pow_mem M ℓ
  let := M.obj.distribMulAction
  let : DistribMulAction K M.obj.V := DistribMulAction.compHom _ K.subtype
  obtain ⟨n, F, h0, hn, hmono, hK, hℓ, htriv⟩ := exists_filtration_of_isPGroup (K := K) ℓ
    ((actionKernel M).comap K.subtype) (fun k hk x ↦ (mem_actionKernel M).1 hk x)
    (fun k ↦ by simpa [Subgroup.mem_subgroupOf] using hpow k k.2) hM
  exact ⟨K, hKo, hKℓ, n, F, h0, hn, hmono, fun i k hk ↦ hK i ⟨k, hk⟩, hℓ,
    fun i k hk ↦ htriv i ⟨k, hk⟩⟩

end DiscreteModule
