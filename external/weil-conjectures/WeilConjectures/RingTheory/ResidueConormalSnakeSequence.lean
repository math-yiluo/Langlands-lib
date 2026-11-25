/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PthRootResidueDifferentials
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import WeilConjectures.RingTheory.SubsingletonH1CotangentOfCharP
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Extension.ExtendScalars

/-! # The snake sequence of absolute residue conormal rows

Source: Stacks Project, More on Algebra, Tag 07E5, the big conormal diagram.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Field Jacobi-Zariski identifies the two defects of absolute differential comparison.

Source: Stacks Project, Algebra, Tags 00S2 and 0322; More on Algebra, Tag 07E5.

Proof: In Jacobi-Zariski for F_p -> K -> L, H1(L/F_p) is zero because a
field extension of a perfect field is formally smooth. Exactness therefore makes
H1(L/K) -> L tensor_K Omega[K/F_p] injective with image the kernel of gamma.
Restrict this connecting map to its image to obtain the first equivalence.
The right exact differential sequence identifies the image of gamma with the
kernel of the surjection Omega[L/F_p] -> Omega[L/K]. The first isomorphism
theorem gives the second equivalence. No separability assumption on L/K is used:
purely inseparable extensions may have nonzero H1(L/K). For K=L both defects
are zero, as are H1(K/K) and Omega[K/K]. -/
private theorem primeField_differential_defects
    (p : ℕ) [Fact p.Prime] (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra (ZMod p) K] [Algebra K L]
    [Algebra (ZMod p) L] [IsScalarTower (ZMod p) K L] :
    let γ := KaehlerDifferential.mapBaseChange (ZMod p) K L
    Nonempty (H1Cotangent K L ≃ₗ[L] γ.ker) ∧
      Nonempty ((KaehlerDifferential (ZMod p) L ⧸ γ.range) ≃ₗ[L]
        KaehlerDifferential K L)  := by
  classical
  dsimp
  have : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have hsub : Subsingleton (H1Cotangent (ZMod p) L) := by
    have h := subsingleton_h1Cotangent_of_charP p (Fact.out : p.Prime).pos L
    have he : ZMod.algebra L p = (inferInstance : Algebra (ZMod p) L) :=
      Subsingleton.elim _ _
    rw [he] at h
    exact h
  let δ := H1Cotangent.δ (ZMod p) K L
  have hi : Function.Injective δ := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (H1Cotangent.exact_map_δ (ZMod p) K L)).mpr
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  let δ' : H1Cotangent K L →ₗ[L]
      (KaehlerDifferential.mapBaseChange (ZMod p) K L).ker :=
    δ.codRestrict _ (fun x ↦
      (H1Cotangent.exact_δ_mapBaseChange (ZMod p) K L).apply_apply_eq_zero x)
  have hb : Function.Bijective δ' := by
    constructor
    · intro x y hxy
      exact hi (congrArg Subtype.val hxy)
    · intro x
      obtain ⟨y, hy⟩ :=
        (H1Cotangent.exact_δ_mapBaseChange (ZMod p) K L x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨⟨LinearEquiv.ofBijective δ' hb⟩,
    ⟨(KaehlerDifferential.exact_mapBaseChange_map (ZMod p) K L).linearEquivOfSurjective
      (KaehlerDifferential.map_surjective (ZMod p) K L)⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem local_conormal_row
    (p : ℕ) [Fact p.Prime] (A : Type u)
    [CommRing A] [Algebra (ZMod p) A] [IsLocalRing A] :
    ∃ c : IsLocalRing.CotangentSpace A →ₗ[IsLocalRing.ResidueField A]
        (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential (ZMod p) A),
      Function.Injective c ∧ Function.Exact c
        (KaehlerDifferential.mapBaseChange (ZMod p) A (IsLocalRing.ResidueField A)) := by
  classical
  let K := IsLocalRing.ResidueField A
  let P := Extension.ofSurjective (IsScalarTower.toAlgHom (ZMod p) A K)
    (IsLocalRing.residue_surjective (R := A))
  let e₀ : P.Cotangent ≃ₗ[A] IsLocalRing.CotangentSpace A := by
    let ek : P.Cotangent ≃ₗ[A] (RingHom.ker (IsLocalRing.residue A)).Cotangent :=
      P.cotangentEquivCotangentKer
    exact ek.trans (Ideal.Cotangent.equivOfEq _ _ IsLocalRing.ker_residue)
  let e := e₀.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := A))
  let c : IsLocalRing.CotangentSpace A →ₗ[K] (K ⊗[A] KaehlerDifferential (ZMod p) A) :=
    P.cotangentComplex.comp e.symm.toLinearMap
  have : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hsub : Subsingleton (H1Cotangent (ZMod p) K) := by
    have h := subsingleton_h1Cotangent_of_charP p (Fact.out : p.Prime).pos K
    have he : ZMod.algebra K p = (inferInstance : Algebra (ZMod p) K) :=
      Subsingleton.elim _ _
    rw [he] at h
    exact h
  have hi : Function.Injective (H1Cotangent.δ (ZMod p) A K) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (H1Cotangent.exact_map_δ (ZMod p) A K)).mpr
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hδ : P.cotangentComplex.comp P.h1CotangentEquivCotangent.toLinearMap =
      H1Cotangent.δ (ZMod p) A K := P.cotangentComplex_comp_h1CotangentEquivCotangent
  have hi' : Function.Injective P.cotangentComplex := by
    intro x y hxy
    apply P.h1CotangentEquivCotangent.symm.injective
    apply hi
    rw [← hδ]
    change P.cotangentComplex (P.h1CotangentEquivCotangent
      (P.h1CotangentEquivCotangent.symm x)) =
      P.cotangentComplex (P.h1CotangentEquivCotangent
        (P.h1CotangentEquivCotangent.symm y))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hxy
  refine ⟨c, hi'.comp e.symm.injective, ?_⟩
  have hex : Function.Exact P.cotangentComplex
      (KaehlerDifferential.mapBaseChange (ZMod p) A K) := by
    have h := H1Cotangent.exact_δ_mapBaseChange (ZMod p) A K
    rw [← hδ] at h
    exact P.h1CotangentEquivCotangent.surjective.comp_exact_iff_exact.mp h
  exact e.symm.surjective.comp_exact_iff_exact.mpr hex

set_option backward.isDefEq.respectTransparency false in
/-- The two short exact conormal rows commute with the residue differential comparison.

Source: Stacks Project, More on Algebra, Tag 07E5, big conormal diagram.

Proof: Apply Jacobi-Zariski to F_p -> A -> K. H1(K/F_p) vanishes, so the
connecting map is injective; identify its source H1(K/A) with m_A/m_A² using the
surjective presentation. Its cokernel is Omega[K/F_p]. Tensor this short exact
row with L over K, which preserves exactness and injection since K is a field.
Tensor cancellation identifies the middle module with L tensor_A Omega[A/F_p].
Apply the same construction to B -> L. For the right square, both composites
send l tensor da to l tensor d(residue(a)); these elements span the source,
proving equality. Exactness now puts beta a in ker d = range c. Factor beta a through the
inverse of the
injective arrow c onto its range to define alpha and prove the left square. The quotient
maps in both rows are surjective by the right exact differential sequence.
This also covers A and B fields, when their conormal spaces are zero. -/
private theorem residue_conormal_snake_rows
    (p : ℕ) [Fact p.Prime] (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra (ZMod p) A] [Algebra A B]
    [Algebra (ZMod p) B] [IsScalarTower (ZMod p) A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] :
    let K := IsLocalRing.ResidueField A
    let L := IsLocalRing.ResidueField B
    let β := residueDifferentialComparison p A B
    let γ := KaehlerDifferential.mapBaseChange (ZMod p) K L
    ∃ (α : (L ⊗[K] IsLocalRing.CotangentSpace A) →ₗ[L] IsLocalRing.CotangentSpace B)
      (a : (L ⊗[K] IsLocalRing.CotangentSpace A) →ₗ[L]
        (L ⊗[A] KaehlerDifferential (ZMod p) A))
      (b : (L ⊗[A] KaehlerDifferential (ZMod p) A) →ₗ[L]
        (L ⊗[K] KaehlerDifferential (ZMod p) K))
      (c : IsLocalRing.CotangentSpace B →ₗ[L]
        (L ⊗[B] KaehlerDifferential (ZMod p) B))
      (d : (L ⊗[B] KaehlerDifferential (ZMod p) B) →ₗ[L]
        KaehlerDifferential (ZMod p) L),
      Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
      Function.Injective c ∧ Function.Exact c d ∧ Function.Surjective d ∧
      c.comp α = β.comp a ∧ d.comp β = γ.comp b := by
  classical
  dsimp
  let K := IsLocalRing.ResidueField A
  let L := IsLocalRing.ResidueField B
  let β := residueDifferentialComparison p A B
  let γ := KaehlerDifferential.mapBaseChange (ZMod p) K L
  obtain ⟨a₀, ha₀, hab₀⟩ := local_conormal_row p A
  obtain ⟨c, hc, hcd⟩ := local_conormal_row p B
  let b₀ := KaehlerDifferential.mapBaseChange (ZMod p) A K
  let d := KaehlerDifferential.mapBaseChange (ZMod p) B L
  have hb₀ : Function.Surjective b₀ :=
    KaehlerDifferential.mapBaseChange_surjective (ZMod p) A K IsLocalRing.residue_surjective
  have hd : Function.Surjective d :=
    KaehlerDifferential.mapBaseChange_surjective (ZMod p) B L IsLocalRing.residue_surjective
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A K L L
    (KaehlerDifferential (ZMod p) A)
  let a := e.toLinearMap.comp (a₀.baseChange L)
  let b := (b₀.baseChange L).comp e.symm.toLinearMap
  have ha : Function.Injective a :=
    e.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap a₀ ha₀)
  have hab : Function.Exact a b := by
    apply (LinearEquiv.conj_exact_iff_exact _ _ e).mpr
    exact Module.Flat.lTensor_exact L hab₀
  have hb : Function.Surjective b :=
    (LinearMap.lTensor_surjective L hb₀).comp e.symm.surjective
  have h₂ : d.comp β = γ.comp b := by
    ext l
    simp [K, L, d, β, residueDifferentialComparison, γ, b, b₀, e,
      LinearMap.baseChange_tmul, KaehlerDifferential.mapBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  let t : (L ⊗[K] IsLocalRing.CotangentSpace A) →ₗ[L] c.range :=
    (β.comp a).codRestrict c.range (fun x ↦ by
      rw [← hcd.linearMap_ker_eq, LinearMap.mem_ker]
      change d (β (a x)) = 0
      rw [← LinearMap.comp_apply, h₂]
      change γ (b (a x)) = 0
      rw [hab.apply_apply_eq_zero, map_zero])
  let α := (LinearEquiv.ofInjective c hc).symm.toLinearMap.comp t
  have h₁ : c.comp α = β.comp a := by
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective c hc).apply_symm_apply (t x))
  exact ⟨α, a, b, c, d, ha, hab, hb, hc, hcd, hd, h₁, h₂⟩

private theorem module_snake
    {R M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    (α : M₁ →ₗ[R] N₁) (β : M₂ →ₗ[R] N₂) (γ : M₃ →ₗ[R] N₃)
    (a : M₁ →ₗ[R] M₂) (b : M₂ →ₗ[R] M₃)
    (c : N₁ →ₗ[R] N₂) (d : N₂ →ₗ[R] N₃)
    (ha : Function.Injective a) (hab : Function.Exact a b) (hb : Function.Surjective b)
    (hc : Function.Injective c) (hcd : Function.Exact c d) (hd : Function.Surjective d)
    (h₁ : c.comp α = β.comp a) (h₂ : d.comp β = γ.comp b) :
    ∃ (k₀ : α.ker →ₗ[R] β.ker) (k₁ : β.ker →ₗ[R] γ.ker)
      (δ : γ.ker →ₗ[R] (N₁ ⧸ α.range))
      (q₁ : (N₁ ⧸ α.range) →ₗ[R] (N₂ ⧸ β.range))
      (q₂ : (N₂ ⧸ β.range) →ₗ[R] (N₃ ⧸ γ.range)),
      Function.Injective k₀ ∧ Function.Exact k₀ k₁ ∧ Function.Exact k₁ δ ∧
      Function.Exact δ q₁ ∧ Function.Exact q₁ q₂ ∧ Function.Surjective q₂ := by
  classical
  let k₀ : α.ker →ₗ[R] β.ker :=
    (a.comp α.ker.subtype).codRestrict β.ker (fun x ↦ by
      change β (a x.val) = 0
      rw [← LinearMap.comp_apply, ← h₁, LinearMap.comp_apply, x.property, map_zero])
  let k₁ : β.ker →ₗ[R] γ.ker :=
    (b.comp β.ker.subtype).codRestrict γ.ker (fun x ↦ by
      change γ (b x.val) = 0
      rw [← LinearMap.comp_apply, ← h₂, LinearMap.comp_apply, x.property, map_zero])
  let q₁ : (N₁ ⧸ α.range) →ₗ[R] (N₂ ⧸ β.range) :=
    α.range.mapQ β.range c (by
      rintro _ ⟨x, rfl⟩
      exact ⟨a x, DFunLike.congr_fun h₁ x |>.symm⟩)
  let q₂ : (N₂ ⧸ β.range) →ₗ[R] (N₃ ⧸ γ.range) :=
    β.range.mapQ γ.range d (by
      rintro _ ⟨x, rfl⟩
      exact ⟨b x, DFunLike.congr_fun h₂ x |>.symm⟩)
  let δ := SnakeLemma.δ' α β γ a b hab c d hcd h₁ h₂
    γ.ker.subtype (LinearMap.exact_subtype_ker_map γ)
    α.range.mkQ (LinearMap.exact_map_mkQ_range α) hb hc
  refine ⟨k₀, k₁, δ, q₁, q₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply ha
    exact congrArg Subtype.val hxy
  · intro x
    constructor
    · intro hx
      have hx' : b x.val = 0 := congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (hab x.val).mp hx'
      have hy' : α y = 0 := by
        apply hc
        rw [map_zero, ← LinearMap.comp_apply, h₁, LinearMap.comp_apply, hy]
        exact x.property
      exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact hab.apply_apply_eq_zero y.val
  · exact SnakeLemma.exact_δ'_right α β γ a b hab c d hcd h₁ h₂
      β.ker.subtype (LinearMap.exact_subtype_ker_map β)
      γ.ker.subtype (LinearMap.exact_subtype_ker_map γ)
      α.range.mkQ (LinearMap.exact_map_mkQ_range α) hb hc k₁ rfl
      γ.ker.subtype_injective
  · exact SnakeLemma.exact_δ'_left α β γ a b hab c d hcd h₁ h₂
      γ.ker.subtype (LinearMap.exact_subtype_ker_map γ)
      α.range.mkQ (LinearMap.exact_map_mkQ_range α)
      β.range.mkQ (LinearMap.exact_map_mkQ_range β) hb hc q₁
      (Submodule.mapQ_mkQ _ _ _) α.range.mkQ_surjective
  · intro x
    obtain ⟨x, rfl⟩ := β.range.mkQ_surjective x
    change γ.range.mkQ (d x) = 0 ↔ ∃ y, q₁ y = β.range.mkQ x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := (LinearMap.exact_map_mkQ_range γ (d x)).mp hx
      obtain ⟨w, hw⟩ := hb z
      have hx' : d (x - β w) = 0 := by
        rw [map_sub, ← LinearMap.comp_apply, h₂, LinearMap.comp_apply, hw, hz, sub_self]
      obtain ⟨y, hy⟩ := (hcd (x - β w)).mp hx'
      refine ⟨α.range.mkQ y, ?_⟩
      change β.range.mkQ (c y) = β.range.mkQ x
      rw [hy, map_sub, (LinearMap.exact_map_mkQ_range β (β w)).mpr ⟨w, rfl⟩,
        sub_zero]
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := α.range.mkQ_surjective y
      have hzero : q₂ (q₁ (α.range.mkQ y)) = 0 := by
        change γ.range.mkQ (d (c y)) = 0
        rw [hcd.apply_apply_eq_zero, map_zero]
      rw [hy] at hzero
      exact hzero
  · intro x
    obtain ⟨x, rfl⟩ := γ.range.mkQ_surjective x
    obtain ⟨y, rfl⟩ := hd x
    exact ⟨β.range.mkQ y, rfl⟩

/-- The absolute residue comparison fits into the conormal snake sequence for any
local homomorphism of local algebras over the positive prime field.

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), big diagram;
Algebra, Tags 00S1 and 0322 for the conormal rows and prime-field homology vanishing.
(blueprint: lem-weil-pbc-residue-conormal-snake-sequence).

Proof: Write K and L for the residue fields. The Jacobi-Zariski sequence for
F_p -> A -> K, prime-field H1 vanishing, and the identification H1(K/A) = m/m²
produce a short exact conormal row. Tensor it with L over K; field extensions
are flat, and tensor cancellation identifies its middle term with L tensor_A
Omega[A/F_p]. The analogous row for B has middle term L tensor_B Omega[B/F_p].
Compatibility of differential maps with residue maps gives the square for beta
and the field differential comparison gamma: on generators both composites send
1 tensor df to d(residue(f)). Exactness puts beta a in the range of the injective
lower conormal arrow c. Factoring through c defines alpha and gives the first
commuting square without a connecting-map naturality theorem. Apply the module
snake lemma to these two short exact rows. Jacobi-Zariski for F_p -> K -> L
identifies ker gamma with H1(L/K), because H1(L/F_p) vanishes, and identifies coker gamma with
Omega[L/K].
Transport the snake maps through these two linear equivalences. This gives the
five displayed maps, their four exactness assertions, and the endpoint injection
and surjection. No finiteness or regularity is needed for this exact sequence. -/
theorem residue_conormal_snake_sequence
    (p : ℕ) [Fact p.Prime] (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra (ZMod p) A] [Algebra A B]
    [Algebra (ZMod p) B] [IsScalarTower (ZMod p) A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] :
    let K := IsLocalRing.ResidueField A
    let L := IsLocalRing.ResidueField B
    let β := residueDifferentialComparison p A B
    ∃ (α : (L ⊗[K] IsLocalRing.CotangentSpace A) →ₗ[L] IsLocalRing.CotangentSpace B)
      (f₀ : α.ker →ₗ[L] β.ker)
      (f₁ : β.ker →ₗ[L] H1Cotangent K L)
      (f₂ : H1Cotangent K L →ₗ[L] (IsLocalRing.CotangentSpace B ⧸ α.range))
      (f₃ : (IsLocalRing.CotangentSpace B ⧸ α.range) →ₗ[L]
        ((L ⊗[B] KaehlerDifferential (ZMod p) B) ⧸ β.range))
      (f₄ : ((L ⊗[B] KaehlerDifferential (ZMod p) B) ⧸ β.range) →ₗ[L]
        KaehlerDifferential K L),
      Function.Injective f₀ ∧ Function.Exact f₀ f₁ ∧ Function.Exact f₁ f₂ ∧
        Function.Exact f₂ f₃ ∧ Function.Exact f₃ f₄ ∧ Function.Surjective f₄ := by
  classical
  dsimp
  obtain ⟨α, a, b, c, d, ha, hab, hb, hc, hcd, hd, h₁, h₂⟩ :=
    residue_conormal_snake_rows p A B
  obtain ⟨⟨e⟩, ⟨e'⟩⟩ := primeField_differential_defects p
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  obtain ⟨k₀, k₁, δ, q₁, q₂, hk₀, hk01, hk1δ, hδq₁, hq12, hq₂⟩ :=
    module_snake α (residueDifferentialComparison p A B)
      (KaehlerDifferential.mapBaseChange (ZMod p)
        (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
      a b c d ha hab hb hc hcd hd h₁ h₂
  refine ⟨α, k₀, e.symm.toLinearMap.comp k₁, δ.comp e.toLinearMap,
    q₁, e'.toLinearMap.comp q₂, hk₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.symm.injective.comp_exact_iff_exact.mpr hk01
  · exact LinearEquiv.conj_symm_exact_iff_exact _ _ e |>.mpr hk1δ
  · exact e.surjective.comp_exact_iff_exact.mpr hδq₁
  · exact e'.injective.comp_exact_iff_exact.mpr hq12
  · exact e'.surjective.comp hq₂

end Algebra
