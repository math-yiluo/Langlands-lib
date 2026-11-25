/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Group.TypeTags.Basic

/-! # Comparing representation functors on a common additive fibre

Source: the ordinary intertwiner and scalar-linearity argument for a fibre functor.
(blueprint: lem-dl-a1-fibre-action-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe uC vC uR uV uW
open CategoryTheory
namespace Representation

/-- Agreement of two transported actions in nonnegative degree implies agreement everywhere.
Source: the inverse identity for a group representation.
(blueprint: lem-dl-a1-fibre-action-comparison).

Proof: negative-degree elements have positive-degree inverses. Apply the given
identity to the inverse, the moved first vector, and its unique matching second
vector. Cancel the inverse actions using their group law. -/
theorem fibre_action_of_nonnegative
    {R : Type uR} [Semiring R] {W : Type uW} [Group W]
    {V U : Type uV} [AddCommMonoid V] [AddCommMonoid U] [Module R V] [Module R U]
    (ρ : Representation R W V) (σ : Representation R W U)
    {B : Type uV} (β : V → B) (γ : U → B) (hγ : Function.Bijective γ)
    (d : W →* Multiplicative ℤ)
    (h : ∀ w, 0 ≤ (d w).toAdd → ∀ v u, β v = γ u → β (ρ w v) = γ (σ w u)) :
    ∀ w v u, β v = γ u → β (ρ w v) = γ (σ w u) := by
  intro w v u hvu
  by_cases hw : 0 ≤ (d w).toAdd
  · exact h w hw v u hvu
  · have hwi : 0 ≤ (d w⁻¹).toAdd := by
      rw [map_inv, toAdd_inv]
      omega
    obtain ⟨z, hz⟩ := hγ.surjective (β (ρ w v))
    have hi := h w⁻¹ hwi (ρ w v) z hz.symm
    have hc : ρ w⁻¹ (ρ w v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hc, hvu] at hi
    have hu : u = σ w⁻¹ z := hγ.injective hi
    rw [hu, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact hz.symm

/-- Geometric-kernel and positive-return formulas determine the transported action.
Source: Weil II (1.1.10), generation by the degree kernel and positive elements.
(blueprint: lem-dl-a1-fibre-action-comparison).

Proof: degree zero means membership in the geometric image. A strictly positive
integer is uniquely n+1 for a natural n. Apply these two formulas in nonnegative
degree, then use inversion for negative degree. No degree-one lift is assumed. -/
theorem fibre_action_of_geometric_positive
    {R : Type uR} [Semiring R] {W : Type uW} [Group W]
    {V U : Type uV} [AddCommMonoid V] [AddCommMonoid U] [Module R V] [Module R U]
    (ρ : Representation R W V) (σ : Representation R W U)
    {B : Type uV} (β : V → B) (γ : U → B) (hγ : Function.Bijective γ)
    (d : W →* Multiplicative ℤ) {P : Type uW} [Group P] (j : P →* W)
    (hj : j.range = d.ker)
    (hgeo : ∀ a v u, β v = γ u → β (ρ (j a) v) = γ (σ (j a) u))
    (hpos : ∀ w (n : ℕ), d w = Multiplicative.ofAdd (n + 1 : ℤ) →
      ∀ v u, β v = γ u → β (ρ w v) = γ (σ w u)) :
    ∀ w v u, β v = γ u → β (ρ w v) = γ (σ w u) := by
  apply fibre_action_of_nonnegative ρ σ β γ hγ d
  intro w hw v u hvu
  by_cases hz : (d w).toAdd = 0
  · have hmem : w ∈ d.ker := Multiplicative.toAdd.injective hz
    rw [← hj] at hmem
    obtain ⟨a, rfl⟩ := hmem
    exact hgeo a v u hvu
  · let n := (d w).toAdd.toNat - 1
    have hd : d w = Multiplicative.ofAdd (n + 1 : ℤ) := by
      apply Multiplicative.toAdd.injective
      change (d w).toAdd = (n : ℤ) + 1
      dsimp only [n]
      omega
    exact hpos w n hd v u hvu

/-- Linearity and equality of transported actions lift a natural additive fibre comparison.
Source: fibre-functor uniqueness by linear intertwining maps.
(blueprint: lem-dl-a1-fibre-action-comparison).

Proof: compose the first fibre isomorphism with the inverse of the second. The
common scalar formula makes each component linear, and its bijectivity makes it
a linear equivalence. The action identity says it is a representation equivalence.
The original additive naturality squares give naturality of these intertwiners;
faithfulness of the inclusions and the underlying-vector-space functor detects
the required equations. -/
theorem functor_iso_of_fibre_action
    {C : Type uC} [Category.{vC} C]
    {R : Type uR} [CommRing R] {W : Type uW} [Group W]
    {P : ObjectProperty (Rep.{uV} R W)} (F G : C ⥤ P.FullSubcategory)
    (H : C ⥤ Ab.{uV})
    (β : F ⋙ P.ι ⋙ forget₂ (Rep.{uV} R W) (ModuleCat.{uV} R) ⋙
      forget₂ (ModuleCat.{uV} R) Ab.{uV} ≅ H)
    (γ : G ⋙ P.ι ⋙ forget₂ (Rep.{uV} R W) (ModuleCat.{uV} R) ⋙
      forget₂ (ModuleCat.{uV} R) Ab.{uV} ≅ H)
    (s : ∀ X : C, R → H.obj X → H.obj X)
    (hβ : ∀ X a (v : (F.obj X).obj.V),
      β.hom.app X (a • v) = s X a (β.hom.app X v))
    (hγ : ∀ X a (v : (G.obj X).obj.V),
      γ.hom.app X (a • v) = s X a (γ.hom.app X v))
    (hact : ∀ X w (v : (F.obj X).obj.V) (u : (G.obj X).obj.V),
      β.hom.app X v = γ.hom.app X u →
      β.hom.app X ((F.obj X).obj.ρ w v) = γ.hom.app X ((G.obj X).obj.ρ w u)) :
    Nonempty (F ≅ G) := by
  classical
  have he (X : C) : ∃ e : (F.obj X).obj.V ≃ₗ[R] (G.obj X).obj.V,
      ∀ v, γ.hom.app X (e v) = β.hom.app X v := by
    let b := β.app X ≪≫ (γ.app X).symm
    have hb (v : (F.obj X).obj.V) : γ.hom.app X (b.hom v) = β.hom.app X v := by
      exact ConcreteCategory.congr_hom
        (show b.hom ≫ γ.hom.app X = β.hom.app X by dsimp only [b]; simp) v
    let f : (F.obj X).obj.V →ₗ[R] (G.obj X).obj.V :=
      { toFun := b.hom
        map_add' := b.hom.hom.map_add
        map_smul' := by
          intro a v
          apply (ConcreteCategory.bijective_of_isIso (γ.hom.app X)).injective
          simp only [hb, hβ, hγ, RingHom.id_apply] }
    exact ⟨LinearEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso b.hom), hb⟩
  choose e he using he
  let f (X : C) : (F.obj X).obj.ρ.Equiv (G.obj X).obj.ρ :=
    Representation.Equiv.mk (e X) (by
      intro w
      ext v
      apply (ConcreteCategory.bijective_of_isIso (γ.hom.app X)).injective
      exact (he X _).trans (hact X w v (e X v) (he X v).symm))
  let b (X : C) : F.obj X ≅ G.obj X := ObjectProperty.isoMk _ (Rep.mkIso (f X))
  refine ⟨NatIso.ofComponents b ?_⟩
  intro X Y a
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  ext v
  apply (ConcreteCategory.bijective_of_isIso (γ.hom.app Y)).injective
  change γ.hom.app Y (e Y ((F.map a).hom.hom v)) =
    γ.hom.app Y ((G.map a).hom.hom (e X v))
  rw [he]
  have hF := ConcreteCategory.congr_hom (β.hom.naturality a) v
  have hG := ConcreteCategory.congr_hom (γ.hom.naturality a) (e X v)
  change β.hom.app Y ((F.map a).hom.hom v) = H.map a (β.hom.app X v) at hF
  change γ.hom.app Y ((G.map a).hom.hom (e X v)) =
    H.map a (γ.hom.app X (e X v)) at hG
  rw [hF, hG, he]

end Representation
