/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import Mathlib.CategoryTheory.EqToHom

/-! # Natural isomorphisms between prescribed raw bilinear scalar extensions

Source: the existing rawBilinearIso_existsUnique proof in DerivedPullbackTensorHom.
(blueprint: lem-weil-raw-bilinear-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe r s u₁ v₁ u₂ v₂
open TensorProduct CategoryTheory

namespace WeilConjectures.RawBilinearScalarComparison

attribute [local irreducible] ScalarLocalization.composition

/-- A prescribed raw bilinear scalar extension carries the integral natural isomorphism.
Source: the existing rawBilinearIso_existsUnique proof in DerivedPullbackTensorHom.
(blueprint: lem-weil-raw-bilinear-scalar-comparison).
Proof: conjugate each localized component of the integral isomorphism by the
prescribed object equalities. Prove naturality by tensor-product induction in each
arrow. Additivity handles sums and zero. For pure tensors, substitute both prescribed
bilinear formulas; localization composition reduces to scalar multiplication and
integral naturality. These components define a natural isomorphism. The prescribed
component formula determines every component and hence the whole isomorphism. -/
theorem existsUnique
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]
    (t : R) (b : S) (c : Localization.Away t → Localization.Away b)
    (U V : C × C ⥤ D) (e : U ≅ V)
    (F G : ScalarLocalization R C t × ScalarLocalization R C t ⥤
      ScalarLocalization S D b)
    (hF : ∀ K, F.obj K = ⟨U.obj (K.1.obj, K.2.obj)⟩)
    (hG : ∀ K, G.obj K = ⟨V.obj (K.1.obj, K.2.obj)⟩)
    (mF : ∀ (K K' L L' : ScalarLocalization R C t),
      ∃ β : (K ⟶ K') →+
        (L ⟶ L') →+ (F.obj (K, L) ⟶ F.obj (K', L')),
        (∀ f g, F.map (Prod.mkHom f g) = β f g) ∧
        ∀ (f : K.obj ⟶ K'.obj) (g : L.obj ⟶ L'.obj) (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] f) (y ⊗ₜ[R] g))
            (c (x * y) ⊗ₜ[S] U.map (Prod.mkHom f g)))
    (mG : ∀ (K K' L L' : ScalarLocalization R C t),
      ∃ β : (K ⟶ K') →+
        (L ⟶ L') →+ (G.obj (K, L) ⟶ G.obj (K', L')),
        (∀ f g, G.map (Prod.mkHom f g) = β f g) ∧
        ∀ (f : K.obj ⟶ K'.obj) (g : L.obj ⟶ L'.obj) (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] f) (y ⊗ₜ[R] g))
            (c (x * y) ⊗ₜ[S] V.map (Prod.mkHom f g))) :
    ∃! α : F ≅ G, ∀ K, HEq (α.hom.app K)
      ((ScalarLocalization.localization S D b).map (e.hom.app (K.1.obj, K.2.obj))) := by
  let Q := ScalarLocalization.localization S D b
  let a K := eqToIso (hF K) ≪≫ Q.mapIso (e.app (K.1.obj, K.2.obj)) ≪≫
    (eqToIso (hG K)).symm
  have ha K : HEq (a K).hom (Q.map (e.hom.app (K.1.obj, K.2.obj))) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Functor.mapIso_hom]
    exact ((conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 rfl)
  have hn (K L : ScalarLocalization R C t × ScalarLocalization R C t)
      (f : K ⟶ L) : F.map f ≫ (a L).hom = (a K).hom ≫ G.map f := by
    obtain ⟨β, hβ, pβ⟩ := mF K.1 L.1 K.2 L.2
    obtain ⟨γ, hγ, pγ⟩ := mG K.1 L.1 K.2 L.2
    change F.map (Prod.mkHom f.1 f.2) ≫ _ = _ ≫ G.map (Prod.mkHom f.1 f.2)
    rw [hβ, hγ]
    generalize f.1 = f₁, f.2 = f₂
    change Localization.Away t ⊗[R] (K.1.obj ⟶ L.1.obj) at f₁
    change Localization.Away t ⊗[R] (K.2.obj ⟶ L.2.obj) at f₂
    induction f₁ using TensorProduct.inductionOn with
    | tmul x f₁ =>
      induction f₂ using TensorProduct.inductionOn with
      | tmul y f₂ =>
        have h₁ := heq_comp (hF K) (hF L) (hG L) (pβ f₁ f₂ x y) (ha L)
        have h₂ := heq_comp (hF K) (hG K) (hG L) (ha K) (pγ f₁ f₂ x y)
        apply eq_of_heq
        refine h₁.trans (HEq.trans ?_ h₂.symm)
        apply heq_of_eq
        change ScalarLocalization.composition S D b _ _ _
            (1 ⊗ₜ[S] e.hom.app (L.1.obj, L.2.obj))
            (c (x * y) ⊗ₜ[S] U.map (Prod.mkHom f₁ f₂)) =
          ScalarLocalization.composition S D b _ _ _
            (c (x * y) ⊗ₜ[S] V.map (Prod.mkHom f₁ f₂))
            (1 ⊗ₜ[S] e.hom.app (K.1.obj, K.2.obj))
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one,
          e.hom.naturality]
      | add x y hx hy => simp only [map_add, Preadditive.add_comp,
          Preadditive.comp_add, hx, hy]
    | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply,
        Preadditive.add_comp, Preadditive.comp_add, hx, hy]
  refine ⟨NatIso.ofComponents a (fun {K L} f ↦ hn K L f), ha, ?_⟩
  intro α hα
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hα K).trans (ha K).symm)

end WeilConjectures.RawBilinearScalarComparison
