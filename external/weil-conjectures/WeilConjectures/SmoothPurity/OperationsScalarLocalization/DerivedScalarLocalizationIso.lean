/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.NatIso

/-! # Normalized isomorphisms of localized functors

Extracted proved scalar-localization calculus used by the derived-operation construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂
open Opposite TensorProduct CategoryTheory
namespace WeilConjectures.OperationsScalarLocalization

/-- Normalized isomorphisms of localized functors.
Source: module base change (Stacks 00CV, 00CX), and the rational paragraph of
blueprint `prose-03-02`.
(blueprint: lem-sf-localized-natural-iso).
Proof: Conjugate the localized integral comparison by the prescribed object equalities. On a pure
tensor, the two map formulas and the integral naturality square prove naturality; additivity
proves it on zero and sums. The conjugated components are isomorphisms, hence form a natural
isomorphism. The prescribed component equality and natural transformation extensionality prove
uniqueness. -/
theorem iso_existsUnique
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]
    (t : R) (b : S) (c : Localization.Away t → Localization.Away b)
    (U V : C ⥤ D) (e : U ≅ V)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D b)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨U.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨V.obj K.obj⟩)
    (mF : ∀ (K L : C) (a : K ⟶ L) (z : Localization.Away t),
      HEq (F.map (z ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c z ⊗ₜ[S] U.map a))
    (mG : ∀ (K L : C) (a : K ⟶ L) (z : Localization.Away t),
      HEq (G.map (z ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c z ⊗ₜ[S] V.map a)) :
    ∃! α : F ≅ G, ∀ K, HEq (α.hom.app K)
      ((ScalarLocalization.localization S D b).map (e.hom.app K.obj)) := by
  let Q := ScalarLocalization.localization S D b
  let a (K : ScalarLocalization R C t) :=
    eqToIso (hF K) ≪≫ Q.mapIso (e.app K.obj) ≪≫ (eqToIso (hG K)).symm
  have ha (K : ScalarLocalization R C t) :
      HEq (a K).hom (Q.map (e.hom.app K.obj)) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Functor.mapIso_hom]
    exact ((conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 rfl)
  have hn (K L : ScalarLocalization R C t) (f : K ⟶ L) :
      F.map f ≫ (a L).hom = (a K).hom ≫ G.map f := by
    change Localization.Away t ⊗[R] (K.obj ⟶ L.obj) at f
    induction f using TensorProduct.inductionOn with
    | tmul z f =>
      have h₁ := heq_comp (hF K) (hF L) (hG L) (mF K.obj L.obj f z) (ha L)
      have h₂ := heq_comp (hF K) (hG K) (hG L) (ha K) (mG K.obj L.obj f z)
      apply eq_of_heq
      refine h₁.trans (HEq.trans ?_ h₂.symm)
      apply heq_of_eq
      change ScalarLocalization.composition S D b _ _ _
          (1 ⊗ₜ[S] e.hom.app L.obj) (c z ⊗ₜ[S] U.map f) =
        ScalarLocalization.composition S D b _ _ _
          (c z ⊗ₜ[S] V.map f) (1 ⊗ₜ[S] e.hom.app K.obj)
      simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, e.hom.naturality]
    | add x y hx hy => simp only [F.map_add, G.map_add,
        Preadditive.add_comp, Preadditive.comp_add, hx, hy]
  refine ⟨NatIso.ofComponents a (fun {K L} f ↦ hn K L f), ha, ?_⟩
  intro α hα
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hα K).trans (ha K).symm)

end WeilConjectures.OperationsScalarLocalization
