/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.NatIso

/-! # Semilinear comparison of localized bilinear functors

Extracted proved scalar-localization calculus used by the derived-operation construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂
open Opposite TensorProduct CategoryTheory
namespace WeilConjectures.OperationsScalarLocalization

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private def bilinearAdd {R : Type*} [CommSemiring R]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (b : M →ₗ[R] N →ₗ[R] P) :
    M →+ N →+ P :=
  LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom

private def bilinearPost {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (b : M →+ N →+ P) (f : P →+ Q) : M →+ N →+ Q where
  toFun x := f.comp (b x)
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

private def bilinearPre {M N P M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    (b : M →+ N →+ P) (f : M' →+ M) (g : N' →+ N) : M' →+ N' →+ P where
  toFun x := (b (f x)).comp g
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

private theorem prod_hom_heq
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {X Y X' Y' : C} {Z T Z' T' : D}
    (hx : X = X') (hy : Y = Y') (hz : Z = Z') (ht : T = T')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Z ⟶ T} {g' : Z' ⟶ T'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (Prod.mkHom f g) (Prod.mkHom f' g') := by
  cases hx; cases hy; cases hz; cases ht
  cases hf; cases hg
  rfl

private theorem rawBilinearIso_existsUnique
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

-- Keep the composition calculation generic, so it never unfolds a derived Hom group.
section SemilinearTensorComparison
set_option backward.defeqAttrib.useBackward false

/-- Semilinear comparison of localized bilinear functors.
Source: module base change (Stacks 00CV, 00CX), and the rational paragraph of
blueprint `prose-03-02`.
(blueprint: lem-sf-localized-bilinear-comparison).
Proof: Construct a normalized natural isomorphism by conjugating localized integral components
with the object equalities. Double tensor induction proves naturality from the integral naturality
square and coefficient multiplication. For the semilinear composite, postcompose the source
bilinear Hom map with the additive scalar functor; precompose the target bilinear Hom map with
that functor in both arguments. The pure-tensor map formula and multiplicativity of the
coefficient homomorphism identify both comparisons with the normalized integral comparison.
Component extensionality proves uniqueness. -/
theorem bilinearComparison_existsUnique
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]
    (t : R) (tS : S) (c : Localization.Away t →+* Localization.Away tS)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (r : C ⥤ D)
    (A : ScalarLocalization R C t × ScalarLocalization R C t ⥤ ScalarLocalization R C t)
    (B : ScalarLocalization S D tS × ScalarLocalization S D tS ⥤ ScalarLocalization S D tS)
    (T : ScalarLocalization R C t ⥤ ScalarLocalization S D tS) [T.Additive]
    (hA : ∀ K, A.obj K = ⟨U.obj (K.1.obj, K.2.obj)⟩)
    (hB : ∀ K, B.obj K = ⟨V.obj (K.1.obj, K.2.obj)⟩)
    (hT : ∀ K, T.obj K = ⟨r.obj K.obj⟩)
    (mT : ∀ (K K' : C) (a : K ⟶ K') (x : Localization.Away t),
      HEq (T.map (x ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk K'))
        (c x ⊗ₜ[S] r.map a))
    (mA : ∀ (K K' N N' : ScalarLocalization R C t),
      ∃ β : (K ⟶ K') →ₗ[Localization.Away t] (N ⟶ N') →ₗ[Localization.Away t]
          (A.obj (K, N) ⟶ A.obj (K', N')),
        (∀ a b, A.map (Prod.mkHom a b) = β a b) ∧
        ∀ (a : K.obj ⟶ K'.obj) (b : N.obj ⟶ N'.obj) (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] a) (y ⊗ₜ[R] b)) ((x * y) ⊗ₜ[R] U.map (Prod.mkHom a b)))
    (mB : ∀ (K K' N N' : ScalarLocalization S D tS),
      ∃ β : (K ⟶ K') →ₗ[Localization.Away tS] (N ⟶ N') →ₗ[Localization.Away tS]
          (B.obj (K, N) ⟶ B.obj (K', N')),
        (∀ a b, B.map (Prod.mkHom a b) = β a b) ∧
        ∀ (a : K.obj ⟶ K'.obj) (b : N.obj ⟶ N'.obj) (x y : Localization.Away tS),
          HEq (β (x ⊗ₜ[S] a) (y ⊗ₜ[S] b)) ((x * y) ⊗ₜ[S] V.map (Prod.mkHom a b)))
    (μ : U ⋙ r ≅ r.prod r ⋙ V) :
    ∃! α : A ⋙ T ≅ T.prod T ⋙ B,
      ∀ K, HEq (α.hom.app K)
        ((ScalarLocalization.localization S D tS).map (μ.hom.app (K.1.obj, K.2.obj))) := by
  apply rawBilinearIso_existsUnique t tS c (U ⋙ r) (r.prod r ⋙ V) μ
    (A ⋙ T) (T.prod T ⋙ B)
  · intro K
    exact (congrArg T.obj (hA K)).trans (hT _)
  · intro K
    exact (hB _).trans (congrArg
      (fun Z : ScalarLocalization S D tS × ScalarLocalization S D tS ↦
        ScalarLocalization.mk (V.obj (Z.1.obj, Z.2.obj)))
      (congrArg₂ Prod.mk (hT K.1) (hT K.2)))
  · intro K K' N N'
    obtain ⟨β, hβ, pβ⟩ := mA K K' N N'
    let γ := bilinearPost (bilinearAdd (R := Localization.Away t) β) T.mapAddHom
    refine ⟨γ, ?_, ?_⟩
    · intro a b
      change T.map (A.map (Prod.mkHom a b)) = T.map (β a b)
      rw [hβ]
    · intro a b x y
      exact (map_heq T (hA _) (hA _) (pβ a b x y)).trans
        (mT _ _ (U.map (Prod.mkHom a b)) (x * y))
  · intro K K' N N'
    obtain ⟨β, hβ, pβ⟩ := mB (T.obj K) (T.obj K') (T.obj N) (T.obj N')
    let γ := bilinearPre (bilinearAdd (R := Localization.Away tS) β) T.mapAddHom T.mapAddHom
    refine ⟨γ, ?_, ?_⟩
    · intro a b
      exact hβ (T.map a) (T.map b)
    · intro a b x y
      change HEq (β (T.map _) (T.map _)) _
      rw [← hβ]
      have hp := prod_hom_heq (hT K) (hT K') (hT N) (hT N')
        (mT K.obj K'.obj a x) (mT N.obj N'.obj b y)
      have hm := map_heq B (congrArg₂ Prod.mk (hT K) (hT N))
        (congrArg₂ Prod.mk (hT K') (hT N')) hp
      obtain ⟨δ, hδ, pδ⟩ := mB ⟨r.obj K.obj⟩ ⟨r.obj K'.obj⟩
        ⟨r.obj N.obj⟩ ⟨r.obj N'.obj⟩
      have hd := pδ (r.map a) (r.map b) (c x) (c y)
      rw [← hδ] at hd
      rw [← c.map_mul] at hd
      exact hm.trans hd

end SemilinearTensorComparison

end WeilConjectures.OperationsScalarLocalization
