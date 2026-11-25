/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # open immersion projection formula

Source: the open and closed immersion paragraphs and the derived version of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/`
`det-lem-int-tensor-projection.proof.md`
(blueprint: lem-sfb-open-immersion-derived-tensor-projection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

private def isoOfHomEquiv {C : Type*} [Category* C] (A B : C)
    (e : ∀ T, (B ⟶ T) ≃ (A ⟶ T))
    (hn : ∀ (T T' : C) (x : B ⟶ T) (t : T ⟶ T'),
      e T' (x ≫ t) = e T x ≫ t) : A ≅ B where
  hom := e B (𝟙 B)
  inv := (e A).symm (𝟙 A)
  hom_inv_id := by
    rw [← hn B A (𝟙 B) ((e A).symm (𝟙 A))]
    simp
  inv_hom_id := by
    apply (e B).injective
    rw [hn]
    simp

private def bifunctorIsoOfHomEquiv
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F G : C ⥤ D ⥤ E)
    (e : ∀ A B T, ((G.obj A).obj B ⟶ T) ≃ ((F.obj A).obj B ⟶ T))
    (ht : ∀ A B T T' (x : (G.obj A).obj B ⟶ T) (t : T ⟶ T'),
      e A B T' (x ≫ t) = e A B T x ≫ t)
    (ha : ∀ A A' B T (a : A ⟶ A') (x : (G.obj A').obj B ⟶ T),
      e A B T ((G.map a).app B ≫ x) = (F.map a).app B ≫ e A' B T x)
    (hb : ∀ A B B' T (b : B ⟶ B') (x : (G.obj A).obj B' ⟶ T),
      e A B T ((G.obj A).map b ≫ x) = (F.obj A).map b ≫ e A B' T x) : F ≅ G := by
  refine NatIso.ofComponents (fun A ↦ NatIso.ofComponents
    (fun B ↦ isoOfHomEquiv _ _ (e A B) (ht A B)) ?_) ?_
  · intro B B' b
    change (F.obj A).map b ≫ e A B' _ (𝟙 _) = e A B _ (𝟙 _) ≫ (G.obj A).map b
    rw [← hb A B B' _ b (𝟙 _), Category.comp_id,
      ← ht A B _ _ (𝟙 _) ((G.obj A).map b), Category.id_comp]
  · intro A A' a
    ext B
    change (F.map a).app B ≫ e A' B _ (𝟙 _) = e A B _ (𝟙 _) ≫ (G.map a).app B
    rw [← ha A A' B _ a (𝟙 _), Category.comp_id,
      ← ht A B _ _ (𝟙 _) ((G.map a).app B), Category.id_comp]

private noncomputable def projectionOfInternalHom
    {C D : Type*} [Category* C] [Category* D]
    (E : C ⥤ D) (r : D ⥤ C) (R : C ⥤ D)
    (a : E ⊣ r) (b : r ⊣ R)
    (F : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (c : F ⊣₂ H)
    (G : D ⥤ D ⥤ D) (I : Dᵒᵖ ⥤ D ⥤ D) (d : G ⊣₂ I)
    (o : ∀ M T, (I.obj (Opposite.op (E.obj M))).obj T ≅
      R.obj ((H.obj (Opposite.op M)).obj (r.obj T)))
    (ho : ∀ M M' T T' (m : M' ⟶ M) (t : T ⟶ T'),
      ((I.map (E.map m).op).app T ≫
        (I.obj (Opposite.op (E.obj M'))).map t) ≫ (o M' T').hom =
      (o M T).hom ≫ R.map ((H.map m.op).app (r.obj T) ≫
        (H.obj (Opposite.op M')).map (r.map t))) :
    (((Functor.whiskeringLeft₂ _).obj E).obj (𝟭 D)).obj G ≅
      (Functor.postcompose₂.obj E).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 C)).obj r).obj F) := by
  let e : ∀ M N T, (E.obj ((F.obj M).obj (r.obj N)) ⟶ T) ≃
      ((G.obj (E.obj M)).obj N ⟶ T) := fun M N T ↦
    ((a.homEquiv _ _).trans c.homEquiv).trans
      ((b.homEquiv _ _).trans
        ((Iso.homCongr (Iso.refl _) (o M T).symm).trans d.homEquiv.symm))
  refine bifunctorIsoOfHomEquiv _ _ e ?_ ?_ ?_
  · intro M N T T' x t
    dsimp [e]
    simp only [a.homEquiv_naturality_right, c.homEquiv_naturality_three,
      b.homEquiv_naturality_right, Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Category.id_comp]
    have hot := ho M M T T' (𝟙 M) t
    simp only [E.map_id M, op_id, I.map_id _, H.map_id _,
      NatTrans.id_app, Category.id_comp] at hot
    have hi : R.map ((H.obj (Opposite.op M)).map (r.map t)) ≫ (o M T').inv =
        (o M T).inv ≫ (I.obj (Opposite.op (E.obj M))).map t := by
      apply (cancel_mono (o M T').hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hot,
        Iso.inv_hom_id_assoc]
    rw [Category.assoc, hi, ← Category.assoc, d.homEquiv_symm_naturality_three]
  · intro M M' N T m x
    dsimp [e]
    simp only [a.homEquiv_naturality_left, c.homEquiv_naturality_one,
      b.homEquiv_naturality_right, Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Category.id_comp]
    have hom := ho M' M T T m (𝟙 T)
    simp only [(I.obj _).map_id T, r.map_id T, (H.obj _).map_id _,
      Category.comp_id] at hom
    have hi : R.map ((H.map m.op).app (r.obj T)) ≫ (o M T).inv =
        (o M' T).inv ≫ (I.map (E.map m).op).app T := by
      apply (cancel_mono (o M T).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hom,
        Iso.inv_hom_id_assoc]
    rw [Category.assoc, hi, ← Category.assoc, d.homEquiv_symm_naturality_one]
  · intro M N N' T n x
    dsimp [e]
    simp only [a.homEquiv_naturality_left, c.homEquiv_naturality_two,
      b.homEquiv_naturality_left, Iso.homCongr_apply, Iso.refl_inv,
      Iso.symm_hom, Category.id_comp, Category.assoc,
      d.homEquiv_symm_naturality_two]

/-- The open immersion case of the relative derived projection formula.
Source: `det-lem-int-tensor-projection.proof.md`, open immersions and Derived version
(blueprint: lem-sfb-open-immersion-derived-tensor-projection).

Proof: choose the reduced closed complement of the open image using its vanishing
ideal. The ambient scheme X is Noetherian, since it is quasi-compact and locally of finite type
over a field, so the open immersion is quasi-compact. Apply
`openClosedInternalHomFormulas` to this complementary pair. Write E for extension by
zero, r for supportPullback on derived categories and R for derived direct image.
For arbitrary M,N,T the existing adjunctions and the open internal-Hom isomorphism give

Hom(E(M tensor rN), T) = Hom(M tensor rN, rT)
  = Hom(rN, RHom(M,rT)) = Hom(N, R RHom(M,rT))
  = Hom(N, RHom(EM,T)) = Hom(EM tensor N,T).

Every equality here is an equivalence of Hom sets. Naturality in T follows from the
ordinary adjunction naturality and the covariant naturality of the open Hom formula;
naturality in M follows from the parametrized tensor--Hom adjunction and its
contravariant naturality; naturality in N is the ordinary left-variable adjunction
naturality. Yoneda therefore gives an isomorphism natural in M and N. Finally transport
r to the specified upperStar using supportPullbackIsoUpperStar and
mapDerivedCategoryNatIso. No finiteness of the complexes or Tor-amplitude is used.
Empty source or target and zero coefficients are included: the adjunctions and Yoneda
argument remain valid in the zero categories. -/
theorem openImmersionTensorProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {S X : Scheme.{u}}
    [S.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of k))]
    [IsOpenImmersion f] :
    Nonempty (
      (((Functor.whiskeringLeft₂ _).obj
          (openImmersionLowerShriek Λ f).mapDerivedCategory).obj (𝟭 _)).obj
        (derivedTensor Λ X) ≅
      (Functor.postcompose₂.obj
        (openImmersionLowerShriek Λ f).mapDerivedCategory).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
          ((f)^*⟦Λ⟧.mapDerivedCategory)).obj (derivedTensor Λ S))) := by
  let Z : TopologicalSpace.Closeds X :=
    ⟨(Set.range f.base)ᶜ, f.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  let i := J.subschemeι
  have hij : Set.range i.base = (Set.range f.base)ᶜ := by
    change Set.range J.subschemeι = _
    rw [J.range_subschemeι]
    simp [J, Z]
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact f := inferInstance
  obtain ⟨_, o, _, _, _, _, ho, _⟩ := openClosedInternalHomFormulas Λ i f hij
  let e := projectionOfInternalHom
    (openImmersionLowerShriek Λ f).mapDerivedCategory
    (supportPullback Λ f).mapDerivedCategory (lowerStar Λ f).rightDerivedFunctor
    (openSupportDerivedAdjunction Λ f) (closedSupportOpenDerivedAdjunction Λ f)
    (derivedTensor Λ S) (derivedHom Λ S) (derivedTensorHomAdjunction₂ Λ S)
    (derivedTensor Λ X) (derivedHom Λ X) (derivedTensorHomAdjunction₂ Λ X) o ho
  let er := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ f)
  exact ⟨e ≪≫ (Functor.postcompose₂.obj
    (openImmersionLowerShriek Λ f).mapDerivedCategory).mapIso
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).mapIso er).app (derivedTensor Λ S))⟩

end AlgebraicGeometry.ProEtale.CondensedRing
