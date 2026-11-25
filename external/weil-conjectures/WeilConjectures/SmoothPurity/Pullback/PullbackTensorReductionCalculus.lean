/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Reduction calculations for pullback tensor comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Functor
namespace WeilConjectures

/-- Faithful reduction detects naturality of a normalized tensor comparison.
Source: naturality and cancellation in the parent pullback tensor reduction square.
(blueprint: lem-pur-reduced-pullback-tensor-naturality).
Proof: The tensor and pullback reduction isomorphisms give natural isomorphisms
from the two reduced composite functors to the same system functor. The prescribed
component equation identifies the reduced comparison with their quotient. That
quotient is natural, and faithfulness of reduction reflects its naturality. -/
theorem reducedComparison_natural
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (Q : C ⥤ S) (R : D ⥤ T) [R.Faithful]
    (F : C ⥤ D) (H : S ⥤ T) (U : C × C ⥤ C) (V : D × D ⥤ D)
    (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ Q ≅ (Q.prod Q) ⋙ J) (b : V ⋙ R ≅ (R.prod R) ⋙ I)
    (c : F ⋙ R ≅ Q ⋙ H) (μ : J ⋙ H ≅ (H.prod H) ⋙ I)
    (ν : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hc : ∀ M N, R.map (ν M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
        I.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) =
      c.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        μ.hom.app (Q.obj M, Q.obj N))
    {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N') :
    F.map (U.map (Prod.mkHom f g)) ≫ (ν M' N').hom =
      (ν M N).hom ≫ V.map (Prod.mkHom (F.map f) (F.map g)) := by
  let p : (F.prod F) ⋙ V ⋙ R ≅ (Q.prod Q) ⋙ (H.prod H) ⋙ I :=
    isoWhiskerLeft (F.prod F) b ≪≫ isoWhiskerRight (NatIso.prod c c) I
  let q : U ⋙ F ⋙ R ≅ (Q.prod Q) ⋙ (H.prod H) ⋙ I :=
    isoWhiskerLeft U c ≪≫ isoWhiskerRight a H ≪≫
      isoWhiskerLeft (Q.prod Q) μ
  have h (A B) : R.map (ν A B).hom ≫ p.hom.app (A, B) = q.hom.app (A, B) := by
    simpa only [p, q, Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app,
      whiskerRight_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, NatIso.prod_hom,
      NatTrans.prod, Functor.prod_obj, Functor.comp_obj, Category.assoc] using hc A B
  have hp := p.hom.naturality (Prod.mkHom f g)
  have hq := q.hom.naturality (Prod.mkHom f g)
  apply R.map_injective
  apply (cancel_mono (p.hom.app (M', N'))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [h]
  change R.map (F.map (U.map (Prod.mkHom f g))) ≫ q.hom.app (M', N') =
    R.map (ν M N).hom ≫ R.map (V.map (Prod.mkHom (F.map f) (F.map g))) ≫
      p.hom.app (M', N')
  change R.map (V.map (Prod.mkHom (F.map f) (F.map g))) ≫ p.hom.app (M', N') =
    p.hom.app (M, N) ≫ I.map (Prod.mkHom (H.map (Q.map f)) (H.map (Q.map g))) at hp
  rw [hp, ← Category.assoc, h]
  exact hq

private theorem cached_map_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A' B'
  cases h
  rfl

private theorem cached_bimap_heq {C D : Type*} [Category* C] [Category* D]
    (F : C × C ⥤ D) {A B C₀ D₀ A' B' C₀' D₀' : C}
    (hA : A = A') (hB : B = B') (hC : C₀ = C₀') (hD : D₀ = D₀')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : C₀ ⟶ D₀} {g' : C₀' ⟶ D₀'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (F.map (Prod.mkHom f g)) (F.map (Prod.mkHom f' g')) := by
  subst A' B' C₀' D₀'
  cases hf
  cases hg
  rfl

private theorem cached_id_heq {C : Type*} [Category* C] {A B : C} (h : A = B) :
    HEq (𝟙 A) (𝟙 B) := by
  subst B
  rfl

private theorem representative_associativity
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (μ : ∀ M N, F.obj (T.obj (M, N)) ≅ S.obj (F.obj M, F.obj N))
    (hn : ∀ {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (T.map (Prod.mkHom f g)) ≫ (μ M' N').hom =
        (μ M N).hom ≫ S.map (Prod.mkHom (F.map f) (F.map g)))
    (α : ∀ M N P, T.obj (T.obj (M, N), P) ≅ T.obj (M, T.obj (N, P)))
    (β : ∀ M N P, S.obj (S.obj (M, N), P) ≅ S.obj (M, S.obj (N, P)))
    (hc : ∀ M N P, F.map (α M N P).hom ≫ (μ M (T.obj (N, P))).hom ≫
        S.map (Prod.mkHom (𝟙 _) (μ N P).hom) =
      (μ (T.obj (M, N)) P).hom ≫ S.map (Prod.mkHom (μ M N).hom (𝟙 _)) ≫
        (β (F.obj M) (F.obj N) (F.obj P)).hom)
    (hβ : ∀ {M M' N N' P P' : D} (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P'),
      S.map (Prod.mkHom (S.map (Prod.mkHom f g)) h) ≫ (β M' N' P').hom =
        (β M N P).hom ≫ S.map (Prod.mkHom f (S.map (Prod.mkHom g h))))
    (M N P A B C₀ D₀ : C)
    (U V P₁ P₂ P₃ W Z X Y T₀ S₀ L₀ R₀ : D)
    (i : A ≅ T.obj (M, N)) (j : B ≅ T.obj (N, P))
    (c : C₀ ≅ T.obj (A, P)) (d : D₀ ≅ T.obj (M, B))
    (u : U ≅ F.obj C₀) (v : V ≅ F.obj D₀)
    (p : P₁ ≅ F.obj M) (q : P₂ ≅ F.obj N) (r : P₃ ≅ F.obj P)
    (w : W ≅ F.obj A) (z : Z ≅ F.obj B)
    (x : X ≅ S.obj (P₁, P₂)) (y : Y ≅ S.obj (P₂, P₃))
    (t : T₀ ≅ S.obj (W, P₃)) (s : S₀ ≅ S.obj (P₁, Z))
    (a : L₀ ≅ S.obj (X, P₃)) (b : R₀ ≅ S.obj (P₁, Y)) :
    ((u.hom ≫ F.map ((c.hom ≫ T.map (Prod.mkHom i.hom (𝟙 P))) ≫
        (α M N P).hom ≫ T.map (Prod.mkHom (𝟙 M) j.inv) ≫ d.inv) ≫ v.inv) ≫
      (v.hom ≫ F.map d.hom ≫ (μ M B).hom ≫
        S.map (Prod.mkHom p.inv z.inv) ≫ s.inv)) ≫
      (s.hom ≫ S.map (Prod.mkHom (𝟙 P₁)
        (z.hom ≫ F.map j.hom ≫ (μ N P).hom ≫
          S.map (Prod.mkHom q.inv r.inv) ≫ y.inv)) ≫ b.inv) =
    ((u.hom ≫ F.map c.hom ≫ (μ A P).hom ≫
        S.map (Prod.mkHom w.inv r.inv) ≫ t.inv) ≫
      (t.hom ≫ S.map (Prod.mkHom
        (w.hom ≫ F.map i.hom ≫ (μ M N).hom ≫
          S.map (Prod.mkHom p.inv q.inv) ≫ x.inv) (𝟙 P₃)) ≫ a.inv)) ≫
      ((a.hom ≫ S.map (Prod.mkHom x.hom (𝟙 P₃))) ≫ (β P₁ P₂ P₃).hom ≫
        S.map (Prod.mkHom (𝟙 P₁) y.inv) ≫ b.inv) := by
  have hl : S.map (Prod.mkHom (𝟙 (F.obj M)) (F.map j.inv)) ≫
      S.map (Prod.mkHom p.inv z.inv) ≫
      S.map (Prod.mkHom (𝟙 P₁) (z.hom ≫ F.map j.hom ≫ (μ N P).hom ≫
        S.map (Prod.mkHom q.inv r.inv) ≫ y.inv)) =
    S.map (Prod.mkHom (𝟙 (F.obj M)) (μ N P).hom) ≫
      S.map (Prod.mkHom p.inv (S.map (Prod.mkHom q.inv r.inv))) ≫
      S.map (Prod.mkHom (𝟙 P₁) y.inv) := by
    simp only [← S.map_comp, prod_comp, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id_map_assoc, Category.id_comp, Category.comp_id]
  have hr : S.map (Prod.mkHom w.inv r.inv) ≫
      S.map (Prod.mkHom (w.hom ≫ F.map i.hom ≫ (μ M N).hom ≫
        S.map (Prod.mkHom p.inv q.inv) ≫ x.inv) (𝟙 P₃)) ≫
      S.map (Prod.mkHom x.hom (𝟙 P₃)) =
    S.map (Prod.mkHom (F.map i.hom) (𝟙 (F.obj P))) ≫
      S.map (Prod.mkHom (μ M N).hom (𝟙 (F.obj P))) ≫
      S.map (Prod.mkHom (S.map (Prod.mkHom p.inv q.inv)) r.inv) := by
    simp only [← S.map_comp, prod_comp, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  have hj : F.map (T.map (Prod.mkHom (𝟙 M) j.inv)) ≫ (μ M B).hom =
      (μ M (T.obj (N, P))).hom ≫
        S.map (Prod.mkHom (𝟙 (F.obj M)) (F.map j.inv)) := by
    simpa only [Functor.map_id] using hn (𝟙 M) j.inv
  have hi : F.map (T.map (Prod.mkHom i.hom (𝟙 P))) ≫ (μ (T.obj (M, N)) P).hom =
      (μ A P).hom ≫ S.map (Prod.mkHom (F.map i.hom) (𝟙 (F.obj P))) := by
    simpa only [Functor.map_id] using hn i.hom (𝟙 P)
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_map_assoc]
  rw [reassoc_of% hj, reassoc_of% hl, reassoc_of% hr, ← reassoc_of% hi,
    reassoc_of% (hc M N P), ← reassoc_of% (hβ p.inv q.inv r.inv)]

section ReductionCalculus
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem reduction_comparison
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (L : S ⥤ C) (A : R ⊣ L)
    (Q : D ⥤ T) (K : T ⥤ D) (B : Q ⊣ K)
    (F : D ⥤ C) (H : T ⥤ S) (U : D × D ⥤ D) (V : C × C ⥤ C)
    (J : T × T ⥤ T) (I : S × S ⥤ S)
    (a : F ≅ Q ⋙ H ⋙ L) (b : U ≅ (Q.prod Q) ⋙ J ⋙ K)
    (c : V ≅ (R.prod R) ⋙ I ⋙ L)
    (μ : J ⋙ H ≅ (H.prod H) ⋙ I) (M N : D)
    [IsIso (B.counit.app (J.obj (Q.obj M, Q.obj N)))]
    [IsIso (A.counit.app (H.obj (Q.obj M)))]
    [IsIso (A.counit.app (H.obj (Q.obj N)))] :
    R.map (a.hom.app (U.obj (M, N)) ≫
      L.map (H.map (Q.map (b.hom.app (M, N)))) ≫
      L.map (H.map (B.counit.app (J.obj (Q.obj M, Q.obj N)))) ≫
      L.map (μ.hom.app (Q.obj M, Q.obj N)) ≫
      L.map (I.map (Prod.mkHom (inv (A.counit.app (H.obj (Q.obj M))))
        (inv (A.counit.app (H.obj (Q.obj N)))))) ≫
      L.map (I.map (Prod.mkHom (R.map (a.inv.app M)) (R.map (a.inv.app N)))) ≫
      c.inv.app (F.obj M, F.obj N)) ≫
      R.map (c.hom.app (F.obj M, F.obj N)) ≫
      A.counit.app (I.obj (R.obj (F.obj M), R.obj (F.obj N))) ≫
      I.map (Prod.mkHom (R.map (a.hom.app M) ≫ A.counit.app (H.obj (Q.obj M)))
        (R.map (a.hom.app N) ≫ A.counit.app (H.obj (Q.obj N)))) =
    R.map (a.hom.app (U.obj (M, N))) ≫
      A.counit.app (H.obj (Q.obj (U.obj (M, N)))) ≫
      H.map (Q.map (b.hom.app (M, N))) ≫
      H.map (B.counit.app (J.obj (Q.obj M, Q.obj N))) ≫
      μ.hom.app (Q.obj M, Q.obj N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (c.inv.app _) (c.hom.app _), c.inv_hom_id_app, R.map_id, Category.id_comp]
  simp only [A.counit_naturality_assoc]
  simp only [← I.map_comp, CategoryTheory.prod_comp, ← R.map_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  erw [R.map_id, R.map_id]
  simp only [Category.id_comp, IsIso.inv_hom_id]
  erw [← prod_id, I.map_id, Category.comp_id]

private theorem counit_model_naturality
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (R : D ⥤ T) (L : T ⥤ D) (adj : R ⊣ L) (F : C ⥤ D) (H : C ⥤ T)
    (a : F ≅ H ⋙ L) {M N : C} (f : M ⟶ N) :
    R.map (F.map f) ≫ R.map (a.hom.app N) ≫ adj.counit.app (H.obj N) =
      R.map (a.hom.app M) ≫ adj.counit.app (H.obj M) ≫ H.map f := by
  rw [← R.map_comp_assoc, a.hom.naturality, R.map_comp]
  simp only [Functor.comp_map, Category.assoc]
  exact congrArg (fun k ↦ R.map (a.hom.app M) ≫ k)
    (adj.counit.naturality (H.map f))

private theorem reduced_braiding
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : ∀ M N, R.obj (U.obj (M, N)) ≅ J.obj (R.obj M, R.obj N))
    (b : ∀ M N, Q.obj (V.obj (M, N)) ≅ I.obj (Q.obj M, Q.obj N))
    (p : F ⋙ Q ≅ R ⋙ H)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : ∀ M N, H.obj (J.obj (M, N)) ≅ I.obj (H.obj M, H.obj N))
    (βC : ∀ M N, U.obj (M, N) ≅ U.obj (N, M))
    (βD : ∀ M N, V.obj (M, N) ≅ V.obj (N, M))
    (βS : ∀ M N, J.obj (M, N) ≅ J.obj (N, M))
    (βT : I ≅ CategoryTheory.Prod.swap T T ⋙ I)
    (hC : ∀ M N, R.map (βC M N).hom ≫ (a N M).hom =
      (a M N).hom ≫ (βS (R.obj M) (R.obj N)).hom)
    (hD : ∀ M N, Q.map (βD M N).hom ≫ (b N M).hom =
      (b M N).hom ≫ βT.hom.app (Q.obj M, Q.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ (b (F.obj M) (F.obj N)).hom ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a M N).hom ≫ (ν (R.obj M) (R.obj N)).hom)
    (hν : ∀ M N, H.map (βS M N).hom ≫ (ν N M).hom =
      (ν M N).hom ≫ βT.hom.app (H.obj M, H.obj N)) (M N : C) :
    F.map (βC M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (βD (F.obj M) (F.obj N)).hom := by
  apply Q.map_injective
  let d := b (F.obj N) (F.obj M) ≪≫ I.mapIso (Iso.prod (p.app N) (p.app M))
  apply (cancel_mono d.hom).1
  change _ ≫ ((b (F.obj N) (F.obj M)).hom ≫
    I.map (Prod.mkHom (p.hom.app N) (p.hom.app M))) =
    _ ≫ ((b (F.obj N) (F.obj M)).hom ≫
    I.map (Prod.mkHom (p.hom.app N) (p.hom.app M)))
  simp only [Functor.map_comp, Category.assoc]
  rw [hμ]
  have hp := p.hom.naturality (βC M N).hom
  change Q.map (F.map _) ≫ p.hom.app _ = p.hom.app _ ≫ H.map (R.map _) at hp
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hC, H.map_comp]
  simp only [Category.assoc]
  rw [hν]
  rw [← Category.assoc (Q.map (βD (F.obj M) (F.obj N)).hom), hD]
  simp only [Category.assoc]
  have hn := βT.hom.naturality (Prod.mkHom (p.hom.app M) (p.hom.app N))
  change I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) ≫ _ =
    _ ≫ I.map (Prod.mkHom (p.hom.app N) (p.hom.app M)) at hn
  dsimp only [Functor.comp_obj] at hn
  erw [← hn]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ βT.hom.app (H.obj (R.obj M), H.obj (R.obj N))) (hμ M N).symm

private theorem map_pair_comp
    {C D S : Type*} [Category* C] [Category* D] [Category* S]
    (I : C × D ⥤ S) {A B C' : C} {X Y Z : D}
    (f : A ⟶ B) (g : X ⟶ Y) (f' : B ⟶ C') (g' : Y ⟶ Z) :
    I.map (Prod.mkHom f g) ≫ I.map (Prod.mkHom f' g') =
      I.map (Prod.mkHom (f ≫ f') (g ≫ g')) := by
  rw [← I.map_comp]
  rfl

private theorem nested_right
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        ν.hom.app (R.obj M, R.obj N)) (M N P : C) :
    Q.map (μ M (U.obj (N, P))).hom ≫
      Q.map (V.map (Prod.mkHom (𝟙 _) (μ N P).hom)) ≫
      b.hom.app (F.obj M, V.obj (F.obj N, F.obj P)) ≫
      I.map (Prod.mkHom (p.hom.app M)
        (b.hom.app (F.obj N, F.obj P) ≫
          I.map (Prod.mkHom (p.hom.app N) (p.hom.app P)))) =
    p.hom.app (U.obj (M, U.obj (N, P))) ≫
      H.map (a.hom.app (M, U.obj (N, P))) ≫
      H.map (J.map (Prod.mkHom (𝟙 _) (a.hom.app (N, P)))) ≫
      ν.hom.app (R.obj M, J.obj (R.obj N, R.obj P)) ≫
      I.map (Prod.mkHom (𝟙 _) (ν.hom.app (R.obj N, R.obj P))) := by
  have hb := b.hom.naturality (Prod.mkHom (𝟙 (F.obj M)) (μ N P).hom)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at hb
  rw [← Category.assoc (Q.map (V.map _)), hb]
  simp only [Category.assoc]
  rw [map_pair_comp]
  erw [Q.map_id, Category.id_comp]
  rw [hμ]
  have hs := map_pair_comp I (p.hom.app M) (p.hom.app (U.obj (N, P)))
    (𝟙 _) (H.map (a.hom.app (N, P)) ≫ ν.hom.app (R.obj N, R.obj P))
  simp only [Category.comp_id] at hs
  rw [← hs]
  rw [reassoc_of% hμ]
  have hs' := map_pair_comp I (𝟙 (H.obj (R.obj M))) (H.map (a.hom.app (N, P)))
    (𝟙 _) (ν.hom.app (R.obj N, R.obj P))
  simp only [Category.id_comp] at hs'
  erw [← hs']
  have hn := ν.hom.naturality
    (Prod.mkHom (𝟙 (R.obj M)) (a.hom.app (N, P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [H.map_id] at hn
  erw [← reassoc_of% hn]
  rfl

private theorem nested_left
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        ν.hom.app (R.obj M, R.obj N)) (M N P : C) :
    Q.map (μ (U.obj (M, N)) P).hom ≫
      Q.map (V.map (Prod.mkHom (μ M N).hom (𝟙 _))) ≫
      b.hom.app (V.obj (F.obj M, F.obj N), F.obj P) ≫
      I.map (Prod.mkHom
        (b.hom.app (F.obj M, F.obj N) ≫
          I.map (Prod.mkHom (p.hom.app M) (p.hom.app N))) (p.hom.app P)) =
    p.hom.app (U.obj (U.obj (M, N), P)) ≫
      H.map (a.hom.app (U.obj (M, N), P)) ≫
      H.map (J.map (Prod.mkHom (a.hom.app (M, N)) (𝟙 _))) ≫
      ν.hom.app (J.obj (R.obj M, R.obj N), R.obj P) ≫
      I.map (Prod.mkHom (ν.hom.app (R.obj M, R.obj N)) (𝟙 _)) := by
  have hb := b.hom.naturality (Prod.mkHom (μ M N).hom (𝟙 (F.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at hb
  rw [← Category.assoc (Q.map (V.map _)), hb]
  simp only [Category.assoc]
  rw [map_pair_comp]
  erw [Q.map_id, Category.id_comp]
  rw [hμ]
  have hs := map_pair_comp I (p.hom.app (U.obj (M, N))) (p.hom.app P)
    (H.map (a.hom.app (M, N)) ≫ ν.hom.app (R.obj M, R.obj N)) (𝟙 _)
  simp only [Category.comp_id] at hs
  rw [← hs]
  rw [reassoc_of% hμ]
  have hs' := map_pair_comp I (H.map (a.hom.app (M, N))) (𝟙 (H.obj (R.obj P)))
    (ν.hom.app (R.obj M, R.obj N)) (𝟙 _)
  simp only [Category.id_comp] at hs'
  erw [← hs']
  have hn := ν.hom.naturality
    (Prod.mkHom (a.hom.app (M, N)) (𝟙 (R.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [H.map_id] at hn
  erw [← reassoc_of% hn]
  rfl

private theorem transport_associator
    {C T : Type*} [Category* C] [Category* T]
    (Q : C ⥤ T) (V : C × C ⥤ C) (I : T × T ⥤ T)
    (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (αC : ∀ M N P, V.obj (V.obj (M, N), P) ≅ V.obj (M, V.obj (N, P)))
    (αT : ∀ M N P, I.obj (I.obj (M, N), P) ≅ I.obj (M, I.obj (N, P)))
    (hn : ∀ {M N P M' N' P' : T} (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P'),
      I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h) ≫ (αT M' N' P').hom =
        (αT M N P).hom ≫ I.map (Prod.mkHom f (I.map (Prod.mkHom g h))))
    (hc : ∀ M N P, Q.map (αC M N P).hom ≫ b.hom.app (M, V.obj (N, P)) ≫
      I.map (Prod.mkHom (𝟙 _) (b.hom.app (N, P))) =
        b.hom.app (V.obj (M, N), P) ≫
          I.map (Prod.mkHom (b.hom.app (M, N)) (𝟙 _)) ≫
          (αT (Q.obj M) (Q.obj N) (Q.obj P)).hom)
    (M N P : C) {M' N' P' : T}
    (pM : Q.obj M ≅ M') (pN : Q.obj N ≅ N') (pP : Q.obj P ≅ P') :
    Q.map (αC M N P).hom ≫ b.hom.app (M, V.obj (N, P)) ≫
      I.map (Prod.mkHom pM.hom
        (b.hom.app (N, P) ≫ I.map (Prod.mkHom pN.hom pP.hom))) =
    b.hom.app (V.obj (M, N), P) ≫
      I.map (Prod.mkHom
        (b.hom.app (M, N) ≫ I.map (Prod.mkHom pM.hom pN.hom)) pP.hom) ≫
          (αT M' N' P').hom := by
  have hr := map_pair_comp I (𝟙 (Q.obj M)) (b.hom.app (N, P))
    pM.hom (I.map (Prod.mkHom pN.hom pP.hom))
  simp only [Category.id_comp] at hr
  rw [← hr]
  have hc' := hc M N P
  rw [← Category.assoc] at hc'
  rw [reassoc_of% hc']
  have hl := map_pair_comp I (b.hom.app (M, N)) (𝟙 (Q.obj P))
    (I.map (Prod.mkHom pM.hom pN.hom)) pP.hom
  simp only [Category.id_comp] at hl
  rw [← hl]
  simp only [Category.assoc]
  rw [hn]

private theorem reduced_square
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (p : F ⋙ Q ≅ R ⋙ H)
    {A B : C} {A' B' : D} {U V : S} {U' V' : T}
    (a : R.obj A ≅ U) (b : R.obj B ≅ V)
    (rA : Q.obj A' ≅ U') (rB : Q.obj B' ≅ V')
    (α : A ≅ B) (β : A' ≅ B') (γ : U ≅ V) (δ : U' ≅ V')
    (μA : F.obj A ≅ A') (μB : F.obj B ≅ B')
    (νA : H.obj U ≅ U') (νB : H.obj V ≅ V')
    (hα : R.map α.hom ≫ b.hom = a.hom ≫ γ.hom)
    (hβ : Q.map β.hom ≫ rB.hom = rA.hom ≫ δ.hom)
    (hμA : Q.map μA.hom ≫ rA.hom = p.hom.app A ≫ H.map a.hom ≫ νA.hom)
    (hμB : Q.map μB.hom ≫ rB.hom = p.hom.app B ≫ H.map b.hom ≫ νB.hom)
    (hν : H.map γ.hom ≫ νB.hom = νA.hom ≫ δ.hom) :
    F.map α.hom ≫ μB.hom = μA.hom ≫ β.hom := by
  apply Q.map_injective
  apply (cancel_mono rB.hom).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hμB]
  have hn := p.hom.naturality α.hom
  change Q.map (F.map α.hom) ≫ p.hom.app B = p.hom.app A ≫ H.map (R.map α.hom) at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hα, H.map_comp]
  simp only [Category.assoc]
  rw [hν, hβ]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ δ.hom) hμA.symm

private theorem reduced_associativity
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (αC : ∀ M N P, U.obj (U.obj (M, N), P) ≅ U.obj (M, U.obj (N, P)))
    (αD : ∀ M N P, V.obj (V.obj (M, N), P) ≅ V.obj (M, V.obj (N, P)))
    (αS : ∀ M N P, J.obj (J.obj (M, N), P) ≅ J.obj (M, J.obj (N, P)))
    (αT : ∀ M N P, I.obj (I.obj (M, N), P) ≅ I.obj (M, I.obj (N, P)))
    (hn : ∀ {M N P M' N' P' : T} (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P'),
      I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h) ≫ (αT M' N' P').hom =
        (αT M N P).hom ≫ I.map (Prod.mkHom f (I.map (Prod.mkHom g h))))
    (hC : ∀ M N P, R.map (αC M N P).hom ≫ a.hom.app (M, U.obj (N, P)) ≫
      J.map (Prod.mkHom (𝟙 _) (a.hom.app (N, P))) =
        a.hom.app (U.obj (M, N), P) ≫
          J.map (Prod.mkHom (a.hom.app (M, N)) (𝟙 _)) ≫
          (αS (R.obj M) (R.obj N) (R.obj P)).hom)
    (hD : ∀ M N P, Q.map (αD M N P).hom ≫ b.hom.app (M, V.obj (N, P)) ≫
      I.map (Prod.mkHom (𝟙 _) (b.hom.app (N, P))) =
        b.hom.app (V.obj (M, N), P) ≫
          I.map (Prod.mkHom (b.hom.app (M, N)) (𝟙 _)) ≫
          (αT (Q.obj M) (Q.obj N) (Q.obj P)).hom)
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        ν.hom.app (R.obj M, R.obj N))
    (hν : ∀ M N P, H.map (αS M N P).hom ≫
      ν.hom.app (M, J.obj (N, P)) ≫
        I.map (Prod.mkHom (𝟙 _) (ν.hom.app (N, P))) =
      ν.hom.app (J.obj (M, N), P) ≫
        I.map (Prod.mkHom (ν.hom.app (M, N)) (𝟙 _)) ≫
          (αT (H.obj M) (H.obj N) (H.obj P)).hom) (M N P : C) :
    F.map (αC M N P).hom ≫ (μ M (U.obj (N, P))).hom ≫
      V.map (Prod.mkHom (𝟙 _) (μ N P).hom) =
    (μ (U.obj (M, N)) P).hom ≫
      V.map (Prod.mkHom (μ M N).hom (𝟙 _)) ≫
        (αD (F.obj M) (F.obj N) (F.obj P)).hom := by
  let aL := a.app (U.obj (M, N), P) ≪≫
    J.mapIso (Iso.prod (a.app (M, N)) (Iso.refl _))
  let aR := a.app (M, U.obj (N, P)) ≪≫
    J.mapIso (Iso.prod (Iso.refl _) (a.app (N, P)))
  let bL := b.app (V.obj (F.obj M, F.obj N), F.obj P) ≪≫
    I.mapIso (Iso.prod
      (b.app (F.obj M, F.obj N) ≪≫ I.mapIso (Iso.prod (p.app M) (p.app N))) (p.app P))
  let bR := b.app (F.obj M, V.obj (F.obj N, F.obj P)) ≪≫
    I.mapIso (Iso.prod (p.app M)
      (b.app (F.obj N, F.obj P) ≪≫ I.mapIso (Iso.prod (p.app N) (p.app P))))
  let μL := μ (U.obj (M, N)) P ≪≫
    V.mapIso (Iso.prod (μ M N) (Iso.refl _))
  let μR := μ M (U.obj (N, P)) ≪≫
    V.mapIso (Iso.prod (Iso.refl _) (μ N P))
  let νL := ν.app (J.obj (R.obj M, R.obj N), R.obj P) ≪≫
    I.mapIso (Iso.prod (ν.app (R.obj M, R.obj N)) (Iso.refl _))
  let νR := ν.app (R.obj M, J.obj (R.obj N, R.obj P)) ≪≫
    I.mapIso (Iso.prod (Iso.refl _) (ν.app (R.obj N, R.obj P)))
  have he := reduced_square R Q F H p aL aR bL bR
    (αC M N P) (αD (F.obj M) (F.obj N) (F.obj P))
    (αS (R.obj M) (R.obj N) (R.obj P))
    (αT (H.obj (R.obj M)) (H.obj (R.obj N)) (H.obj (R.obj P))) μL μR νL νR
  suffices hh : F.map (αC M N P).hom ≫ μR.hom =
      μL.hom ≫ (αD (F.obj M) (F.obj N) (F.obj P)).hom by
    simpa only [μL, μR, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Category.assoc] using hh
  apply he
  · simpa only [aR, aL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Iso.app_hom, Category.assoc] using hC M N P
  · simpa only [bR, bL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.app_hom, Functor.comp_obj, Category.assoc] using
      transport_associator Q V I b αD αT hn hD _ _ _ (p.app M) (p.app N) (p.app P)
  · simpa only [μL, bL, aL, νL, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Functor.map_comp, Category.assoc] using
        nested_left R Q F H U V J I a b p ν μ hμ M N P
  · simpa only [μR, bR, aR, νR, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Functor.map_comp, Category.assoc] using
        nested_right R Q F H U V J I a b p ν μ hμ M N P
  · simpa only [νR, νL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Iso.app_hom, Category.assoc] using hν (R.obj M) (R.obj N) (R.obj P)

end ReductionCalculus

end WeilConjectures
