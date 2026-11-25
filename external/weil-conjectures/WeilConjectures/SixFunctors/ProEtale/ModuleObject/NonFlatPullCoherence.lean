/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube

/-!
# Coherence of the derived (Pull) isomorphism for an arbitrary coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat. This file
reduces the coherence of the derived (Pull) isomorphisms
`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a` with the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (the hypothesis
`ProEtale.CondensedRing.DerivedUpperStarExtendScalarsIsoCompCoherenceAt` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube`) to the compatibility of
`derivedUpperStarExtendScalarsIso a h` with the counits of the left derived functors on K-flat
complexes (`ProEtale.CondensedRing.DerivedUpperStarExtendScalarsIsoFac`).

* `CategoryTheory.Adjunction.comp_coherence_app_of_isIso_left`: a diagram chase deducing a
  coherence of "derived" isomorphisms of left derived functors from its "underived" analogue,
  dual to `CategoryTheory.Adjunction.comp_coherence_app_of_isIso`.
* `ProEtale.CondensedRing.pullIso_hom_app_comp`: the underived (Pull) isomorphisms are compatible
  with the composition isomorphisms of pullbacks, being conjugates of `comapLowerStarIso`; the
  same holds on the homotopy categories
  (`ProEtale.CondensedRing.pullIsoHomotopy_upperStarCompHomotopy`, via
  `CategoryTheory.Functor.mapHomotopyCategoryCommIsoHom_app_comp`).
* `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoCompCoherenceAt_of_fac`: the
  reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C_X C_Y C_Z C'_X C'_Y C'_Z D_X D_Y D_Z D'_X D'_Y D'_Z : Type*}
  [Category* C_X] [Category* C_Y] [Category* C_Z] [Category* C'_X] [Category* C'_Y]
  [Category* C'_Z] [Category* D_X] [Category* D_Y] [Category* D_Z] [Category* D'_X]
  [Category* D'_Y] [Category* D'_Z]
  {Q_X : C_X ⥤ D_X} {Q_Y : C_Y ⥤ D_Y} {Q_Z : C_Z ⥤ D_Z}
  {Q'_X : C'_X ⥤ D'_X} {Q'_Y : C'_Y ⥤ D'_Y} {Q'_Z : C'_Z ⥤ D'_Z}
  {P_f : C_Y ⥤ C_X} {P_g : C_Z ⥤ C_Y} {P_fg : C_Z ⥤ C_X}
  {P'_f : C'_Y ⥤ C'_X} {P'_g : C'_Z ⥤ C'_Y} {P'_fg : C'_Z ⥤ C'_X}
  {R_f : D_Y ⥤ D_X} {R_g : D_Z ⥤ D_Y} {R_fg : D_Z ⥤ D_X}
  {R'_f : D'_Y ⥤ D'_X} {R'_g : D'_Z ⥤ D'_Y} {R'_fg : D'_Z ⥤ D'_X}
  {H_X : C_X ⥤ C'_X} {H_Y : C_Y ⥤ C'_Y} {H_Z : C_Z ⥤ C'_Z}
  {T_X : D_X ⥤ D'_X} {T_Y : D_Y ⥤ D'_Y} {T_Z : D_Z ⥤ D'_Z}

/-- A diagram chase: let `R`, `R'` be functors between "derived" categories, with comparisons
`α : Q ⋙ R ⟶ P ⋙ Q` to functors `P` between "homotopy" categories, and let `T`, `H` be functors
related by comparisons `φ : Q ⋙ T ⟶ H ⋙ Q'`. Let `E_f`, `E_g`, `E_fg : R ⋙ T ≅ T ⋙ R'` be
isomorphisms induced by maps `e : H ⋙ P ⟶ P' ⋙ H` through the `α` and `φ`, and `d`, `d'`
composition isomorphisms induced by `d_h`, `d'_h`. If the `e` are compatible with `d_h` and
`d'_h`, then the `E` are compatible with `d` and `d'` on the objects `Q K` for which the
composite `R'_f R'_g φ_Z ≫ R'_f α'_g ≫ α'_f` is an isomorphism. -/
lemma comp_coherence_app_Q_of_isIso_left
    (α_f : Q_Y ⋙ R_f ⟶ P_f ⋙ Q_X) (α_g : Q_Z ⋙ R_g ⟶ P_g ⋙ Q_Y)
    (α_fg : Q_Z ⋙ R_fg ⟶ P_fg ⋙ Q_X)
    (α'_f : Q'_Y ⋙ R'_f ⟶ P'_f ⋙ Q'_X) (α'_g : Q'_Z ⋙ R'_g ⟶ P'_g ⋙ Q'_Y)
    (α'_fg : Q'_Z ⋙ R'_fg ⟶ P'_fg ⋙ Q'_X)
    (φ_X : Q_X ⋙ T_X ⟶ H_X ⋙ Q'_X) (φ_Y : Q_Y ⋙ T_Y ⟶ H_Y ⋙ Q'_Y)
    (φ_Z : Q_Z ⋙ T_Z ⟶ H_Z ⋙ Q'_Z)
    (E_f : R_f ⋙ T_X ≅ T_Y ⋙ R'_f) (E_g : R_g ⋙ T_Y ≅ T_Z ⋙ R'_g)
    (E_fg : R_fg ⋙ T_X ≅ T_Z ⋙ R'_fg)
    (e_f : ∀ K, H_X.obj (P_f.obj K) ⟶ P'_f.obj (H_Y.obj K))
    (e_g : ∀ K, H_Y.obj (P_g.obj K) ⟶ P'_g.obj (H_Z.obj K))
    (e_fg : ∀ K, H_X.obj (P_fg.obj K) ⟶ P'_fg.obj (H_Z.obj K))
    (d : R_fg ⟶ R_g ⋙ R_f) (d' : R'_fg ⟶ R'_g ⋙ R'_f)
    (d_h : ∀ K, P_fg.obj K ⟶ P_f.obj (P_g.obj K))
    (d'_h : ∀ K, P'_fg.obj K ⟶ P'_f.obj (P'_g.obj K)) (K : C_Z)
    (hE_f : E_f.hom.app (Q_Y.obj (P_g.obj K)) ≫ R'_f.map (φ_Y.app (P_g.obj K)) ≫
        α'_f.app (H_Y.obj (P_g.obj K)) =
      T_X.map (α_f.app (P_g.obj K)) ≫ φ_X.app (P_f.obj (P_g.obj K)) ≫
        Q'_X.map (e_f (P_g.obj K)))
    (hE_g : E_g.hom.app (Q_Z.obj K) ≫ R'_g.map (φ_Z.app K) ≫ α'_g.app (H_Z.obj K) =
      T_Y.map (α_g.app K) ≫ φ_Y.app (P_g.obj K) ≫ Q'_Y.map (e_g K))
    (hE_fg : E_fg.hom.app (Q_Z.obj K) ≫ R'_fg.map (φ_Z.app K) ≫ α'_fg.app (H_Z.obj K) =
      T_X.map (α_fg.app K) ≫ φ_X.app (P_fg.obj K) ≫ Q'_X.map (e_fg K))
    (hd : d.app (Q_Z.obj K) ≫ R_f.map (α_g.app K) ≫ α_f.app (P_g.obj K) =
      α_fg.app K ≫ Q_X.map (d_h K))
    (hd' : d'.app (Q'_Z.obj (H_Z.obj K)) ≫ R'_f.map (α'_g.app (H_Z.obj K)) ≫
        α'_f.app (P'_g.obj (H_Z.obj K)) =
      α'_fg.app (H_Z.obj K) ≫ Q'_X.map (d'_h (H_Z.obj K)))
    (hH : e_fg K ≫ d'_h (H_Z.obj K) = H_X.map (d_h K) ≫ e_f (P_g.obj K) ≫ P'_f.map (e_g K))
    [IsIso (R'_f.map (R'_g.map (φ_Z.app K)) ≫ R'_f.map (α'_g.app (H_Z.obj K)) ≫
      α'_f.app (P'_g.obj (H_Z.obj K)))] :
    E_fg.hom.app (Q_Z.obj K) ≫ d'.app (T_Z.obj (Q_Z.obj K)) =
      T_X.map (d.app (Q_Z.obj K)) ≫ E_f.hom.app (R_g.obj (Q_Z.obj K)) ≫
        R'_f.map (E_g.hom.app (Q_Z.obj K)) := by
  rw [← cancel_mono (R'_f.map (R'_g.map (φ_Z.app K)) ≫ R'_f.map (α'_g.app (H_Z.obj K)) ≫
      α'_f.app (P'_g.obj (H_Z.obj K)))]
  have n₁ := d'.naturality (φ_Z.app K)
  have n₂ := α'_f.naturality (e_g K)
  have n₃ := E_f.hom.naturality (α_g.app K)
  have n₄ := φ_X.naturality (d_h K)
  dsimp at n₁ n₂ n₃ n₄
  have hg := congrArg R'_f.map hE_g
  have hd₂ := congrArg T_X.map hd
  simp only [Functor.map_comp] at hg hd₂
  have hL : (E_fg.hom.app (Q_Z.obj K) ≫ d'.app (T_Z.obj (Q_Z.obj K))) ≫
      R'_f.map (R'_g.map (φ_Z.app K)) ≫ R'_f.map (α'_g.app (H_Z.obj K)) ≫
        α'_f.app (P'_g.obj (H_Z.obj K)) =
      T_X.map (α_fg.app K) ≫ φ_X.app (P_fg.obj K) ≫
        Q'_X.map (e_fg K ≫ d'_h (H_Z.obj K)) := by
    rw [Category.assoc, ← reassoc_of% n₁]
    rw [hd']
    rw [reassoc_of% hE_fg, Q'_X.map_comp]
  have hR : (T_X.map (d.app (Q_Z.obj K)) ≫ E_f.hom.app (R_g.obj (Q_Z.obj K)) ≫
        R'_f.map (E_g.hom.app (Q_Z.obj K))) ≫
      R'_f.map (R'_g.map (φ_Z.app K)) ≫ R'_f.map (α'_g.app (H_Z.obj K)) ≫
        α'_f.app (P'_g.obj (H_Z.obj K)) =
      T_X.map (α_fg.app K) ≫ φ_X.app (P_fg.obj K) ≫
        Q'_X.map (H_X.map (d_h K) ≫ e_f (P_g.obj K) ≫ P'_f.map (e_g K)) := by
    simp only [Category.assoc]
    rw [reassoc_of% hg, n₂, ← reassoc_of% n₃, reassoc_of% hE_f, reassoc_of% hd₂,
      reassoc_of% n₄, Q'_X.map_comp, Q'_X.map_comp]
  rw [hL, hR, hH]

/-- The diagram chase `Adjunction.comp_coherence_app_Q_of_isIso_left`, on every object, provided
every object is isomorphic to some `Q K`, with `K` satisfying a property `W` on which the
compatibilities of the `E` hold, such that `R'_f R'_g φ_Z ≫ R'_f α'_g ≫ α'_f` is an
isomorphism at `K`. -/
lemma comp_coherence_app_of_isIso_left
    (α_f : Q_Y ⋙ R_f ⟶ P_f ⋙ Q_X) (α_g : Q_Z ⋙ R_g ⟶ P_g ⋙ Q_Y)
    (α_fg : Q_Z ⋙ R_fg ⟶ P_fg ⋙ Q_X)
    (α'_f : Q'_Y ⋙ R'_f ⟶ P'_f ⋙ Q'_X) (α'_g : Q'_Z ⋙ R'_g ⟶ P'_g ⋙ Q'_Y)
    (α'_fg : Q'_Z ⋙ R'_fg ⟶ P'_fg ⋙ Q'_X)
    (φ_X : Q_X ⋙ T_X ⟶ H_X ⋙ Q'_X) (φ_Y : Q_Y ⋙ T_Y ⟶ H_Y ⋙ Q'_Y)
    (φ_Z : Q_Z ⋙ T_Z ⟶ H_Z ⋙ Q'_Z)
    (E_f : R_f ⋙ T_X ≅ T_Y ⋙ R'_f) (E_g : R_g ⋙ T_Y ≅ T_Z ⋙ R'_g)
    (E_fg : R_fg ⋙ T_X ≅ T_Z ⋙ R'_fg)
    (e_f : ∀ K, H_X.obj (P_f.obj K) ⟶ P'_f.obj (H_Y.obj K))
    (e_g : ∀ K, H_Y.obj (P_g.obj K) ⟶ P'_g.obj (H_Z.obj K))
    (e_fg : ∀ K, H_X.obj (P_fg.obj K) ⟶ P'_fg.obj (H_Z.obj K))
    (d : R_fg ⟶ R_g ⋙ R_f) (d' : R'_fg ⟶ R'_g ⋙ R'_f)
    (d_h : ∀ K, P_fg.obj K ⟶ P_f.obj (P_g.obj K))
    (d'_h : ∀ K, P'_fg.obj K ⟶ P'_f.obj (P'_g.obj K)) (W : C_Z → Prop)
    (hE_f : ∀ K, W K → E_f.hom.app (Q_Y.obj (P_g.obj K)) ≫ R'_f.map (φ_Y.app (P_g.obj K)) ≫
        α'_f.app (H_Y.obj (P_g.obj K)) =
      T_X.map (α_f.app (P_g.obj K)) ≫ φ_X.app (P_f.obj (P_g.obj K)) ≫
        Q'_X.map (e_f (P_g.obj K)))
    (hE_g : ∀ K, W K → E_g.hom.app (Q_Z.obj K) ≫ R'_g.map (φ_Z.app K) ≫ α'_g.app (H_Z.obj K) =
      T_Y.map (α_g.app K) ≫ φ_Y.app (P_g.obj K) ≫ Q'_Y.map (e_g K))
    (hE_fg : ∀ K, W K →
      E_fg.hom.app (Q_Z.obj K) ≫ R'_fg.map (φ_Z.app K) ≫ α'_fg.app (H_Z.obj K) =
        T_X.map (α_fg.app K) ≫ φ_X.app (P_fg.obj K) ≫ Q'_X.map (e_fg K))
    (hd : ∀ K, d.app (Q_Z.obj K) ≫ R_f.map (α_g.app K) ≫ α_f.app (P_g.obj K) =
      α_fg.app K ≫ Q_X.map (d_h K))
    (hd' : ∀ K, d'.app (Q'_Z.obj K) ≫ R'_f.map (α'_g.app K) ≫ α'_f.app (P'_g.obj K) =
      α'_fg.app K ≫ Q'_X.map (d'_h K))
    (hH : ∀ K, e_fg K ≫ d'_h (H_Z.obj K) =
      H_X.map (d_h K) ≫ e_f (P_g.obj K) ≫ P'_f.map (e_g K))
    (hK : ∀ N : D_Z, ∃ K : C_Z, W K ∧ Nonempty (N ≅ Q_Z.obj K) ∧
      IsIso (R'_f.map (R'_g.map (φ_Z.app K)) ≫ R'_f.map (α'_g.app (H_Z.obj K)) ≫
        α'_f.app (P'_g.obj (H_Z.obj K))))
    (N : D_Z) :
    E_fg.hom.app N ≫ d'.app (T_Z.obj N) =
      T_X.map (d.app N) ≫ E_f.hom.app (R_g.obj N) ≫ R'_f.map (E_g.hom.app N) := by
  obtain ⟨K, hW, ⟨i⟩, _⟩ := hK N
  have key := comp_coherence_app_Q_of_isIso_left α_f α_g α_fg α'_f α'_g α'_fg φ_X φ_Y φ_Z E_f E_g
    E_fg e_f e_g e_fg d d' d_h d'_h K (hE_f K hW) (hE_g K hW) (hE_fg K hW) (hd K) (hd' _) (hH K)
  have n₁ := (E_fg.hom ≫ Functor.whiskerLeft T_Z d').naturality i.inv
  have n₂ := (Functor.whiskerRight d T_X ≫ Functor.whiskerLeft R_g E_f.hom ≫
    Functor.whiskerRight E_g.hom R'_f).naturality i.inv
  simp only [Functor.comp_obj, Functor.comp_map, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] at n₁ n₂
  rw [← cancel_epi (T_X.map (R_fg.map i.inv)), n₁, reassoc_of% key, ← n₂]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {A_X A_Y A_Z B_X B_Y B_Z : Type*} [Category* A_X] [Category* A_Y] [Category* A_Z]
  [Category* B_X] [Category* B_Y] [Category* B_Z] [Preadditive A_X] [Preadditive A_Y]
  [Preadditive A_Z] [Preadditive B_X] [Preadditive B_Y] [Preadditive B_Z]
  {P_f : A_Y ⥤ A_X} {P_g : A_Z ⥤ A_Y} {P_fg : A_Z ⥤ A_X}
  {P'_f : B_Y ⥤ B_X} {P'_g : B_Z ⥤ B_Y} {P'_fg : B_Z ⥤ B_X}
  {H_X : A_X ⥤ B_X} {H_Y : A_Y ⥤ B_Y} {H_Z : A_Z ⥤ B_Z}
  [P_f.Additive] [P_g.Additive] [P_fg.Additive] [P'_f.Additive] [P'_g.Additive]
  [P'_fg.Additive] [H_X.Additive] [H_Y.Additive] [H_Z.Additive]
  {J : Type*} (c : ComplexShape J)

/-- An isomorphism `P ⋙ H ≅ H' ⋙ P'` of additive functors, on the homotopy categories. -/
noncomputable def mapHomotopyCategoryCommIsoHom {A A' B B' : Type*} [Category* A] [Category* A']
    [Category* B] [Category* B'] [Preadditive A] [Preadditive A'] [Preadditive B]
    [Preadditive B'] {P : A ⥤ A'} {H : A' ⥤ B'} {H' : A ⥤ B} {P' : B ⥤ B'} [P.Additive]
    [H.Additive] [H'.Additive] [P'.Additive] (e : P ⋙ H ≅ H' ⋙ P') :
    P.mapHomotopyCategory c ⋙ H.mapHomotopyCategory c ⟶
      H'.mapHomotopyCategory c ⋙ P'.mapHomotopyCategory c :=
  (mapHomotopyCategoryCompIso e c).hom ≫ (mapHomotopyCategoryCompIso (Iso.refl _) c).inv

/-- If isomorphisms `e : P ⋙ H ≅ H' ⋙ P'` of additive functors are compatible with isomorphisms
`d : P_fg ≅ P_g ⋙ P_f` and `d' : P'_fg ≅ P'_g ⋙ P'_f`, then so are the induced morphisms on the
homotopy categories. -/
lemma mapHomotopyCategoryCommIsoHom_app_comp (e_f : P_f ⋙ H_X ≅ H_Y ⋙ P'_f)
    (e_g : P_g ⋙ H_Y ≅ H_Z ⋙ P'_g) (e_fg : P_fg ⋙ H_X ≅ H_Z ⋙ P'_fg)
    (d : P_fg ≅ P_g ⋙ P_f) (d' : P'_fg ≅ P'_g ⋙ P'_f)
    (h : ∀ M, e_fg.hom.app M ≫ d'.hom.app (H_Z.obj M) =
      H_X.map (d.hom.app M) ≫ e_f.hom.app (P_g.obj M) ≫ P'_f.map (e_g.hom.app M))
    (K : HomotopyCategory A_Z c) :
    (mapHomotopyCategoryCommIsoHom c e_fg).app K ≫
        (mapHomotopyCategoryCompIso d'.symm c).symm.hom.app ((H_Z.mapHomotopyCategory c).obj K) =
      (H_X.mapHomotopyCategory c).map ((mapHomotopyCategoryCompIso d.symm c).symm.hom.app K) ≫
        (mapHomotopyCategoryCommIsoHom c e_f).app ((P_g.mapHomotopyCategory c).obj K) ≫
        (P'_f.mapHomotopyCategory c).map ((mapHomotopyCategoryCommIsoHom c e_g).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change ((HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _) ≫
      (HomotopyCategory.quotient _ _).map _ =
    (H_X.mapHomotopyCategory c).map ((HomotopyCategory.quotient _ _).map _) ≫
      ((HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _) ≫
      (P'_f.mapHomotopyCategory c).map
        ((HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _)
  simp only [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  refine congrArg _ ?_
  ext n : 1
  simp only [comp_obj, Category.assoc, HomologicalComplex.comp_f,
    mapHomologicalComplexCompIso_hom_app_f, mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
    NatTrans.id_app, Iso.symm_inv, map_comp, mapHomologicalComplex_map_f]
  erw [Category.id_comp, Category.id_comp, Functor.map_id, Category.comp_id]
  exact h (K.X n)

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y Z : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The underived (Pull) isomorphisms `pullIso a` are compatible with the composition
isomorphisms `(f ≫ g)^* ≅ g^* ⋙ f^*`: they are the conjugates of the isomorphisms
`comapLowerStarIso a`, which are compatible with the composition isomorphisms of
pushforwards. -/
lemma pullIso_hom_app_comp
    (M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (pullIso a (f ≫ g)).hom.app M ≫
        (upperStarComp Λ' f g).hom.app ((Mod.extendScalars (coefficientMap a Z)).obj M) =
      (Mod.extendScalars (coefficientMap a X)).map ((upperStarComp Λ f g).hom.app M) ≫
        (pullIso a f).hom.app ((g)^*⟦Λ⟧.obj M) ≫
          (f)^*⟦Λ'⟧.map ((pullIso a g).hom.app M) :=
  Adjunction.pullIsoOfComapIso_hom_app_comp
    (adj_f := upperStarLowerStarAdjunction Λ f) (adj_g := upperStarLowerStarAdjunction Λ g)
    (adj_fg := upperStarLowerStarAdjunction Λ (f ≫ g))
    (adj'_f := upperStarLowerStarAdjunction Λ' f) (adj'_g := upperStarLowerStarAdjunction Λ' g)
    (adj'_fg := upperStarLowerStarAdjunction Λ' (f ≫ g))
    (c := upperStarComp Λ f g) (c' := upperStarComp Λ' f g)
    (h := fun N ↦ by
      simp only [conjugateIsoEquiv_apply_hom, conjugateEquiv_upperStarComp_hom_eq_lowerStarComp]
      exact comapLowerStarIso_hom_app_lowerStarComp Λ f g a N) (M := M) ..

/-- The underived (Pull) isomorphism `pullIso a h` on the homotopy categories:
`h^*_h ⋙ Ext_h ⟶ Ext_h ⋙ h^*_h`. -/
noncomputable abbrev pullIsoHomotopy {X Y : Scheme.{u}} (h : X ⟶ Y) :
    ((h)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ⋙
        (Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory (.up ℤ) ⟶
      (Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ) ⋙
        ((h)^*⟦Λ'⟧).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCommIsoHom (.up ℤ) (pullIso a h)

/-- The underived coherence of `pullIso a` with the composition isomorphisms of pullbacks, on the
homotopy categories. -/
lemma pullIsoHomotopy_upperStarCompHomotopy
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (.up ℤ)) :
    (pullIsoHomotopy a (f ≫ g)).app K ≫
        (upperStarCompHomotopy Λ' f g).hom.app
          (((Mod.extendScalars (coefficientMap a Z)).mapHomotopyCategory (.up ℤ)).obj K) =
      ((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategory (.up ℤ)).map
          ((upperStarCompHomotopy Λ f g).hom.app K) ≫
        (pullIsoHomotopy a f).app ((((g)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (((f)^*⟦Λ'⟧).mapHomotopyCategory (.up ℤ)).map ((pullIsoHomotopy a g).app K) :=
  Functor.mapHomotopyCategoryCommIsoHom_app_comp (.up ℤ) (pullIso a f) (pullIso a g)
    (pullIso a (f ≫ g)) (upperStarComp Λ f g) (upperStarComp Λ' f g) (pullIso_hom_app_comp a f g) K

-- the instances of the general lemmas are found for each of the categories of module objects
/-- The compatibility of `derivedUpperStarExtendScalarsIso a f` with the counits of the left
derived functors at a complex `K`: through these counits, it is the underived (Pull)
isomorphism `pullIso a f` at `K`. -/
def DerivedUpperStarExtendScalarsIsoFac
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) : Prop :=
  (derivedUpperStarExtendScalarsIso a f).hom.app (DerivedCategory.Qh.obj K) ≫
      L((f)^*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
      ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ)).obj K) =
    L(Mod.extendScalars (coefficientMap a X)).map (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K) ≫
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
        ((((f)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((pullIsoHomotopy a f).app K)

-- the instances of the general lemmas are found for each of the categories of module objects
/-- Every object of the derived category is the image of a K-flat complex `K`, at which the
composite of the counits of `L(Ext)`, `Lg^*` and `Lf^*` is an isomorphism: the pullbacks being
exact, their counits are isomorphisms. -/
lemma exists_kFlat_isIso_leftDerivedFunctorCounit_extendScalars
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    ∃ K, (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K ∧ Nonempty (N ≅ DerivedCategory.Qh.obj K) ∧
      IsIso (L((f)^*⟦Λ'⟧).map (L((g)^*⟦Λ'⟧).map
          ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctorCounit.app K)) ≫
        L((f)^*⟦Λ'⟧).map (((g)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
          (((Mod.extendScalars (coefficientMap a Z)).mapHomotopyCategory (.up ℤ)).obj K)) ≫
        ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app ((((g)^*⟦Λ'⟧).mapHomotopyCategory (.up ℤ)).obj
          (((Mod.extendScalars (coefficientMap a Z)).mapHomotopyCategory (.up ℤ)).obj K))) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_kFlat_iso_Qh_obj Λ N
  have := (Mod.extendScalars (coefficientMap a Z)).isIso_leftDerivedFunctorCounit_app_of_kFlat'
    K hK
  exact ⟨K, hK, ⟨e.symm⟩, inferInstance⟩

-- the instances of the general lemmas are found for each of the categories of module objects
/-- **Coherence of the derived (Pull) isomorphism for an arbitrary coefficient change**, given its
compatibility with the counits of the left derived functors on K-flat complexes:
`derivedUpperStarExtendScalarsIso a` is compatible with the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. -/
theorem derivedUpperStarExtendScalarsIsoCompCoherenceAt_of_fac
    (hE_f : ∀ K, (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K →
      DerivedUpperStarExtendScalarsIsoFac a f ((((g)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj K))
    (hE_g : ∀ K, (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K →
      DerivedUpperStarExtendScalarsIsoFac a g K)
    (hE_fg : ∀ K, (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K →
      DerivedUpperStarExtendScalarsIsoFac a (f ≫ g) K) :
    DerivedUpperStarExtendScalarsIsoCompCoherenceAt a f g :=
  Adjunction.comp_coherence_app_of_isIso_left
    (α_f := ((f)^*⟦Λ⟧).leftDerivedFunctorCounit) (α_g := ((g)^*⟦Λ⟧).leftDerivedFunctorCounit)
    (α_fg := ((f ≫ g)^*⟦Λ⟧).leftDerivedFunctorCounit)
    (α'_f := ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit) (α'_g := ((g)^*⟦Λ'⟧).leftDerivedFunctorCounit)
    (α'_fg := ((f ≫ g)^*⟦Λ'⟧).leftDerivedFunctorCounit)
    (φ_X := (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit)
    (φ_Y := (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit)
    (φ_Z := (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctorCounit)
    (E_f := derivedUpperStarExtendScalarsIso a f) (E_g := derivedUpperStarExtendScalarsIso a g)
    (E_fg := derivedUpperStarExtendScalarsIso a (f ≫ g))
    (e_f := (pullIsoHomotopy a f).app) (e_g := (pullIsoHomotopy a g).app)
    (e_fg := (pullIsoHomotopy a (f ≫ g)).app)
    (d := (leftDerivedUpperStarComp Λ f g).hom) (d' := (leftDerivedUpperStarComp Λ' f g).hom)
    (d_h := (upperStarCompHomotopy Λ f g).hom.app)
    (d'_h := (upperStarCompHomotopy Λ' f g).hom.app)
    (W := (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat) (hE_f := hE_f) (hE_g := hE_g)
    (hE_fg := hE_fg) (hd := leftDerivedUpperStarComp_hom_app_Qh_fac Λ f g)
    (hd' := leftDerivedUpperStarComp_hom_app_Qh_fac Λ' f g)
    (hH := pullIsoHomotopy_upperStarCompHomotopy a f g)
    (hK := exists_kFlat_isIso_leftDerivedFunctorCounit_extendScalars a f g)

end AlgebraicGeometry.ProEtale.CondensedRing
