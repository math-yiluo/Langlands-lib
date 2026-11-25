/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-!

# Vertical pasting of the compact-support base change

For cartesian squares `sq₁ : IsPullback h v₁ v₂ g` and `sq₂ : IsPullback g w₁ w₂ l` of separated
`k`-schemes of finite type, the compact-support base change `Ex_!` of the outer rectangle on
bounded constructible `ℚ̄_ℓ`-sheaves is the horizontal composite of those of the two squares,
through the composition isomorphisms `R(v₂ ≫ w₂)_! ≅ Rv₂_! ⋙ Rw₂_!` and
`R(v₁ ≫ w₁)_! ≅ Rv₁_! ⋙ Rw₁_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert'`,
blueprint `proposition-composition-base-change-rf-shriek`, item (2)).

The proof computes all the compact-support base changes through the triangle of compactifications
`T₂` defining the composition isomorphism of `(v₂, w₂)` and its base change `T₁'` along the two
squares (`Compactification.Triangle.ofIsPullback`), on which the exchange maps are compatible
with the composition isomorphisms of the triangles
(`CategoryTheory.ExchangeFormalism.compIso_shriekBaseChange`), and uses that the composition
isomorphism of `(v₁, w₁)` can be computed through `T₁'`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

/-- The 2-categorical computation behind the vertical pasting of the compact-support base change:
if the exchange maps `EU`, `EV`, `EW` are conjugates of `SU`, `SV`, `SW` by comparison
isomorphisms, the composition isomorphisms `C₂`, `C₁` are computed through `cT₂`, `cT₁` and
the exchange maps `SU`, `SV`, `SW` are compatible with `cT₂`, `cT₁`, then `EU` is the
horizontal composite of `EV` and `EW`, conjugated by `C₂` and `C₁`. -/
lemma CategoryTheory.TwoSquare.eq_hComp_of_conj {A B C A' B' C' : Type*} [Category* A]
    [Category* B] [Category* C] [Category* A'] [Category* B'] [Category* C']
    {V₂ V₂T : A ⥤ B} {W₂ W₂T : B ⥤ C} {U₂ U₂T : A ⥤ C} {V₁ V₁T : A' ⥤ B'} {W₁ W₁T : B' ⥤ C'}
    {U₁ U₁T : A' ⥤ C'} {Lh : A ⥤ A'} {Lk : B ⥤ B'} {Ll : C ⥤ C'}
    (iU₂ : U₂ ≅ U₂T) (iV₂ : V₂ ≅ V₂T) (iW₂ : W₂ ≅ W₂T) (jU₁ : U₁T ≅ U₁) (jV₁ : V₁T ≅ V₁)
    (jW₁ : W₁T ≅ W₁) (kV₂ : V₂T ≅ V₂) (kW₂ : W₂T ≅ W₂) (kU₁ : U₁ ≅ U₁T)
    (cT₂ : V₂T ⋙ W₂T ≅ U₂T) (cT₁ : V₁T ⋙ W₁T ≅ U₁T)
    (SU : U₂T ⋙ Ll ⟶ Lh ⋙ U₁T) (SV : V₂T ⋙ Lk ⟶ Lh ⋙ V₁T) (SW : W₂T ⋙ Ll ⟶ Lk ⋙ W₁T)
    (EU : U₂ ⋙ Ll ⟶ Lh ⋙ U₁) (EV : V₂ ⋙ Lk ⟶ Lh ⋙ V₁) (EW : W₂ ⋙ Ll ⟶ Lk ⋙ W₁)
    (C₂ : U₂ ≅ V₂ ⋙ W₂) (C₁ : U₁ ≅ V₁ ⋙ W₁)
    (hU : EU = Functor.whiskerRight iU₂.hom Ll ≫ SU ≫ Functor.whiskerLeft Lh jU₁.hom)
    (hV : EV = Functor.whiskerRight iV₂.hom Lk ≫ SV ≫ Functor.whiskerLeft Lh jV₁.hom)
    (hW : EW = Functor.whiskerRight iW₂.hom Ll ≫ SW ≫ Functor.whiskerLeft Lk jW₁.hom)
    (hC₂ : C₂.hom = iU₂.hom ≫ cT₂.inv ≫ NatTrans.hcomp kV₂.hom kW₂.hom)
    (hC₁ : C₁.hom = kU₁.hom ≫ cT₁.inv ≫ NatTrans.hcomp jV₁.hom jW₁.hom)
    (hkV₂ : iV₂.symm = kV₂) (hkW₂ : iW₂.symm = kW₂) (hkU₁ : jU₁.symm = kU₁)
    (h : Functor.whiskerRight cT₂.hom Ll ≫ SU =
      (TwoSquare.hComp (T := V₂T) (B := V₁T) SV SW) ≫ Functor.whiskerLeft Lh cT₁.hom) :
    EU = Functor.whiskerRight C₂.hom Ll ≫
      (TwoSquare.hComp (T := V₂) (B := V₁) EV EW) ≫ Functor.whiskerLeft Lh C₁.inv := by
  subst hkV₂ hkW₂ hkU₁ hU hV hW
  obtain rfl : C₁ = jU₁.symm ≪≫ cT₁.symm ≪≫ NatIso.hcomp jV₁ jW₁ := Iso.ext (by simp [hC₁])
  ext X
  have hX := congr_app h X
  simp only [TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj] at hX
  simp only [hC₂, TwoSquare.hComp, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    NatIso.hcomp_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj, Functor.map_comp, Category.assoc, NatTrans.hcomp_app]
  simp only [Category.assoc] at hX ⊢
  have hSU : SU.app X = Ll.map (cT₂.inv.app X) ≫ SW.app (V₂T.obj X) ≫ W₁T.map (SV.app X) ≫
      cT₁.hom.app (Lh.obj X) := by
    rw [← hX, ← Ll.map_comp_assoc]; simp
  rw [hSU]
  simp only [Category.assoc, cancel_epi]
  rw [← Ll.map_comp_assoc, ← Ll.map_comp_assoc, Category.assoc, NatIso.naturality_1]
  erw [SW.naturality_assoc]
  simp only [Functor.comp_map]
  rw [jW₁.hom.naturality_assoc, ← W₁.map_comp_assoc, ← Lk.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.map_id, Category.id_comp]
  rw [← jW₁.hom.naturality_assoc, ← jW₁.hom.naturality_assoc, Iso.hom_inv_id_app_assoc,
    ← W₁T.map_comp_assoc]
  simp

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
  [LocallyOfFiniteType Y₃.hom] [QuasiCompact Y₃.hom] [IsSeparated Y₃.hom]
  {h : X₁ ⟶ X₂} {v₁ : X₁ ⟶ Y₁} {v₂ : X₂ ⟶ Y₂} {g : Y₁ ⟶ Y₂} {w₁ : Y₁ ⟶ X₃} {w₂ : Y₂ ⟶ Y₃}
  {l : X₃ ⟶ Y₃}

section Triangles

variable (sq₁ : IsPullback h v₁ v₂ g) (sq₂ : IsPullback g w₁ w₂ l)

variable (v₂ w₂) in
/-- The triangle of compactifications defining the composition isomorphism of `(v₂, w₂)`. -/
noncomputable abbrev pasteVertTriangle :
    AlgebraicGeometry.Compactification.Triangle v₂.left w₂.left :=
  triangleOfCompactifications (compactificationOverField v₂) (compactificationOverField w₂) _
    (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField v₂) (compactificationOverField w₂)).choose_spec

/-- The base change of `pasteVertTriangle` along the squares `sq₁` and `sq₂`. -/
noncomputable abbrev pasteVertTriangle' :
    AlgebraicGeometry.Compactification.Triangle v₁.left w₁.left :=
  (pasteVertTriangle v₂ w₂).ofIsPullback sq₁.overLeft sq₂.overLeft
    (sq₁.paste_vert sq₂).overLeft

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
  [IsSeparated X₁.hom] [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₃.hom] in
/-- The square of the maps `Z₁' ⟶ Z₁`, `W' ⟶ W` and the open immersions `q` of the triangles
`pasteVertTriangle'` and `pasteVertTriangle` is cartesian. -/
lemma isPullback_pasteVertTriangle_q :
    IsPullback ((compactificationOverField v₂).overBaseChangeFst sq₁)
      (Compactification.Triangle.overQ (pasteVertTriangle' sq₁ sq₂))
      (Compactification.Triangle.overQ (pasteVertTriangle v₂ w₂))
      ((Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).overBaseChangeFst
        (sq₁.paste_vert sq₂)) :=
  IsPullback.of_map (Over.forget _)
    (Over.OverMorphism.ext ((pasteVertTriangle v₂ w₂).isPullback_baseChangeQ
      sq₂.overLeft).w)
    ((pasteVertTriangle v₂ w₂).isPullback_baseChangeQ sq₂.overLeft)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
  [IsSeparated X₁.hom] [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₃.hom] in
/-- The maps `W' ⟶ W` and `Z₂' ⟶ Z₂` commute with the maps `r` of the triangles
`pasteVertTriangle'` and `pasteVertTriangle`. -/
lemma pasteVertTriangle_overBaseChangeFst_overP :
    (Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).overBaseChangeFst
        (sq₁.paste_vert sq₂) ≫ Compactification.Triangle.overP (pasteVertTriangle v₂ w₂) =
      Compactification.Triangle.overP (pasteVertTriangle' sq₁ sq₂) ≫
        (compactificationOverField w₂).overBaseChangeFst sq₂ :=
  Over.OverMorphism.ext (pasteVertTriangle v₂ w₂).baseChangeP_fst.symm

/-- The compact-support exchange maps of the triangle `pasteVertTriangle` and its base change
are compatible with the composition isomorphisms of the triangles. -/
lemma pasteVert_compIso_shriekBaseChange :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle v₂ w₂)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle v₂ w₂)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
    Functor.whiskerRight
        ((𝔽).compIso (triangleShriekTriangle (pasteVertTriangle v₂ w₂))).hom
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ l) ≫
      boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ
        (Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂))
        ((Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).ofIsPullback
          (sq₁.paste_vert sq₂).overLeft)
        ((Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).overBaseChangeFst
          (sq₁.paste_vert sq₂))
        ((Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_i
          (sq₁.paste_vert sq₂))
        ((Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_g
          (sq₁.paste_vert sq₂)) =
    (TwoSquare.hComp
        (boundedConstructibleLowerShriekOfCompactificationBaseChange
          ℓ
          (compactificationOverField v₂) ((compactificationOverField v₂).ofIsPullback sq₁.overLeft)
          ((compactificationOverField v₂).overBaseChangeFst sq₁)
          ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁)
          ((compactificationOverField v₂).overBaseChange_isPullback_g sq₁))
        (boundedConstructibleLowerShriekOfCompactificationBaseChange
          ℓ
          (compactificationOverField w₂) ((compactificationOverField w₂).ofIsPullback sq₂.overLeft)
          ((compactificationOverField w₂).overBaseChangeFst sq₂)
          ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂)
          ((compactificationOverField w₂).overBaseChange_isPullback_g sq₂))) ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h)
        ((𝔽).compIso (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂))).hom := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle v₂ w₂)
  have := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle v₂ w₂)
  have := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
  have := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
  have : IsIso ((𝔽).baseChange (SepFinType.homMk h)
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).i₁
      (triangleShriekTriangle (pasteVertTriangle v₂ w₂)).i₁
      (SepFinType.homMk ((compactificationOverField v₂).overBaseChangeFst sq₁))
      (SepFinType.homMk_comp_homMk
        ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁).w)) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁)
  have : IsIso ((𝔽).baseChange (SepFinType.homMk g)
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).i₂
      (triangleShriekTriangle (pasteVertTriangle v₂ w₂)).i₂
      (SepFinType.homMk ((compactificationOverField w₂).overBaseChangeFst sq₂))
      (SepFinType.homMk_comp_homMk
        ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂).w)) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂)
  have : IsIso ((𝔽).baseChange (SepFinType.homMk h)
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).i
      (triangleShriekTriangle (pasteVertTriangle v₂ w₂)).i
      (SepFinType.homMk ((Compactification.Triangle.overCfg
        (pasteVertTriangle v₂ w₂)).overBaseChangeFst (sq₁.paste_vert sq₂)))
      (SepFinType.homMk_comp_homMk ((Compactification.Triangle.overCfg
        (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_i
          (sq₁.paste_vert sq₂)).w)) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      ((Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_i
        (sq₁.paste_vert sq₂))
  have : IsIso ((𝔽).baseChange
      (SepFinType.homMk ((compactificationOverField v₂).overBaseChangeFst sq₁))
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).q
      (triangleShriekTriangle (pasteVertTriangle v₂ w₂)).q
      (SepFinType.homMk ((Compactification.Triangle.overCfg
        (pasteVertTriangle v₂ w₂)).overBaseChangeFst (sq₁.paste_vert sq₂)))
      (SepFinType.homMk_comp_homMk (isPullback_pasteVertTriangle_q sq₁ sq₂).w)) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      (isPullback_pasteVertTriangle_q sq₁ sq₂)
  unfold boundedConstructibleLowerShriekOfCompactificationBaseChange
  exact (𝔽).compIso_shriekBaseChange (triangleShriekTriangle (pasteVertTriangle v₂ w₂))
    (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂))
    (SepFinType.homMk ((compactificationOverField v₂).overBaseChangeFst sq₁))
    (SepFinType.homMk ((compactificationOverField w₂).overBaseChangeFst sq₂))
    (SepFinType.homMk ((Compactification.Triangle.overCfg
      (pasteVertTriangle v₂ w₂)).overBaseChangeFst (sq₁.paste_vert sq₂)))
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁).w)
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField v₂).overBaseChange_isPullback_g sq₁).w)
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂).w)
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField w₂).overBaseChange_isPullback_g sq₂).w)
    (SepFinType.homMk_comp_homMk ((Compactification.Triangle.overCfg
      (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_i (sq₁.paste_vert sq₂)).w)
    (SepFinType.homMk_comp_homMk ((Compactification.Triangle.overCfg
      (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_g (sq₁.paste_vert sq₂)).w)
    (SepFinType.homMk_comp_homMk (isPullback_pasteVertTriangle_q sq₁ sq₂).w)
    (SepFinType.homMk_comp_homMk (pasteVertTriangle_overBaseChangeFst_overP sq₁ sq₂))

/-- **Vertical pasting of `Ex_!`**, as an identity of natural transformations. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert' :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_vert sq₂) =
      Functor.whiskerRight (boundedConstructibleLowerShriekComp_padicAlgCl ℓ v₂ w₂).hom
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ l) ≫
        (TwoSquare.hComp (T := boundedConstructibleLowerShriek ℓ v₂)
          (B := boundedConstructibleLowerShriek ℓ v₁)
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁)
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂)) ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h)
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ v₁ w₁).inv := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle v₂ w₂)
  have := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle v₂ w₂)
  have := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
  have := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
  exact TwoSquare.eq_hComp_of_conj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ (sq₁.paste_vert sq₂)
      (Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂))
      ((Compactification.Triangle.overCfg (pasteVertTriangle v₂ w₂)).ofIsPullback
        (sq₁.paste_vert sq₂).overLeft)
      _ ((Compactification.Triangle.overCfg
        (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_i (sq₁.paste_vert sq₂))
      ((Compactification.Triangle.overCfg
        (pasteVertTriangle v₂ w₂)).overBaseChange_isPullback_g (sq₁.paste_vert sq₂)))
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq₁
      (compactificationOverField v₂) ((compactificationOverField v₂).ofIsPullback sq₁.overLeft)
      _ ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁)
      ((compactificationOverField v₂).overBaseChange_isPullback_g sq₁))
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq₂
      (compactificationOverField w₂) ((compactificationOverField w₂).ofIsPullback sq₂.overLeft)
      _ ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂)
      ((compactificationOverField w₂).overBaseChange_isPullback_g sq₂))
    (boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ v₂ w₂
      (pasteVertTriangle v₂ w₂))
    (boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ v₁ w₁
      (pasteVertTriangle' sq₁ sq₂))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ _ _)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ _ _)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ _ _)
    (pasteVert_compIso_shriekBaseChange ℓ sq₁ sq₂)

end Triangles

end AlgebraicGeometry.ProEtale.CondensedRing
