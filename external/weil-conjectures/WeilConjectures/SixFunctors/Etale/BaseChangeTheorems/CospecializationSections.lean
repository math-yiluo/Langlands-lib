/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Cospecialization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.RingTheory.StrictlyHenselianNormal

/-!
# Cospecialization maps as restriction maps on the strict localization

Let `s : Spec Ω ⟶ Y` be a geometric point, `g : Y_(s) ⟶ Y` the strict localization and
`t : Spec Ω' ⟶ Y_(s)` a geometric point of `Y_(s)`. For a sheaf `G` of `Λ`-modules on `Y_ét`,
the cospecialization map `G_s ⟶ G_{t ≫ g}` is, through the identifications
`G_s ≅ Γ(Y_(s), g^* G)` and `G_{t ≫ g} ≅ Γ(Spec Ω', t^* g^* G)`, the restriction of global
sections along `t`.

## Main results

- `AlgebraicGeometry.Scheme.isIso_toPresheafFiber_of_isStrictlyHenselianLocalRing`: over a
  strictly henselian local ring `R`, the germ `Γ(Spec R, H) ⟶ H_x` at a geometric point `x`
  over the closed point is bijective.
- `AlgebraicGeometry.Scheme.bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap`:
  the cospecialization map is bijective as soon as the restriction
  `Γ(Y_(s), g^* G) ⟶ Γ(Spec Ω', t^* g^* G)` is.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

section Germ

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Sheaf Y.smallEtaleTopology A)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ X)

/-- **Germs of the unit of `f^* ⊣ f_*`.** Through `(f^* G)_y ≅ G_{y ≫ f}`, the germ of the
unit `G(U) ⟶ (f^* G)(U ×_Y X)` at the point of `U ×_Y X` induced by a point `ū` of `U` over
`y ≫ f` is the germ of `G` at `(U, ū)`. -/
@[reassoc]
lemma unit_app_toPresheafFiber_upperStarCompSheafFiberIso_hom (U : Y.Etale)
    (ū : (pointSmallEtale (y ≫ f)).fiber.obj U) :
    ((upperStarLowerStarAdjunction A f).unit.app G).hom.app (op U) ≫
        (pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
          ((pointSmallEtaleFiberEtaleIso f y).inv.app U ū) ((f)^*[A].obj G).obj ≫
        (upperStarCompSheafFiberIso A f y).hom.app G =
      (pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  rw [← Category.assoc, ← Iso.app_hom]
  apply (Iso.eq_comp_inv _).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous (MorphismProperty.Over.pullback @Etale ⊤ f) A
      (Y.smallGrothendieckTopology (P := @Etale)) (X.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction A f) G
  rw [← Category.assoc, ← NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)]
  rfl

/-- A point `v` over `y` of an étale `X`-scheme `V`, followed by a morphism `φ : V ⟶ U` over `f`
to an étale `Y`-scheme `U`, lies over `y ≫ f`. -/
lemma fiber_left_comp_comp_hom_eq {V : X.Etale} {U : Y.Etale} {φ : V.left ⟶ U.left}
    (hφ : φ ≫ U.hom = V.hom ≫ f) (v : (pointSmallEtale y).fiber.obj V) :
    (v.left ≫ φ) ≫ U.hom = y ≫ f := by
  have hv : v.left ≫ V.hom = y := CategoryTheory.Over.w v
  rw [Category.assoc, hφ, reassoc_of% hv]

/-- **Germs of pulled back sections.** Let `φ : V ⟶ U` be a morphism over `f` from an étale
`X`-scheme `V` to an étale `Y`-scheme `U`. Through `(f^* G)_y ≅ G_{y ≫ f}`, the germ at a point
`v` of `V` over `y` of the pullback along `φ` of a section of `G` over `U` is the germ of that
section at the point `v ≫ φ` of `U`. -/
@[reassoc]
lemma unit_app_map_toPresheafFiber_upperStarCompSheafFiberIso_hom {V : X.Etale} {U : Y.Etale}
    (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ f) (v : (pointSmallEtale y).fiber.obj V) :
    ((upperStarLowerStarAdjunction A f).unit.app G).hom.app (op U) ≫
        ((f)^*[A].obj G).obj.map (homToPullback f φ hφ).op ≫
        (pointSmallEtale y).toPresheafFiber V v ((f)^*[A].obj G).obj ≫
        (upperStarCompSheafFiberIso A f y).hom.app G =
      (pointSmallEtale (y ≫ f)).toPresheafFiber U
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (y ≫ f))
          (V := (Etale.forget Y).obj U) (v.left ≫ φ)
          (fiber_left_comp_comp_hom_eq f y hφ v))
        G.obj := by
  have key : (pointSmallEtale y).fiber.map (homToPullback f φ hφ) v =
      (pointSmallEtaleFiberEtaleIso f y).inv.app U
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (y ≫ f))
          (V := (Etale.forget Y).obj U) (v.left ≫ φ) (fiber_left_comp_comp_hom_eq f y hφ v)) := by
    refine ((pointSmallEtaleFiberEtaleIso f y).hom_inv_id_app_apply U _).symm.trans
      (congrArg _ (CategoryTheory.Over.OverMorphism.ext ?_))
    exact (Category.assoc _ _ _).trans (congrArg (v.left ≫ ·) (pullback.lift_fst _ _ _))
  rw [GrothendieckTopology.Point.toPresheafFiber_w_assoc, key]
  exact unit_app_toPresheafFiber_upperStarCompSheafFiberIso_hom A f G y U _

end Germ

section Transport

variable (A : Type u') [Category.{u + 1} A] [HasColimitsOfSize.{u, u} A] {Y : Scheme.{u}}
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- For equal geometric points `p = q`, the stalks at `p` and at `q` are isomorphic compatibly
with the germs. -/
lemma exists_sheafFiber_iso_of_eq {p q : Spec (.of Ω) ⟶ Y} (h : p = q)
    (F : Sheaf Y.smallEtaleTopology A) :
    ∃ e : (pointSmallEtale p).sheafFiber.obj F ≅ (pointSmallEtale q).sheafFiber.obj F,
      ∀ (U : Y.Etale) (u : (pointSmallEtale p).fiber.obj U),
        (pointSmallEtale p).toPresheafFiber U u F.obj ≫ e.hom =
          (pointSmallEtale q).toPresheafFiber U
            (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk q)
              (V := (Etale.forget Y).obj U) u.left (h ▸ CategoryTheory.Over.w u))
            F.obj := by
  subst h
  exact ⟨Iso.refl _, fun U u ↦ Category.comp_id _⟩

end Transport

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A separably closed field is a strictly henselian local ring. -/
instance isStrictlyHenselianLocalRing_of_isSepClosed (K : Type*) [Field K] [IsSepClosed K] :
    IsStrictlyHenselianLocalRing K :=
  IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed K

section StrictLocalization

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The geometric point `Spec Ω ⟶ S_(s)` given by the evaluation `𝒪^{sh}_{S,s} ⟶ Ω` lies over
the closed point of the strict localization. -/
lemma spec_map_strictHenselizationEval_apply_closedPoint :
    Spec.map (strictHenselizationEval s) (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselization s) :=
  have : IsLocalHom (strictHenselizationEval s).hom :=
    ⟨fun _ ha ↦ isUnit_of_strictHenselizationEval_ne_zero ha.ne_zero⟩
  IsLocalRing.comap_closedPoint (strictHenselizationEval s).hom

/-- The lift `v : Spec Ω ⟶ V` of the geometric point to a pointed étale neighbourhood `(V, v)`
is the composite of `Spec` of the evaluation map `𝒪^{sh}_{S,s} ⟶ Ω` with the leg
`S_(s) ⟶ V`. -/
@[reassoc]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationConeAll_π_app
    (x : PointedEtaleNeighborhood s) :
    Spec.map (strictHenselizationEval s) ≫ (strictLocalizationConeAll s).π.app x =
      x.2.left := by
  obtain ⟨c, ⟨f⟩⟩ := AffinePointedEtaleNeighborhood.exists_hom s x
  rw [← (strictLocalizationConeAll s).w f, strictLocalizationConeAll_π_app_ι_obj,
    spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app_assoc]
  exact congrArg CategoryTheory.CommaMorphism.left f.2

end StrictLocalization

/-- The strict henselization at a geometric point is a strictly henselian local ring. -/
instance isStrictlyHenselianLocalRing_strictHenselization {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    IsStrictlyHenselianLocalRing (strictHenselization s) :=
  (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed _).2
    ⟨henselianLocalRing_strictHenselization s, isSepClosed_residueField_strictHenselization s⟩

/-- **Sections over a strictly henselian local scheme are stalks at the closed point.** Let `R`
be a strictly henselian local ring and `x : Spec Ω ⟶ Spec R` a geometric point (`Ω` separably
closed) over the closed point. For every sheaf `H` of `Λ`-modules on `(Spec R)_ét`, the germ
`Γ(Spec R, H) ⟶ H_x` at the pointed étale neighbourhood `(Spec R, x)` is an isomorphism. -/
theorem isIso_toPresheafFiber_of_isStrictlyHenselianLocalRing {R : Type u} [CommRing R]
    [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of R)) (hx : x (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint R)
    (H : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 (Spec (.of R))))
      (CategoryTheory.Over.homMk x (Category.comp_id x)) H.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale x
  let T := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let t : Φ.fiber.obj T := CategoryTheory.Over.homMk x (Category.comp_id x)
  have hsec (X : (Spec (.of R)).Etale) (y : Φ.fiber.obj X) :
      ∃ g : T ⟶ X, Φ.fiber.map g t = y := by
    obtain ⟨σ, hσ, hsσ⟩ := strictlyHenselianSections_pointedSection inferInstance X.hom y.left x
      y.w ((congrArg x (Subsingleton.elim _ _)).trans hx)
    exact ⟨MorphismProperty.Over.homMk σ hσ, CategoryTheory.Over.OverMorphism.ext hsσ⟩
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨Y, f, y, _, heq⟩ := (Φ.toPresheafFiber_eq_iff' (P := H.obj) T t a b).mp hab
    obtain ⟨g, _⟩ := hsec Y y
    have hgf : g ≫ f = 𝟙 T := by
      apply MorphismProperty.Over.Hom.ext
      have hf : f.left ≫ 𝟙 _ = Y.hom := f.w
      rw [Category.comp_id] at hf
      exact (congrArg (g.left ≫ ·) hf).trans g.w
    have h := congrArg (H.obj.map g.op) heq
    simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
  · obtain ⟨X, y, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := H.obj) z
    obtain ⟨g, hg⟩ := hsec X y
    exact ⟨H.obj.map g.op a, by rw [Φ.toPresheafFiber_w_apply, hg]⟩

/-- **Germs of global sections at a geometric point.** Let `t : Spec Ω' ⟶ X` be a geometric
point (`Ω'` separably closed) and `H` a sheaf of `Λ`-modules on `X_ét`. If restriction of global
sections `Γ(X, H) ⟶ Γ(Spec Ω', t^* H)` is an isomorphism, then so is the germ
`Γ(X, H) ⟶ H_t` at the pointed étale neighbourhood `(X, t)`. -/
theorem isIso_toPresheafFiber_of_isIso_globalSectionsUpperStarMap {X : Scheme.{u}}
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ X)
    (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t H)) :
    IsIso ((pointSmallEtale t).toPresheafFiber (Scheme.Etale.mk (𝟙 X))
      (CategoryTheory.Over.homMk t (Category.comp_id t)) H.obj) := by
  let N := Scheme.Etale.mk (𝟙 X)
  let N' := Scheme.Etale.mk (𝟙 (Spec (.of Ω')))
  have hφ : t ≫ N.hom = N'.hom ≫ t := (Category.comp_id t).trans (Category.id_comp t).symm
  let η := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app H
  let H' := (t)^*[ModuleCat.{u + 1} Λ].obj H
  have hcore : IsIso (η.hom.app (op (⊤_ X.Etale)) ≫
      H'.obj.map (PreservesTerminal.iso t.Etale).inv.op) := by
    rw [Etale.globalSectionsUpperStarMap, isIso_comp_left_iff, ← Category.assoc,
      isIso_comp_right_iff] at h
    exact h
  let j : N ⟶ ⊤_ X.Etale :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X).uniqueUpToIso
      terminalIsTerminal).hom
  let k : N' ⟶ ⊤_ (Spec (.of Ω')).Etale :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _).uniqueUpToIso
      terminalIsTerminal).hom
  have hT : IsTerminal (t.Etale.obj (⊤_ X.Etale)) :=
    terminalIsTerminal.ofIso (PreservesTerminal.iso t.Etale).symm
  have e₁ : H.obj.map j.op ≫ η.hom.app (op N) =
      η.hom.app (op (⊤_ X.Etale)) ≫ H'.obj.map (t.Etale.map j).op :=
    η.hom.naturality j.op
  have e₂ : Etale.homToPullback (V := N') (U := N) t t hφ ≫ t.Etale.map j =
      k ≫ (PreservesTerminal.iso t.Etale).inv :=
    hT.hom_ext _ _
  have hL : IsIso (η.hom.app (op N) ≫
      H'.obj.map (Etale.homToPullback (V := N') (U := N) t t hφ).op) := by
    have : IsIso (H.obj.map j.op ≫ η.hom.app (op N) ≫
        H'.obj.map (Etale.homToPullback (V := N') (U := N) t t hφ).op) := by
      rw [← Category.assoc, e₁, Category.assoc, ← Functor.map_comp, ← op_comp, e₂, op_comp,
        Functor.map_comp, ← Category.assoc]
      infer_instance
    exact IsIso.of_isIso_comp_left (H.obj.map j.op) _
  have hgerm : IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω')))).toPresheafFiber N'
      (CategoryTheory.Over.homMk (𝟙 _) (Category.comp_id _)) H'.obj) :=
    isIso_toPresheafFiber_of_isStrictlyHenselianLocalRing (R := Ω') (𝟙 _) rfl H'
  obtain ⟨e, he⟩ := Etale.exists_sheafFiber_iso_of_eq (ModuleCat.{u + 1} Λ)
    (Category.id_comp t) H
  have hfin : (η.hom.app (op N) ≫ H'.obj.map (Etale.homToPullback (V := N') (U := N) t t hφ).op) ≫
      (pointSmallEtale (𝟙 (Spec (.of Ω')))).toPresheafFiber N'
        (CategoryTheory.Over.homMk (𝟙 _) (Category.comp_id _)) H'.obj ≫
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t (𝟙 _)).hom.app H ≫ e.hom =
        (pointSmallEtale t).toPresheafFiber N
          (CategoryTheory.Over.homMk t (Category.comp_id t)) H.obj := by
    rw [Category.assoc, Etale.unit_app_map_toPresheafFiber_upperStarCompSheafFiberIso_hom_assoc,
      he]
    exact congrArg (fun u ↦ (pointSmallEtale t).toPresheafFiber N u H.obj)
      (CategoryTheory.Over.OverMorphism.ext (Category.id_comp t))
  rw [← hfin]
  infer_instance

/-- **The cospecialization map is the restriction of sections over the strict localization.**
Let `s : Spec Ω ⟶ Y` be a geometric point with strict localization `g : Y_(s) ⟶ Y` and
`t : Spec Ω' ⟶ Y_(s)` a geometric point. For a sheaf `G` of `Λ`-modules on `Y_ét`, if
restriction of global sections `Γ(Y_(s), g^* G) ⟶ Γ(Spec Ω', t^* g^* G)` is an isomorphism,
then the cospecialization map `G_s ⟶ G_{t ≫ g}` is bijective. -/
theorem bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap {Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((strictLocalizationToBase s)^*[ModuleCat.{u + 1} Λ].obj G))) :
    Function.Bijective (cospecializationMap s t (ModuleCat.{u + 1} Λ) G).hom := by
  let g := strictLocalizationToBase s
  let s₀ : Spec (.of Ω) ⟶ strictLocalization s := Spec.map (strictHenselizationEval s)
  let G' := (g)^*[ModuleCat.{u + 1} Λ].obj G
  let N := Scheme.Etale.mk (𝟙 (strictLocalization s))
  have hα : IsIso ((pointSmallEtale s₀).toPresheafFiber N
      (CategoryTheory.Over.homMk s₀ (Category.comp_id s₀)) G'.obj) :=
    isIso_toPresheafFiber_of_isStrictlyHenselianLocalRing (R := ↑(strictHenselization s)) s₀
      (spec_map_strictHenselizationEval_apply_closedPoint s) G'
  have hβ := isIso_toPresheafFiber_of_isIso_globalSectionsUpperStarMap t G' h
  obtain ⟨e₀, he₀⟩ := Etale.exists_sheafFiber_iso_of_eq (ModuleCat.{u + 1} Λ)
    (spec_map_strictHenselizationEval_comp_strictLocalizationToBase s) G
  obtain ⟨a, ha⟩ : ∃ a, a = (pointSmallEtale s₀).toPresheafFiber N
      (CategoryTheory.Over.homMk s₀ (Category.comp_id s₀)) G'.obj ≫
    (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g s₀).hom.app G ≫ e₀.hom := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (pointSmallEtale t).toPresheafFiber N
      (CategoryTheory.Over.homMk t (Category.comp_id t)) G'.obj ≫
    (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g t).hom.app G := ⟨_, rfl⟩
  have : IsIso a := by
    rw [ha]
    infer_instance
  have : IsIso b := by
    rw [hb]
    infer_instance
  have hcosp : cospecializationMap s t (ModuleCat.{u + 1} Λ) G = inv a ≫ b := by
    refine (pointSmallEtale s).presheafFiber_hom_ext (P := G.obj) fun X x ↦ ?_
    let leg := (strictLocalizationConeAll s).π.app (Functor.elementsMk _ X x)
    have hleg : leg ≫ X.hom = N.hom ≫ g :=
      (strictLocalizationConeAll_π_app_hom s (Functor.elementsMk _ X x)).trans
        (Category.id_comp g).symm
    have hA : ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app G).hom.app
        (op X) ≫ G'.obj.map (Etale.homToPullback g leg hleg).op ≫ a =
          (pointSmallEtale s).toPresheafFiber X x G.obj := by
      rw [ha, Etale.unit_app_map_toPresheafFiber_upperStarCompSheafFiberIso_hom_assoc, he₀]
      exact congrArg (fun u ↦ (pointSmallEtale s).toPresheafFiber X u G.obj)
        (CategoryTheory.Over.OverMorphism.ext
          (spec_map_strictHenselizationEval_comp_strictLocalizationConeAll_π_app s
            (Functor.elementsMk _ X x)))
    have hB : ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app G).hom.app
        (op X) ≫ G'.obj.map (Etale.homToPullback g leg hleg).op ≫ b =
          (pointSmallEtale (t ≫ g)).toPresheafFiber X
            ((cospecializationNeighborhoodFunctor s t).obj (Functor.elementsMk _ X x)).2 G.obj := by
      rw [hb, Etale.unit_app_map_toPresheafFiber_upperStarCompSheafFiberIso_hom]
      rfl
    rw [toPresheafFiber_cospecializationMap s t _ G (Functor.elementsMk _ X x), ← hA,
      Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, hB]
  have : IsIso (cospecializationMap s t (ModuleCat.{u + 1} Λ) G) := by
    rw [hcosp]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

end AlgebraicGeometry.Scheme
