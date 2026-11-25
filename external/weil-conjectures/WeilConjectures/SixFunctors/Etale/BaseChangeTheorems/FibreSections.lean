/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleSectionContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SeparablyClosed

/-!
# Stalks of a direct image and sections over the geometric fibre

Let `f : X ⟶ Y` be a morphism of schemes, `ȳ : Spec Ω ⟶ Y` a geometric point and
`X_ȳ = X ×_Y Spec Ω` the geometric fibre, with projection `a : X_ȳ ⟶ X`. For an abelian étale
sheaf `F` on `X`, a germ at `ȳ` of a section of `f_* F` is represented by a section `s` of `F`
over `X ×_Y V` for a pointed étale neighbourhood `(V, v)` of `ȳ`; restricting `s` along
`X_ȳ ⟶ X ×_Y V` defines the comparison map
`AlgebraicGeometry.Etale.stalkToFibreSections : (f_* F)_ȳ ⟶ Γ(X_ȳ, a^* F)`.

For `f` proper and `Ω` algebraically closed this map is bijective
(`AlgebraicGeometry.Etale.bijective_stalkToFibreSections_of_isProper`): the stalk is the colimit
of the sections over the `X ×_Y V`, which is the group of sections over `X ×_Y S_(ȳ)` for the
strict localization `S_(ȳ)` (continuity of sections at inverse limits), which is the group of
sections over the closed geometric fibre (the degree-zero comparison over the strictly henselian
local ring of `S_(ȳ)`), which is the group of sections over `X_ȳ` (invariance of sections under
extension of algebraically closed base fields).

## Main definitions

- `AlgebraicGeometry.Etale.stalkToFibreSections`: the comparison map.
- `AlgebraicGeometry.Etale.fibreToStrictLocalization`: the morphism `X_ȳ ⟶ S_(ȳ) ×_Y X`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_stalkToFibreSections_of_isProper`: it is bijective for
  proper `f` and algebraically closed `Ω`.
- `AlgebraicGeometry.Etale.strictLocalizationPullback_sections`: the sections over
  `S_(ȳ) ×_Y X` are the colimit of the sections of `F` over the `V ×_Y X`.
- `AlgebraicGeometry.Etale.bijective_restrictAlong_fibreToStrictLocalization`: restriction of
  sections from `S_(ȳ) ×_Y X` to `X_ȳ` is bijective.

## References

- Stacks Project, Lemma 59.91.4, <https://stacks.math.columbia.edu/tag/0A3S>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {X Y Xy : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (a : Xy ⟶ X) (b : Xy ⟶ Spec (.of Ω)) (hab : a ≫ f = b ≫ y)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The morphism from the fibre `X_y` to the base change `V ×_Y X` given by a lift `v` of the
geometric point `y` to the étale `Y`-scheme `V`. -/
noncomputable def fibreToPullback (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    Xy ⟶ pullback V.hom f :=
  pullback.lift (b ≫ v.left) a (by
    rw [Category.assoc, show v.left ≫ V.hom = y from CategoryTheory.Over.w v, hab])

@[reassoc (attr := simp)]
lemma fibreToPullback_snd (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    fibreToPullback f y a b hab V v ≫ pullback.snd V.hom f = a :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma fibreToPullback_fst (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    fibreToPullback f y a b hab V v ≫ pullback.fst V.hom f = b ≫ v.left :=
  pullback.lift_fst _ _ _

/-- The restriction of a section of `F` over `V ×_Y X` to the fibre `X_y`, along the morphism
`AlgebraicGeometry.Etale.fibreToPullback` given by a lift `v` of `y` to `V`, as a morphism of
abelian groups. -/
noncomputable def fibreRestriction (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op V) ⟶
      ((a)^*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Xy))) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app F).hom.app
      (op (f.Etale.obj V)) ≫
    ((a)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (homToPullback a
      (V := Scheme.Etale.mk (𝟙 Xy)) (U := f.Etale.obj V) (fibreToPullback f y a b hab V v)
      ((fibreToPullback_snd f y a b hab V v).trans (Category.id_comp a).symm)).op

lemma fibreRestriction_apply (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
    (s : ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op V)) :
    fibreRestriction f y a b hab F V v s =
      pullSection a F (V := Scheme.Etale.mk (𝟙 Xy)) (U := f.Etale.obj V)
        (fibreToPullback f y a b hab V v)
        ((fibreToPullback_snd f y a b hab V v).trans (Category.id_comp a).symm) s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction to the fibre is compatible with the restriction maps of the direct image. -/
lemma fibreRestriction_map {V W : Y.Etale} (φ : V ⟶ W) (v : (pointSmallEtale y).fiber.obj V)
    (s : ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op W)) :
    fibreRestriction f y a b hab F V v (((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.map φ.op s) =
      fibreRestriction f y a b hab F W ((pointSmallEtale y).fiber.map φ v) s := by
  rw [fibreRestriction_apply, fibreRestriction_apply]
  change pullSection a F _ _ (F.obj.map (f.Etale.map φ).op s) = _
  rw [← pullSection_comp]
  exact pullSection_congr _ _ _ (by apply pullback.hom_ext <;> simp [Scheme.Hom.Etale]; rfl) _

lemma fibreRestriction_comp {V W : Y.Etale} (φ : V ⟶ W) (v : (pointSmallEtale y).fiber.obj V) :
    ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.map φ.op ≫ fibreRestriction f y a b hab F V v =
      fibreRestriction f y a b hab F W ((pointSmallEtale y).fiber.map φ v) := by
  ext s
  exact (ConcreteCategory.comp_apply _ _ _).trans (fibreRestriction_map f y a b hab F φ v s)

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison map** `(f_* F)_y ⟶ Γ(X_y, a^* F)` from the stalk of the direct image at a
geometric point to the sections over the geometric fibre: a germ represented by a section of
`F` over `V ×_Y X` is sent to its restriction to the fibre. -/
noncomputable def stalkToFibreSections :
    (pointSmallEtale y).presheafFiber.obj ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj ⟶
      ((a)^*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Xy))) :=
  (pointSmallEtale y).presheafFiberDesc (fibreRestriction f y a b hab F)
    (fun _ _ φ v ↦ fibreRestriction_comp f y a b hab F φ v)

lemma toPresheafFiber_stalkToFibreSections (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
    (s : ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op V)) :
    stalkToFibreSections f y a b hab F
        ((pointSmallEtale y).toPresheafFiber V v ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s) =
      fibreRestriction f y a b hab F V v s := by
  rw [← ConcreteCategory.comp_apply, stalkToFibreSections,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _
      (fun _ _ φ v ↦ fibreRestriction_comp f y a b hab F φ v)]

section ClosedFibre

/-- The morphism `X_y ⟶ S_(y) ×_Y X` from the geometric fibre to the base change of `X` to the
strict localization `S_(y)`, given by the factorization `Spec Ω ⟶ S_(y) ⟶ Y` of `y`. -/
noncomputable def fibreToStrictLocalization :
    Xy ⟶ pullback (Scheme.strictLocalizationToBase y) f :=
  pullback.lift (b ≫ Spec.map (Scheme.strictHenselizationEval y)) a (by
    rw [Category.assoc, Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase,
      hab])

/-- The first projection of `fibreToStrictLocalization`. -/
@[reassoc (attr := simp)]
lemma fibreToStrictLocalization_fst :
    fibreToStrictLocalization f y a b hab ≫ pullback.fst _ _ =
      b ≫ Spec.map (Scheme.strictHenselizationEval y) :=
  pullback.lift_fst _ _ _

/-- The second projection of `fibreToStrictLocalization`. -/
@[reassoc (attr := simp)]
lemma fibreToStrictLocalization_snd :
    fibreToStrictLocalization f y a b hab ≫ pullback.snd _ _ = a :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **Sections over the base change to the strict localization are sections over the geometric
fibre.** For `f` proper and `Ω` algebraically closed, restriction of sections of the pullback of
`F` along `X_y ⟶ S_(y) ×_Y X` is bijective. The ring of `S_(y)` is strictly henselian, so these
sections are those over the closed geometric fibre over an algebraic closure `κ̄` of the residue
field (`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_geometricFibre`),
and `X_y` is the base change of the closed geometric fibre along an embedding `κ̄ ⟶ Ω`
(`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_of_isAlgClosed`). -/
theorem bijective_restrictAlong_fibreToStrictLocalization [IsProper f] [IsAlgClosed Ω]
    (h : IsPullback a b f y) :
    Function.Bijective (restrictAlong (pullback.snd (Scheme.strictLocalizationToBase y) f) F
      (fibreToStrictLocalization f y a b h.w) a
      (fibreToStrictLocalization_snd f y a b h.w).symm
      (V := Scheme.Etale.mk (𝟙 _)) (V' := Scheme.Etale.mk (𝟙 Xy))
      (fibreToStrictLocalization f y a b h.w)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  let A := Scheme.strictHenselization y
  let κ := IsLocalRing.ResidueField A
  let κb := AlgebraicClosure κ
  let : Algebra κ Ω := (Scheme.strictHenselizationResidueFieldEmb y).toAlgebra
  have : Module.IsTorsionFree κ Ω := DivisionSemiring.to_moduleIsTorsionFree
  let ψ : κb →ₐ[κ] Ω := IsAlgClosed.lift
  let : Algebra κb Ω := ψ.toRingHom.toAlgebra
  let tS := pullback.snd (Scheme.strictLocalizationToBase y) f
  let p := pullback.fst (Scheme.strictLocalizationToBase y) f
  let sκ : Spec (.of κb) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A κb))
  let i := pullback.fst p sκ
  let q := pullback.snd p sκ
  let ω : Spec (.of Ω) ⟶ Spec (.of κb) := Spec.map (CommRingCat.ofHom (algebraMap κb Ω))
  let pr := pullback.fst q ω
  let q' := pullback.snd q ω
  have hω : ω ≫ sκ = Spec.map (Scheme.strictHenselizationEval y) := by
    rw [← Spec.map_comp]
    congr 1
    ext z
    change ψ (algebraMap A κb z) = _
    rw [IsScalarTower.algebraMap_apply A κ κb, ψ.commutes]
    exact Scheme.strictHenselizationResidueFieldEmb_residue z
  have sq : IsPullback (pr ≫ i ≫ tS) q' f y := by
    have := (IsPullback.of_hasPullback q ω).paste_horiz
      ((IsPullback.of_hasPullback p sκ).paste_horiz
        (IsPullback.of_hasPullback (Scheme.strictLocalizationToBase y) f).flip)
    rwa [← Category.assoc ω, hω,
      Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase] at this
  let e := h.isoIsPullback _ _ sq
  have he₁ : e.hom ≫ pr ≫ i ≫ tS = a := h.isoIsPullback_hom_fst _ _ sq
  have he₂ : e.hom ≫ q' = b := h.isoIsPullback_hom_snd _ _ sq
  have hc : fibreToStrictLocalization f y a b h.w = e.hom ≫ pr ≫ i := by
    apply pullback.hom_ext
    · rw [fibreToStrictLocalization_fst, Category.assoc, Category.assoc,
        show i ≫ p = q ≫ sκ from pullback.condition, ← Category.assoc pr,
        show pr ≫ q = q' ≫ ω from pullback.condition, Category.assoc, ← reassoc_of% he₂, hω]
    · rw [fibreToStrictLocalization_snd, Category.assoc, Category.assoc, he₁]
  have b₁ := (bijective_restrictAlong_iff_isIso_globalSectionsUpperStarMap tS F i (i ≫ tS)
    rfl).2 (Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_geometricFibre A p _)
  have b₂ := (bijective_restrictAlong_iff_isIso_globalSectionsUpperStarMap (i ≫ tS) F pr
    (pr ≫ i ≫ tS) rfl).2 (Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_of_isAlgClosed
      (K := Ω) q _)
  have b₃ := (bijective_restrictAlong_iff_isIso_globalSectionsUpperStarMap (pr ≫ i ≫ tS) F e.hom
    a he₁.symm).2 inferInstance
  convert b₃.comp (b₂.comp b₁) using 1
  funext s
  simp only [Function.comp_apply]
  rw [restrictAlong_restrictAlong, restrictAlong_restrictAlong]
  exact ConcreteCategory.congr_hom (restrictAlong_congr' tS F a hc _ _
    (V := Scheme.Etale.mk (𝟙 _)) (V' := Scheme.Etale.mk (𝟙 Xy)) hc _ _) s

end ClosedFibre

section Neighbourhoods

/-- The projection `S_(y) ×_Y X ⟶ V ×_Y X` for an affine pointed étale neighbourhood `(V, v)`
of `y`, induced by the leg `S_(y) ⟶ V` of the limit cone of the strict localization. -/
noncomputable def strictLocalizationPullbackLeg (x : Scheme.AffinePointedEtaleNeighborhood y) :
    pullback (Scheme.strictLocalizationToBase y) f ⟶ pullback x.obj.1.hom f :=
  pullback.map _ _ _ _ ((Scheme.strictLocalizationCone y).π.app x) (𝟙 X) (𝟙 Y)
    (by simp) (by simp)

/-- The first projection of `strictLocalizationPullbackLeg`. -/
@[reassoc (attr := simp)]
lemma strictLocalizationPullbackLeg_fst (x : Scheme.AffinePointedEtaleNeighborhood y) :
    strictLocalizationPullbackLeg f y x ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (Scheme.strictLocalizationCone y).π.app x :=
  pullback.lift_fst _ _ _

/-- The second projection of `strictLocalizationPullbackLeg`. -/
@[reassoc (attr := simp)]
lemma strictLocalizationPullbackLeg_snd (x : Scheme.AffinePointedEtaleNeighborhood y) :
    strictLocalizationPullbackLeg f y x ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [strictLocalizationPullbackLeg]

/-- The morphism `X_y ⟶ V ×_Y X` given by a lift of `y` to an affine pointed étale
neighbourhood `(V, v)` factors through `S_(y) ×_Y X`. -/
lemma fibreToStrictLocalization_comp_strictLocalizationPullbackLeg
    (x : Scheme.AffinePointedEtaleNeighborhood y) :
    fibreToStrictLocalization f y a b hab ≫ strictLocalizationPullbackLeg f y x =
      fibreToPullback f y a b hab x.obj.1 x.obj.2 := by
  apply pullback.hom_ext
  · rw [Category.assoc, strictLocalizationPullbackLeg_fst, fibreToStrictLocalization_fst_assoc,
      Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app,
      fibreToPullback_fst]
  · rw [Category.assoc, strictLocalizationPullbackLeg_snd, fibreToStrictLocalization_snd,
      fibreToPullback_snd]

/-- The base change `V ×_Y X ⟶ W ×_Y X` of a morphism of affine étale `Y`-schemes is affine. -/
lemma isAffineHom_etale_map_left {V W : Y.Etale} [IsAffine V.left] [IsAffine W.left]
    (φ : V ⟶ W) : IsAffineHom (f.Etale.map φ).left := by
  have big : IsPullback ((f.Etale.map φ).left ≫ pullback.snd W.hom f) (pullback.fst V.hom f) f
      (φ.left ≫ W.hom) := by
    rw [Scheme.Hom.etale_map_left_comp_snd, MorphismProperty.Over.w φ]
    exact (IsPullback.of_hasPullback V.hom f).flip
  have sq := big.of_right (Scheme.Hom.etale_map_left_comp_fst f φ)
    (IsPullback.of_hasPullback W.hom f).flip
  have : IsAffineHom (show V.left ⟶ W.left from φ.left) := isAffineHom_of_isAffine _
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip this

set_option backward.isDefEq.respectTransparency false in
/-- **Sections over the base change to the strict localization.** For `f` proper, the sections
of the pullback of `F` to `S_(y) ×_Y X` are the colimit of the sections of `F` over the
`V ×_Y X`, for the affine pointed étale neighbourhoods `(V, v)` of `y`: every section over
`S_(y) ×_Y X` is the pullback of a section over some `V ×_Y X`, and a section over `V ×_Y X`
whose pullback vanishes already vanishes over `V' ×_Y X` for some `(V', v') ⟶ (V, v)`. This is
the continuity of sections at inverse limits
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`)
for the cofiltered system of the `V ×_Y X` with `V` refining a fixed affine neighbourhood. -/
theorem strictLocalizationPullback_sections [IsProper f] :
    (∀ τ : ((pullback.snd (Scheme.strictLocalizationToBase y) f)^*[AddCommGrpCat.{u + 1}].obj
        F).obj.obj (op (Scheme.Etale.mk (𝟙 _))),
      ∃ (x : Scheme.AffinePointedEtaleNeighborhood y) (s : F.obj.obj (op (f.Etale.obj x.obj.1))),
        pullSection (pullback.snd (Scheme.strictLocalizationToBase y) f) F
          (V := Scheme.Etale.mk (𝟙 _)) (U := f.Etale.obj x.obj.1)
          (strictLocalizationPullbackLeg f y x)
          ((strictLocalizationPullbackLeg_snd f y x).trans (Category.id_comp _).symm) s = τ) ∧
    ∀ (x : Scheme.AffinePointedEtaleNeighborhood y) (s : F.obj.obj (op (f.Etale.obj x.obj.1))),
      pullSection (pullback.snd (Scheme.strictLocalizationToBase y) f) F
          (V := Scheme.Etale.mk (𝟙 _)) (U := f.Etale.obj x.obj.1)
          (strictLocalizationPullbackLeg f y x)
          ((strictLocalizationPullbackLeg_snd f y x).trans (Category.id_comp _).symm) s = 0 →
        ∃ (x' : Scheme.AffinePointedEtaleNeighborhood y) (g : x' ⟶ x),
          F.obj.map (f.Etale.map g.hom.1).op s = 0 := by
  let D₀ := InitiallySmall.CofilteredInitialModel.{u} (Scheme.AffinePointedEtaleNeighborhood y)
  let ι₀ := InitiallySmall.fromCofilteredInitialModel.{u}
    (Scheme.AffinePointedEtaleNeighborhood y)
  let d₀ : D₀ := (IsCofiltered.nonempty (C := D₀)).some
  let Φ : CategoryTheory.Over d₀ ⥤ Scheme.AffinePointedEtaleNeighborhood y :=
    CategoryTheory.Over.forget d₀ ⋙ ι₀
  let U : CategoryTheory.Over d₀ ⥤ X.Etale :=
    Φ ⋙ Scheme.AffinePointedEtaleNeighborhood.ι y ⋙ Functor.Elements.π _ ⋙ f.Etale
  let cK := (CategoryTheory.Over.forget X).mapCone
    ((CategoryTheory.Over.pullback f).mapCone (Scheme.strictLocalizationConeOver y))
  let E : Φ ⋙ (Scheme.affineNeighborhoodDiagramOver y ⋙ CategoryTheory.Over.pullback f) ⋙
      CategoryTheory.Over.forget X ≅ U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
      apply pullback.hom_ext
      · simp only [Functor.comp_obj, CategoryTheory.Over.forget_obj,
          CategoryTheory.Over.pullback_obj_left, Functor.comp_map,
          CategoryTheory.Over.forget_map, CategoryTheory.Over.pullback_map_left, Iso.refl_hom,
          Category.comp_id, Category.id_comp]
        erw [pullback.lift_fst]
      · simp only [Functor.comp_obj, CategoryTheory.Over.forget_obj,
          CategoryTheory.Over.pullback_obj_left, Functor.comp_map,
          CategoryTheory.Over.forget_map, CategoryTheory.Over.pullback_map_left, Iso.refl_hom,
          Category.comp_id, Category.id_comp]
        erw [pullback.lift_snd])
  let c := (Cone.postcompose E.hom).obj (cK.whisker Φ)
  have hc : IsLimit c := (IsLimit.postcomposeHomEquiv E _).symm
    ((Functor.Initial.isLimitWhiskerEquiv Φ cK).symm
      (Scheme.isLimitStrictLocalizationConePullback y f))
  have hcπ (j : CategoryTheory.Over d₀) :
      c.π.app j = strictLocalizationPullbackLeg f y (Φ.obj j) := by
    have h₁ : c.π.app j = pullback.lift (f := (Φ.obj j).obj.1.hom) (g := f)
        (pullback.fst _ _ ≫ (Scheme.strictLocalizationCone y).π.app (Φ.obj j))
        (pullback.snd (Scheme.strictLocalizationToBase y) f)
        (by simp [pullback.condition]) ≫ 𝟙 _ := rfl
    rw [h₁, Category.comp_id]
    apply pullback.hom_ext <;> simp [strictLocalizationPullbackLeg]
  let j₀ : CategoryTheory.Over d₀ := CategoryTheory.Over.mk (𝟙 d₀)
  have hj₀ : IsTerminal j₀ := CategoryTheory.Over.mkIdTerminal
  have ht : pullback.snd (Scheme.strictLocalizationToBase y) f = c.π.app j₀ ≫ (U.obj j₀).hom := by
    rw [hcπ]
    exact (strictLocalizationPullbackLeg_snd f y _).symm
  have (j : CategoryTheory.Over d₀) : CompactSpace (U.obj j).left := by
    have : CompactSpace ((𝟭 Scheme).obj (Φ.obj j).obj.1.left) :=
      inferInstanceAs (CompactSpace (Φ.obj j).obj.1.left)
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (Φ.obj j).obj.1.hom f)
  have (j : CategoryTheory.Over d₀) : QuasiSeparatedSpace (U.obj j).left := by
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj (Φ.obj j).obj.1.left) :=
      inferInstanceAs (QuasiSeparatedSpace (Φ.obj j).obj.1.left)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (Φ.obj j).obj.1.hom f)
  have {j k : CategoryTheory.Over d₀} (g : j ⟶ k) : IsAffineHom (U.map g).left :=
    isAffineHom_etale_map_left f (V := (Φ.obj j).obj.1) (W := (Φ.obj k).obj.1) _
  refine ⟨fun τ ↦ ?_, fun x s hs ↦ ?_⟩
  · obtain ⟨j, s, hs⟩ := exists_pullSection_eq_of_isLimit F U c j₀ hj₀ _ ht hc τ
    refine ⟨Φ.obj j, s, ?_⟩
    rw [← hs]
    exact pullSection_congr _ _ _ (hcπ j).symm _
  · obtain ⟨c'⟩ : Nonempty (CostructuredArrow Φ x) := inferInstance
    let j := c'.left
    let h : Φ.obj j ⟶ x := c'.hom
    have hs' : pullSection (pullback.snd (Scheme.strictLocalizationToBase y) f) F
        (V := Scheme.Etale.mk (𝟙 _)) (U := f.Etale.obj (Φ.obj j).obj.1)
        (strictLocalizationPullbackLeg f y (Φ.obj j))
        ((strictLocalizationPullbackLeg_snd f y _).trans (Category.id_comp _).symm)
        (F.obj.map (f.Etale.map h.hom.1).op s) = 0 := by
      rw [← pullSection_comp, ← hs]
      refine pullSection_congr _ _ _ ?_ _
      apply pullback.hom_ext
      · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst, strictLocalizationPullbackLeg_fst,
          strictLocalizationPullbackLeg_fst_assoc]
        congr 1
        exact (Scheme.strictLocalizationCone y).w h
      · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd, strictLocalizationPullbackLeg_snd,
          strictLocalizationPullbackLeg_snd]
    obtain ⟨j', g, hg⟩ := exists_map_eq_zero_of_pullSection_eq_zero_of_isLimit F U c j₀ hj₀ _ ht
      hc j _ ((pullSection_congr _ _ _ (hcπ j) _).trans hs')
    refine ⟨Φ.obj j', Φ.map g ≫ h, ?_⟩
    have e : (Φ.map g ≫ h).hom.1 = (Φ.map g).hom.1 ≫ h.hom.1 := rfl
    rw [e, Functor.map_comp, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact hg

end Neighbourhoods

/-- **Stalks of a proper direct image are sections over the geometric fibre.** Let
`f : X ⟶ Y` be proper and `y : Spec Ω ⟶ Y` a geometric point with `Ω` algebraically closed,
with geometric fibre `a : X_y ⟶ X`. For every abelian étale sheaf `F` on `X`, the comparison map
`(f_* F)_y ⟶ Γ(X_y, a^* F)` is bijective.

The stalk is the colimit of the sections of `F` over the `V ×_Y X` for the affine pointed étale
neighbourhoods `(V, v)` of `y`, which is the group of sections over `S_(y) ×_Y X` for the strict
localization `S_(y)` by continuity of sections at inverse limits
(`AlgebraicGeometry.Etale.strictLocalizationPullback_sections`); the ring of `S_(y)` is
strictly henselian, so these are the sections over the closed geometric fibre
(`AlgebraicGeometry.Etale.bijective_restrictAlong_fibreToStrictLocalization`), which are the
sections over `X_y` by the invariance of sections under extension of algebraically closed base
fields.
(blueprint: `proposition-proper-base-change-degree-zero`, the stalk formula) -/
@[stacks 0A3S]
theorem bijective_stalkToFibreSections_of_isProper [IsProper f] [IsAlgClosed Ω]
    (h : IsPullback a b f y) :
    Function.Bijective (stalkToFibreSections f y a b h.w F) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨hsurj, hinj⟩ := strictLocalizationPullback_sections f y F
  have hfib := bijective_restrictAlong_fibreToStrictLocalization f y a b F h
  -- the image of a germ over an affine neighbourhood factors through `S_(y) ×_Y X`
  have key (x : Scheme.AffinePointedEtaleNeighborhood y)
      (s : F.obj.obj (op (f.Etale.obj x.obj.1))) :
      stalkToFibreSections f y a b h.w F
          ((pointSmallEtale y).toPresheafFiber x.obj.1 x.obj.2
            ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s) =
        restrictAlong (pullback.snd (Scheme.strictLocalizationToBase y) f) F
          (fibreToStrictLocalization f y a b h.w) a
          (fibreToStrictLocalization_snd f y a b h.w).symm
          (V := Scheme.Etale.mk (𝟙 _)) (V' := Scheme.Etale.mk (𝟙 Xy))
          (fibreToStrictLocalization f y a b h.w)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
          (pullSection (pullback.snd (Scheme.strictLocalizationToBase y) f) F
            (V := Scheme.Etale.mk (𝟙 _)) (U := f.Etale.obj x.obj.1)
            (strictLocalizationPullbackLeg f y x)
            ((strictLocalizationPullbackLeg_snd f y x).trans (Category.id_comp _).symm) s) := by
    rw [toPresheafFiber_stalkToFibreSections, fibreRestriction_apply, restrictAlong_pullSection]
    exact pullSection_congr _ _ _
      (fibreToStrictLocalization_comp_strictLocalizationPullbackLeg f y a b h.w x).symm _
  -- every germ is represented over an affine neighbourhood
  have germ (z : ToType ((pointSmallEtale y).presheafFiber.obj
      ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj)) :
      ∃ (x : Scheme.AffinePointedEtaleNeighborhood y) (s : F.obj.obj (op (f.Etale.obj x.obj.1))),
        (pointSmallEtale y).toPresheafFiber x.obj.1 x.obj.2
          ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s = z := by
    obtain ⟨V, v, s, rfl⟩ := (pointSmallEtale y).toPresheafFiber_jointly_surjective z
    obtain ⟨x, ⟨g⟩⟩ := Scheme.AffinePointedEtaleNeighborhood.exists_hom y
      (Functor.elementsMk _ V v)
    refine ⟨x, ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.map g.1.op s, ?_⟩
    exact (GrothendieckTopology.Point.toPresheafFiber_w_apply _ g.1 x.obj.2 _ s).trans
      (congrArg (fun w ↦ (pointSmallEtale y).toPresheafFiber V w
        ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s) g.2)
  refine ⟨fun z₁ z₂ e ↦ ?_, fun σ ↦ ?_⟩
  · rw [← sub_eq_zero]
    have hz : stalkToFibreSections f y a b h.w F (z₁ - z₂) = 0 := by
      rw [map_sub, e, sub_self]
    obtain ⟨x, s, hs⟩ := germ (z₁ - z₂)
    rw [← hs] at hz ⊢
    rw [key] at hz
    obtain ⟨x', g, hg⟩ := hinj x s (hfib.1 (hz.trans (map_zero _).symm))
    have e₁ : (pointSmallEtale y).toPresheafFiber x.obj.1 x.obj.2
        ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s =
        (pointSmallEtale y).toPresheafFiber x'.obj.1 x'.obj.2
          ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj
          (((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.map g.hom.1.op s) := by
      exact ((GrothendieckTopology.Point.toPresheafFiber_w_apply _ g.hom.1 x'.obj.2
        ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s).trans
        (congrArg (fun w ↦ (pointSmallEtale y).toPresheafFiber x.obj.1 w
          ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s) g.hom.2)).symm
    have e₂ : ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.map g.hom.1.op s = 0 := hg
    rw [e₁, e₂, map_zero]
  · obtain ⟨τ, rfl⟩ := hfib.2 σ
    obtain ⟨x, s, rfl⟩ := hsurj τ
    exact ⟨_, key x s⟩

end AlgebraicGeometry.Etale
