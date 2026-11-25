/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Higher direct images commute with filtered colimits

For a quasi-compact quasi-separated `h : Y ⟶ X`, the functor `F ↦ R^q h_* F` on sheaves of
`Λ`-modules on `Y_ét` commutes with filtered colimits. The proof compares `R^q h_* F` with the
presheaf `W ↦ Hᵠ(W ×_X Y, F|)`: the canonical map between them is locally injective and locally
surjective, and on affine `W` the presheaf commutes with filtered colimits because étale
cohomology of the quasi-compact quasi-separated scheme `W ×_X Y` does.

## Main statements

- `AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImagePresheaf_app`: the
  presheaf `W ↦ Hᵠ(W ×_X Y, F|)` commutes with filtered colimits on each `W` with `W ×_X Y`
  quasi-compact and quasi-separated.
- `AlgebraicGeometry.Etale.preservesFilteredColimitsOfSize_higherDirectImage` and
  `AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`: higher direct images
  along a quasi-compact quasi-separated morphism commute with filtered colimits of sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- On an étale `X`-scheme `W` whose base change `W ×_X Y` is quasi-compact and
quasi-separated, the hypercohomology presheaves of single sheaves commute with filtered
colimits: `Hᵠ(W ×_X Y, F|)` is the étale cohomology of the scheme `W ×_X Y`
(`AlgebraicGeometry.Etale.shiftedHomFunctorUpperStarFreeSheafIso`), which commutes with
filtered colimits by
`AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject`. -/
theorem Etale.preservesColimitsOfShape_higherDirectImagePresheaf_app {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (W : X.Etale)
    [CompactSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left]
    [QuasiSeparatedSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left]
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.higherDirectImagePresheafFunctor Λ h q ⋙ (evaluation _ _).obj (op W)) := by
  -- The instance goals are taken from the type of the isomorphism, so that the kernel does not
  -- have to identify differently elaborated forms of the base change `W ×_X Y`.
  refine @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
    (Etale.shiftedHomFunctorUpperStarFreeSheafIso Λ h W q).symm ?_
  refine @Limits.comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ ?_
    (@Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject Λ _ _
      ‹CompactSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left›
      ‹QuasiSeparatedSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left› q J _ _)
  exact (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).leftAdjoint_preservesColimits
    |>.preservesColimitsOfShape

/-- Over an étale `X`-scheme `W` with affine underlying scheme, the base change along a
quasi-compact quasi-separated `h : Y ⟶ X` is quasi-compact and quasi-separated. -/
lemma Etale.compactSpace_and_quasiSeparatedSpace_pullback {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (W : X.Etale) [IsAffine W.left] :
    CompactSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left ∧
      QuasiSeparatedSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left := by
  rw [show ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left =
    Limits.pullback W.hom h from rfl]
  have : CompactSpace ((𝟭 Scheme).obj W.left) := inferInstanceAs (CompactSpace W.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj W.left) :=
    inferInstanceAs (QuasiSeparatedSpace W.left)
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst W.hom h),
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst W.hom h)⟩

/-- Sections of a filtered colimit of sheaves of `Λ`-modules, computed by sheafifying the
colimit of presheaves, come locally from a stage of the diagram. -/
lemma Etale.sheafifyCocone_locally {X : Scheme.{u}} {J : Type (u + 1)} [SmallCategory J]
    [IsFiltered J]
    (E : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {W : X.Etale}
    (s : ToType ((Sheaf.sheafifyCocone (colimit.cocone
      (E ⋙ sheafToPresheaf _ _))).pt.obj.obj (op W))) :
    Sieve.mk (fun V (g : V ⟶ W) ↦ ∃ (j : J) (x : ToType ((E.obj j).obj.obj (op V))),
      ((Sheaf.sheafifyCocone (colimit.cocone (E ⋙ sheafToPresheaf _ _))).ι.app j).hom.app
        (op V) x =
        (Sheaf.sheafifyCocone (colimit.cocone (E ⋙ sheafToPresheaf _ _))).pt.obj.map g.op s)
      (by
        rintro V V' g ⟨j, x, hx⟩ k
        refine ⟨j, (E.obj j).obj.map k.op x, ?_⟩
        rw [NatTrans.naturality_apply, hx]
        simp)
      ∈ X.smallEtaleTopology W := by
  refine GrothendieckTopology.superset_covering _ ?_ (Presheaf.imageSieve_mem X.smallEtaleTopology
    (toSheafify X.smallEtaleTopology (colimit (E ⋙ sheafToPresheaf _ _))) s)
  rintro V g ⟨t, ht⟩
  have : PreservesColimit ((E ⋙ sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op V))
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    inferInstance
  obtain ⟨j, x, hx⟩ := Concrete.isColimit_exists_rep _
    (isColimitOfPreserves ((evaluation _ _).obj (op V)) (colimit.isColimit _)) t
  refine ⟨j, x, ?_⟩
  rw [Sheaf.sheafifyCocone_ι_app_val, NatTrans.comp_app, ConcreteCategory.comp_apply]
  erw [hx]
  exact ht

-- The element chases below go through many coercions between sections of sheaves of modules
-- and of abelian groups, which are expensive for the kernel.
/-- A functor `G` to sheaves of `Λ`-modules on `X_ét` preserves filtered colimits as soon as it
receives a natural, locally injective and locally surjective map `ψ F : P F ⟶ G F` from a functor
`P` to presheaves which preserves filtered colimits after evaluation at each affine étale
`X`-scheme.

The functors are variables here so that the element chases are checked once, independently of
the (large) definitions of the functors they are later applied to. -/
theorem Etale.preservesColimitsOfShape_of_isLocallyBijective {X : Scheme.{u}}
    {𝒜 : Type*} [Category 𝒜] (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
    [HasColimitsOfShape J 𝒜]
    (G : 𝒜 ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (P : 𝒜 ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (ψ : ∀ F, P.obj F ⟶ ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj (G.obj F)).obj)
    (hψ : ∀ {F F'} (g : F ⟶ F'), P.map g ≫ ψ F' = ψ F ≫ Etale.sectionsMap (G.map g))
    (hψb : ∀ F, Presheaf.IsLocallyInjective X.smallEtaleTopology (ψ F) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology (ψ F))
    (hP : ∀ U : X.AffineEtale, PreservesColimitsOfShape J
      (P ⋙ (evaluation _ _).obj (op ((Scheme.AffineEtale.Spec X).obj U)))) :
    PreservesColimitsOfShape J G := by
  refine ⟨fun {D} ↦ ?_⟩
  let c := colimit.cocone D
  let c₀ := Sheaf.sheafifyCocone (colimit.cocone ((D ⋙ G) ⋙ sheafToPresheaf _ _))
  let hc₀ : IsColimit c₀ := Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)
  let a := hc₀.desc (G.mapCocone c)
  have ha : ∀ j, c₀.ι.app j ≫ a = G.map (c.ι.app j) := hc₀.fac _
  suffices IsIso a from
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D) (IsColimit.ofPointIso hc₀)
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    inferInstance
  refine (Sheaf.isLocallyBijective_iff_isIso a).1 ⟨?_, ?_⟩
  · constructor
    intro W x y hxy
    have hsieve : Presheaf.equalizerSieve x y = Presheaf.equalizerSieve (x - y) 0 := by
      ext V g
      simp only [Presheaf.equalizerSieve_apply, map_sub, map_zero]
      exact sub_eq_zero.symm
    rw [hsieve]
    have hz : a.hom.app W (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    generalize x - y = z at hz ⊢
    refine X.smallEtaleTopology.transitive (Etale.sheafifyCocone_locally Λ (D ⋙ G) z) _ ?_
    rintro V g ⟨j, zj, hzj⟩
    have hzj0 : (G.map (c.ι.app j)).hom.app (op V) zj = 0 := by
      have e := ConcreteCategory.congr_hom
        (NatTrans.congr_app (congrArg (fun f ↦ f.hom) (ha j)) (op V)) zj
      rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        ConcreteCategory.comp_apply, hzj] at e
      erw [NatTrans.naturality_apply a.hom g.op z, hz,
        map_zero] at e
      exact e.symm
    obtain ⟨_, _⟩ := hψb (D.obj j)
    obtain ⟨_, _⟩ := hψb c.pt
    refine X.smallEtaleTopology.transitive (Presheaf.imageSieve_mem X.smallEtaleTopology
      (ψ (D.obj j)) (show ToType ((((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).obj (G.obj (D.obj j))).obj).obj (op V)) from zj)) _ ?_
    rintro V' g' ⟨β, hβ⟩
    have hψβ : (ψ c.pt).app (op V') ((P.map (c.ι.app j)).app (op V') β) = 0 := by
      have e₁ := ConcreteCategory.congr_hom
        (NatTrans.congr_app (hψ (c.ι.app j)) (op V')) β
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e₁
      erw [e₁, hβ]
      have h₀ : (Etale.sectionsMap (G.map (c.ι.app j))).app (op V) zj = 0 := hzj0
      change (Etale.sectionsMap (G.map (c.ι.app j))).app (op V')
        ((((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ)
          AddCommGrpCat.{u + 1})).obj (G.obj (D.obj j))).obj.map g'.op) zj) = 0
      rw [NatTrans.naturality_apply]
      erw [h₀, map_zero]
    refine X.smallEtaleTopology.transitive (Presheaf.equalizerSieve_mem X.smallEtaleTopology
      (ψ c.pt) ((P.map (c.ι.app j)).app (op V') β) 0 (by rw [hψβ, map_zero])) _ ?_
    rintro V'' g'' hg''
    refine X.smallEtaleTopology.superset_covering ?_
      (Functor.is_cover_of_isCoverDense (Scheme.AffineEtale.Spec X) X.smallEtaleTopology V'')
    rintro V''' k ⟨⟨U, k₁, k₂, rfl⟩⟩
    have := hP U
    let βU := (P.obj (D.obj j)).map (k₂ ≫ g'').op β
    have hβU : (P.map (c.ι.app j)).app _ βU = (P.map (c.ι.app j)).app _ 0 := by
      simp only [βU, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, map_zero]
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      erw [hg'']
      erw [map_zero, map_zero]
    obtain ⟨j', f, f', hff⟩ := Concrete.isColimit_exists_of_rep_eq _
      (isColimitOfPreserves (P ⋙ (evaluation _ _).obj (op ((Scheme.AffineEtale.Spec X).obj U)))
        (colimit.isColimit D)) βU 0 hβU
    rw [map_zero] at hff
    have hψU : (ψ (D.obj j')).app _ ((P.map (D.map f)).app _ βU) = 0 := by
      erw [hff]
      exact AddMonoidHom.map_zero _
    have e₁ := ConcreteCategory.congr_hom
      (NatTrans.congr_app (hψ (D.map f)) (op ((Scheme.AffineEtale.Spec X).obj U))) βU
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e₁
    erw [hψU] at e₁
    -- `e₁ : 0 = G(D f)(ψ βU)`
    have e₂ : (ψ (D.obj j)).app _ βU = (G.obj (D.obj j)).obj.map ((k₂ ≫ g'') ≫ g').op zj := by
      simp only [βU]
      erw [NatTrans.naturality_apply (ψ (D.obj j)), hβ]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rfl
    have e₃ := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f ↦ f.hom) (c₀.w f))
        (op ((Scheme.AffineEtale.Spec X).obj U))) ((ψ (D.obj j)).app _ βU)
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] at e₃
    erw [← e₁, map_zero, e₂] at e₃
    -- `e₃ : 0 = c₀.ι j (G(D j).map _ zj)`
    have hU : c₀.pt.obj.map ((k₂ ≫ g'') ≫ g' ≫ g).op z = 0 := by
      rw [show ((k₂ ≫ g'') ≫ g' ≫ g) = ((k₂ ≫ g'') ≫ g') ≫ g by simp only [Category.assoc],
        op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hzj]
      erw [← NatTrans.naturality_apply (c₀.ι.app j).hom]
      exact e₃.symm
    have hU' : c₀.pt.obj.map ((((k₁ ≫ k₂) ≫ g'') ≫ g') ≫ g).op z = 0 := by
      rw [show (((k₁ ≫ k₂) ≫ g'') ≫ g') ≫ g = k₁ ≫ ((k₂ ≫ g'') ≫ g' ≫ g) by
        simp only [Category.assoc], op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hU]
      simp
    simpa using hU'
  · constructor
    intro W s
    obtain ⟨_, _⟩ := hψb c.pt
    have h₁ := Presheaf.imageSieve_mem X.smallEtaleTopology (ψ c.pt)
      (show ToType ((((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).obj (G.obj c.pt)).obj).obj (op W)) from s)
    refine X.smallEtaleTopology.transitive h₁ _ ?_
    rintro V g ⟨t, ht⟩
    refine X.smallEtaleTopology.superset_covering ?_
      (Functor.is_cover_of_isCoverDense (Scheme.AffineEtale.Spec X) X.smallEtaleTopology V)
    rintro V' k ⟨⟨U, k₁, k₂, rfl⟩⟩
    have := hP U
    obtain ⟨j, β, hβ⟩ := Concrete.isColimit_exists_rep _
      (isColimitOfPreserves (P ⋙ (evaluation _ _).obj (op ((Scheme.AffineEtale.Spec X).obj U)))
        (colimit.isColimit D)) ((P.obj c.pt).map k₂.op t)
    refine ⟨c₀.pt.obj.map k₁.op ((c₀.ι.app j).hom.app _ ((ψ (D.obj j)).app _ β)), ?_⟩
    have e₁ := ConcreteCategory.congr_hom
      (NatTrans.congr_app (hψ (c.ι.app j)) (op ((Scheme.AffineEtale.Spec X).obj U))) β
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e₁
    have e₂ := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f ↦ f.hom) (ha j))
        (op ((Scheme.AffineEtale.Spec X).obj U)))
      ((ψ (D.obj j)).app (op ((Scheme.AffineEtale.Spec X).obj U)) β)
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] at e₂
    rw [NatTrans.naturality_apply a.hom k₁.op]
    erw [e₂]
    erw [← e₁]
    erw [hβ, NatTrans.naturality_apply (ψ c.pt) k₂.op t, ht]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl

section ModuleSheafInstances

/- The comparison map `Etale.higherDirectImagePresheafToSheaf` and its properties are stated
with the instance names of `Etale.ModuleSheaf`, while the statements of this file are elaborated
with the instances found by synthesis. The kernel identifies the two only by unfolding the
abbreviation `DerivedCategory.Plus.singleFunctor`, which takes seconds each time. Applying
`Etale.preservesColimitsOfShape_of_isLocallyBijective` with the instances of
`Etale.ModuleSheaf` lets the kernel match the statements of the comparison map syntactically,
so that the two instance paths are compared once instead of once per hypothesis. -/
attribute [local instance] Etale.moduleSheafCategory Etale.moduleSheafPreadditive
  Etale.moduleSheafAbelian Etale.moduleSheafHasDerivedCategory

/-- `F ↦ R^q h_* F` preserves colimits of shape `J` as soon as the hypercohomology presheaves
`W ↦ Hᵠ(W ×_X Y, F|)` do on affine étale `X`-schemes. -/
private theorem Etale.preservesColimitsOfShape_higherDirectImage_of_app {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
    (hP : ∀ U : X.AffineEtale, PreservesColimitsOfShape J
      ((DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.higherDirectImagePresheafFunctor Λ h q) ⋙
          (evaluation _ _).obj (op ((Scheme.AffineEtale.Spec X).obj U)))) :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) :=
  Etale.preservesColimitsOfShape_of_isLocallyBijective Λ J _
    (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      Etale.higherDirectImagePresheafFunctor Λ h q)
    (fun F ↦ Etale.higherDirectImagePresheafToSheaf Λ h q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (fun _ ↦ Etale.higherDirectImagePresheafToSheaf_naturality Λ h q _)
    (fun F ↦ Etale.isLocallyBijective_higherDirectImagePresheafToSheaf Λ h q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) hP

end ModuleSheafInstances

/-- Blueprint `prose-04-17`: Filtered colimits and higher
direct image.

For a quasi-compact quasi-separated morphism `h : Y ⟶ X`, the higher direct image
`F ↦ R^q h_* F` commutes with filtered colimits of sheaves of `Λ`-modules on `Y_ét`:
`colim_i R^q h_* F_i ≅ R^q h_* (colim_i F_i)`. The functor is written out as the degree-`q`
homology of the derived pushforward of a sheaf placed in degree `0`, the functor whose value
at `F` is `AlgebraicGeometry.Etale.higherDirectImage`. -/
theorem Etale.preservesFilteredColimitsOfSize_higherDirectImage {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℤ) :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) := by
  refine ⟨fun J _ _ ↦ Etale.preservesColimitsOfShape_higherDirectImage_of_app Λ h q J
    fun U ↦ ?_⟩
  have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
    rw [Scheme.AffineEtale.Spec_obj_left]; infer_instance
  obtain ⟨_, _⟩ := Etale.compactSpace_and_quasiSeparatedSpace_pullback h
    ((Scheme.AffineEtale.Spec X).obj U)
  have := Etale.preservesColimitsOfShape_higherDirectImagePresheaf_app Λ h q
    ((Scheme.AffineEtale.Spec X).obj U) J
  exact preservesColimitsOfShape_of_natIso (Functor.associator _ _ _).symm

/-- Blueprint `prose-04-17`: Filtered colimits and higher
direct image, for filtered categories of any size
(`AlgebraicGeometry.Etale.preservesFilteredColimitsOfSize_higherDirectImage`).

For a quasi-compact quasi-separated morphism `h : Y ⟶ X`, the higher direct image
`F ↦ R^q h_* F` commutes with colimits over every essentially small (in the universe of the
coefficients) filtered category `J`. -/
theorem Etale.preservesColimitsOfShape_higherDirectImage {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℤ) (J : Type*) [Category* J]
    [EssentiallySmall.{u + 1} J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) :=
  have : IsFiltered (SmallModel.{u + 1} J) := IsFiltered.of_equivalence (equivSmallModel J)
  have := (Etale.preservesFilteredColimitsOfSize_higherDirectImage Λ h q)
    |>.preserves_filtered_colimits (SmallModel.{u + 1} J)
  preservesColimitsOfShape_of_equiv (equivSmallModel J).symm _

end AlgebraicGeometry
