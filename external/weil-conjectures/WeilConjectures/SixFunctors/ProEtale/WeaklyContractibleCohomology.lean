/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension

/-!
# Cohomology over weakly contractible objects of the pro-étale site

For an object `U` of the small pro-étale site of `X`, the cohomology of `U` with coefficients in
a pro-étale sheaf `F` of `Λ`-modules is `Ext^r(Λ[U], F)`, where `Λ[U]` is the free sheaf of
`Λ`-modules on `U` (`AlgebraicGeometry.ProEtale.freeSheaf`).

For `p' : X' ⟶ V'` and a weakly contractible object `W` of `V'_proét`, the free sheaf `Λ[W]` is
projective (`AlgebraicGeometry.ProEtale.projective_freeSheaf`), so the Leray identification
collapses: the cohomology of `X' ×_{V'} W` with coefficients in `F` vanishes in degree `r` if and
only if the sections of `R^r p'_* F` over `W` do
(`AlgebraicGeometry.ProEtale.subsingleton_ext_freeSheaf_pullback_iff`). This gives the corrected
form of blueprint `lem-sf-fullcd-detection-equivalence`
(`AlgebraicGeometry.ProEtale.hasUniformCohomologicalDimensionLE_iff_forall_ext`).

## Main definitions

- `AlgebraicGeometry.ProEtale.freeSheaf`: the free sheaf `Λ[U]` on an object `U` of `X_proét`.
- `AlgebraicGeometry.ProEtale.freeSheafHomEquiv`: `Λ[U]` corepresents sections over `U`.
- `AlgebraicGeometry.ProEtale.upperStarFreeSheafIso`: `g^* Λ[U] ≅ Λ[U ×_X Y]`.

## Main statements

- `AlgebraicGeometry.ProEtale.projective_freeSheaf`: `Λ[W]` is projective for `W` weakly
  contractible.
- `AlgebraicGeometry.ProEtale.subsingleton_ext_freeSheaf_pullback_iff`: the Leray collapse over
  a weakly contractible object.
- `AlgebraicGeometry.ProEtale.hasUniformCohomologicalDimensionLE_iff_forall_ext`: blueprint
  `lem-sf-fullcd-detection-equivalence`, corrected.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The free sheaf `Λ[U]` of `Λ`-modules on an object `U` of the small pro-étale site of `X`:
the sheafification of the presheaf `V ↦ Λ^{(Hom_X(V, U))}`. It corepresents sections over `U`
(`AlgebraicGeometry.ProEtale.freeSheafHomEquiv`), and `Ext^r(Λ[U], F)` is the pro-étale
cohomology `H^r(U, F|_U)`. -/
noncomputable def freeSheaf (X : Scheme.{u}) :
    X.ProEt ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free Λ) ⋙
    presheafToSheaf _ _

variable {X : Scheme.{u}}

/-- The free sheaf `Λ[U]` corepresents sections over `U`. -/
noncomputable def freeSheafHomEquiv (U : X.ProEt)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    ((freeSheaf Λ X).obj U ⟶ G) ≃ G.obj.obj (op U) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((ModuleCat.adj Λ).whiskerRight X.ProEtᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

lemma freeSheafHomEquiv_comp (U : X.ProEt)
    {G G' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (f : (freeSheaf Λ X).obj U ⟶ G) (g : G ⟶ G') :
    freeSheafHomEquiv Λ U G' (f ≫ g) = g.hom.app (op U) (freeSheafHomEquiv Λ U G f) := by
  simp only [freeSheafHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    uliftYonedaEquiv_comp]

/-- For a weakly contractible object `W` of the small pro-étale site, the free sheaf `Λ[W]` is a
projective sheaf of `Λ`-modules: morphisms out of it are sections over `W`, and an epimorphism
of sheaves is locally surjective, hence surjective on sections over `W`. -/
lemma projective_freeSheaf (W : X.ProEt)
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    Projective ((freeSheaf Λ X).obj W) where
  factors {E G} f e _ := by
    have h : Sheaf.IsLocallySurjective e := (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
    obtain ⟨t, ht⟩ := hW ((sheafCompose _ (forget _)).map e)
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 h) (freeSheafHomEquiv Λ W G f)
    refine ⟨(freeSheafHomEquiv Λ W E).symm t, (freeSheafHomEquiv Λ W G).injective ?_⟩
    rw [freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
    exact ht

/-- Morphisms out of `h^* Λ[U]` are morphisms out of `Λ[U ×_X Y]`. -/
noncomputable def upperStarFreeSheafHomEquiv {Y : Scheme.{u}} (h : Y ⟶ X) (U : X.ProEt)
    (G : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    ((upperStar (ModuleCat.{u + 1} Λ) h).obj ((freeSheaf Λ X).obj U) ⟶ G) ≃
      ((freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj U) ⟶ G) :=
  ((upperStarLowerStarAdjunction _ h).homEquiv _ _).trans
    ((freeSheafHomEquiv Λ U _).trans (freeSheafHomEquiv Λ _ G).symm)

lemma upperStarFreeSheafHomEquiv_comp {Y : Scheme.{u}} (h : Y ⟶ X) (U : X.ProEt)
    {G G' : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)}
    (a : (upperStar (ModuleCat.{u + 1} Λ) h).obj ((freeSheaf Λ X).obj U) ⟶ G) (g : G ⟶ G') :
    upperStarFreeSheafHomEquiv Λ h U G' (a ≫ g) = upperStarFreeSheafHomEquiv Λ h U G a ≫ g := by
  apply (freeSheafHomEquiv Λ _ G').injective
  simp only [upperStarFreeSheafHomEquiv, Equiv.trans_apply, freeSheafHomEquiv_comp,
    Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The pullback of the free sheaf `Λ[U]` along `h : Y ⟶ X` is the free sheaf on `U ×_X Y`:
both corepresent the sections over `U ×_X Y`. -/
noncomputable def upperStarFreeSheafIso {Y : Scheme.{u}} (h : Y ⟶ X) (U : X.ProEt) :
    (upperStar (ModuleCat.{u + 1} Λ) h).obj ((freeSheaf Λ X).obj U) ≅
      (freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj U) :=
  Coyoneda.ext _ _ (fun f ↦ upperStarFreeSheafHomEquiv Λ h U _ f)
    (fun g ↦ (upperStarFreeSheafHomEquiv Λ h U _).symm g) (by simp) (by simp) (by
      intro Z Z' f g
      apply (upperStarFreeSheafHomEquiv Λ h U _).injective
      rw [upperStarFreeSheafHomEquiv_comp]
      simp)

/-- **Leray collapse over a weakly contractible object.** Let `p' : X' ⟶ V'`, let `W` be a
weakly contractible object of `V'_proét` and `F` a pro-étale sheaf of `Λ`-modules on `X'`. Then
the cohomology `H^r(X' ×_{V'} W, F|) = Ext^r(Λ[X' ×_{V'} W], F)` vanishes if and only if the
sections of `R^r p'_* F` over `W` vanish.

Indeed `Λ[X' ×_{V'} W] ≅ p'^* Λ[W]`, so by the adjunction `Lp'^* ⊣ Rp'_*` the Ext group is
`Hom(Λ[W][0], (Rp'_* F)[r])`; and `Λ[W]` is projective
(`AlgebraicGeometry.ProEtale.projective_freeSheaf`), so this vanishes if and only if
`Hom(Λ[W], R^r p'_* F)`, the sections of `R^r p'_* F` over `W`, does. -/
theorem subsingleton_ext_freeSheaf_pullback_iff {X' V' : Scheme.{u}} (p' : X' ⟶ V')
    (W : V'.ProEt) (hW : (Scheme.ProEt.topology V').IsWeaklyContractible.{u + 1} W)
    (F : Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} Λ)) (r : ℕ) :
    Subsingleton (Abelian.Ext.{u + 1} ((freeSheaf Λ X').obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p').obj W)) F r) ↔
      Subsingleton (((DerivedCategory.homologyFunctor _ r).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) p').rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).obj.obj (op W)) := by
  have := projective_freeSheaf Λ W hW
  let P := (freeSheaf Λ V').obj W
  let e : Abelian.Ext.{u + 1} ((freeSheaf Λ X').obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p').obj W)) F r ≃
      ((DerivedCategory.singleFunctor _ 0).obj P ⟶
        ((lowerStar (ModuleCat.{u + 1} Λ) p').rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj F))⟦(r : ℤ)⟧) :=
    Abelian.Ext.homEquiv.trans <|
      (Iso.homCongr ((DerivedCategory.singleFunctor _ 0).mapIso
          (upperStarFreeSheafIso Λ p' W).symm ≪≫
        ((singleFunctorCompLeftDerivedUpperStarIso _ p').app P).symm) (Iso.refl _)).trans <|
      ((derivedUpperStarLowerStarAdjunction _ p').homEquiv _ _).trans <|
      Iso.homCongr (Iso.refl _)
        (((lowerStar (ModuleCat.{u + 1} Λ) p').rightDerivedFunctor.commShiftIso (r : ℤ)).app _)
  rw [e.subsingleton_congr,
    DerivedCategory.subsingleton_singleFunctor_hom_shift_iff_of_projective,
    (freeSheafHomEquiv Λ W _).subsingleton_congr]

/-- Blueprint `lem-sf-fullcd-detection-equivalence` (corrected): detection of `FullCD` by the
cohomology of base changes of affine weakly contractible objects.

`FullCD(p, Λ; c)` holds if and only if, for every base change `p' : X' ⟶ V` of `p` along an
object `V` of `Y_proét`, every pro-étale sheaf `F` of `Λ`-modules on `X'`, every `r > c` and
every affine weakly contractible object `W` of `V_proét`, the pro-étale cohomology
`H^r((X' ×_V W)_proét, F|) = Ext^r(Λ[X' ×_V W], F)` vanishes.

The blueprint states the equivalence with the vanishing of `H^r((X ×_Y V)_proét, F|)` for all
objects `V` of `Y_proét`. That statement is false: for `p = 𝟙`, `FullCD(𝟙, Λ; 0)` holds since
the identity has no higher direct images, while `H^r(V_proét, F)` is nonzero in general. Its
proof, the collapse of the Leray spectral sequence, only works over weakly contractible `V`,
where `Λ[V]` is projective; that argument proves the corrected form above, by combining
`AlgebraicGeometry.ProEtale.subsingleton_ext_freeSheaf_pullback_iff` with the test on affine
weakly contractible objects of blueprint `cor-sf-fullcd-weakly-contractible-test`
(`AlgebraicGeometry.ProEtale.hasUniformCohomologicalDimensionLE_iff_forall_isWeaklyContractible`).
The degree `r : ℤ` of `FullCD` with `r > c ≥ 0` is a natural number here. -/
theorem hasUniformCohomologicalDimensionLE_iff_forall_ext {X Y : Scheme.{u}} (p : X ⟶ Y)
    (c : ℕ) :
    HasUniformCohomologicalDimensionLE (ModuleCat.{u + 1} Λ) p c ↔
      ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
        IsPullback g' p' p V.hom →
          ∀ (F : Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} Λ)) (r : ℕ), c < r →
            ∀ W : V.left.ProEt, IsAffine W.left →
              (Scheme.ProEt.topology V.left).IsWeaklyContractible.{u + 1} W →
                Subsingleton (Abelian.Ext.{u + 1} ((freeSheaf Λ X').obj
                  ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p').obj W)) F r) := by
  rw [hasUniformCohomologicalDimensionLE_iff_forall_isWeaklyContractible]
  refine forall_congr' fun V ↦ forall_congr' fun X' ↦ forall_congr' fun g' ↦
    forall_congr' fun p' ↦ forall_congr' fun _ ↦ forall_congr' fun F ↦ ?_
  refine ⟨fun h r hr W hWa hW ↦ (subsingleton_ext_freeSheaf_pullback_iff Λ p' W hW F r).2
    (h r (by exact_mod_cast hr) W hWa hW), fun h r hr W hWa hW ↦ ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ r)
  exact (subsingleton_ext_freeSheaf_pullback_iff Λ p' W hW F n).1
    (h n (by exact_mod_cast hr) W hWa hW)

end ProEtale

end AlgebraicGeometry
