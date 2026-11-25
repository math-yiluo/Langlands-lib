/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleBaseChangeRestrictScalars

/-!
# The coefficients of the smooth base change theorem

The smooth base change theorem is stated for a sheaf `F` of `Λ`-modules whose geometric stalks
are torsion of orders invertible on the base, while the base-change property
`AlgebraicGeometry.Etale.BaseChangeProperty` is indexed by a fixed coefficient ring. This file
contains the passage between the two.

- In negative degrees both sides of the base-change map vanish, the pullbacks being exact and
  the derived pushforwards preserving complexes concentrated in nonnegative degrees.
- *Filtered torsion*: `F` is the filtered colimit of subsheaves killed by integers `n`
  invertible on `S`
  (`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit`); the source
  `p⁻¹ R^q g_*` and the target `R^q h_* e⁻¹` of the base-change map commute with filtered
  colimits (`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`, and `p⁻¹`,
  `e⁻¹` are left adjoints), so it suffices to treat sheaves killed by one such `n`.
- *Change of rings*: a sheaf of `Λ`-modules killed by `n` is a sheaf of `Λ/nΛ`-modules, and
  its base-change map is the one computed over `Λ/nΛ`, so the base-change property over the
  ring `Λ/nΛ`, in which `n = 0`, applies to it.

## Main statements

- `AlgebraicGeometry.Etale.isZero_baseChangeSourceFunctor_obj_of_neg`,
  `AlgebraicGeometry.Etale.isZero_baseChangeTargetFunctor_obj_of_neg`: vanishing in negative
  degrees.
- `AlgebraicGeometry.Etale.baseChangeProperty_of_neg` and
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_neg`: the base-change property, and
  its universal form, in negative degrees.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_forall_nsmul_eq_zero`: reduction to
  sheaves killed by an integer invertible on `S`.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_nsmul_eq_zero`: the change of rings
  `Λ ↝ Λ/nΛ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]
  {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

section Identification

/-- The source `F ↦ H^q(p^*(R g_* F[0]))` of the base-change map is `p^*` of the higher direct
image functor `F ↦ R^q g_* F`, the pullback `p^*` being exact. -/
noncomputable def Etale.baseChangeSourceFunctorIso (p : X ⟶ S) (g : T ⟶ S) (q : ℤ) :
    Etale.baseChangeSourceFunctor Λ p g q ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙
        DerivedCategory.Plus.homologyFunctor _ q) ⋙ (p)^*[ModuleCat.{u + 1} Λ] :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R+((g)_*[ModuleCat.{u + 1} Λ])
      (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- The target `F ↦ H^q(R h_*(e^*(F[0])))` of the base-change map is the higher direct image
functor `F ↦ R^q h_* F` precomposed with `e^*`, the pullback `e^*` being exact. -/
noncomputable def Etale.baseChangeTargetFunctorIso (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ) :
    Etale.baseChangeTargetFunctor Λ e h q ≅
      (e)^*[ModuleCat.{u + 1} Λ] ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
      (R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) ≪≫
    Functor.associator _ _ _

/-- The source `p⁻¹ R^q g_* F` of the base-change map vanishes in negative degrees. -/
lemma Etale.isZero_baseChangeSourceFunctor_obj_of_neg (p : X ⟶ S) (g : T ⟶ S) {q : ℤ}
    (hq : q < 0) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero ((Etale.baseChangeSourceFunctor Λ p g q).obj F) :=
  IsZero.of_iso (((p)^*[ModuleCat.{u + 1} Λ]).map_isZero
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq))
    ((Etale.baseChangeSourceFunctorIso Λ p g q).app F)

/-- The target `R^q h_* e⁻¹ F` of the base-change map vanishes in negative degrees. -/
lemma Etale.isZero_baseChangeTargetFunctor_obj_of_neg (e : Y ⟶ T) (h : Y ⟶ X) {q : ℤ}
    (hq : q < 0) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero ((Etale.baseChangeTargetFunctor Λ e h q).obj F) :=
  IsZero.of_iso (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq)
    ((Etale.baseChangeTargetFunctorIso Λ e h q).app F)

/-- In negative degrees the base-change map is an isomorphism between zero objects. -/
lemma Etale.isIso_baseChangeHomologyMap_of_neg (sq : IsPullback e h g p) {q : ℤ} (hq : q < 0)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  ⟨0, (Etale.isZero_baseChangeSourceFunctor_obj_of_neg Λ p g hq F).eq_of_src _ _,
    (Etale.isZero_baseChangeTargetFunctor_obj_of_neg Λ e h hq F).eq_of_src _ _⟩

/-- The base-change property holds in negative degrees for every morphism `p`: the derived
pushforward of a sheaf placed in degree `0` has no cohomology in negative degrees, so both
`p⁻¹ R^q g_* F` and `R^q h_* e⁻¹ F` vanish for `q < 0`
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_neg`). -/
theorem Etale.baseChangeProperty_of_neg (p : X ⟶ S) {q : ℤ} (hq : q < 0) :
    Etale.BaseChangeProperty Λ p q := by
  intro T Y g e h _ _ sq F
  exact Etale.isIso_baseChangeHomologyMap_of_neg Λ sq hq F

/-- The base-change property holds universally in negative degrees, by
`AlgebraicGeometry.Etale.baseChangeProperty_of_neg` applied to every base change of `p`. -/
theorem Etale.universalBaseChangeProperty_of_neg (p : X ⟶ S) {q : ℤ} (hq : q < 0) :
    Etale.UniversalBaseChangeProperty Λ p q :=
  fun _ _ _ _ p' _ ↦ Etale.baseChangeProperty_of_neg Λ p' hq

end Identification

section ChangeOfRings

/-- The derived base-change morphism is the base change morphism of the right derived functor
`R g_*` along the exact functors `p^*` and `e^*`, attached to the underived base-change map. -/
lemma Etale.baseChange_eq_rightDerivedFunctorPlusBaseChange (sq : CommSq e h g p) :
    Etale.baseChange (ModuleCat.{u + 1} Λ) sq =
      Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  exact (Etale.derivedBaseChangeMapPlus_ext _ sq _
    (fun K ↦ Functor.rightDerivedFunctorPlusBaseChange_fac_app _ K)).symm

/-- If `a ≫ f = g ≫ b` with `a` and `b` isomorphisms, then `f` is an isomorphism as soon as
`g` is. -/
lemma Etale.isIso_of_comm {C : Type*} [Category C] {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (a : A' ⟶ A) (b : B' ⟶ B) [IsIso a] [IsIso b] (w : a ≫ f = g ≫ b) [IsIso g] : IsIso f := by
  have : IsIso (a ≫ f) := by rw [w]; infer_instance
  exact IsIso.of_isIso_comp_left a f

variable {Λ} {Λ' : Type (u + 1)} [CommRing Λ'] (φ : Λ →+* Λ')

/-- Restriction of scalars along `φ : Λ →+* Λ'` and the derived base-change morphism: if the
degree-`q` homology of the base-change morphism over `Λ'` is an isomorphism at a complex `K`,
then so is the degree-`q` homology of the base-change morphism over `Λ` at the restriction of
scalars of `K`. Restriction of scalars commutes with `p^*`, `e^*`
(`AlgebraicGeometry.Etale.upperStarRestrictScalars`), with the derived direct images
(`AlgebraicGeometry.Etale.rightDerivedLowerStarRestrictScalars`) and with the underived
base-change map (`AlgebraicGeometry.Etale.baseChangeMap_restrictScalars`); the pasting and
naturality laws of the base change morphisms of right derived functors identify the two
derived base-change morphisms up to these isomorphisms. -/
lemma Etale.isIso_homologyMap_baseChange_restrictScalars (sq : IsPullback e h g p) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ')))
    (hK : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ') sq.toCommSq).app K))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K))) := by
  rw [Etale.baseChange_eq_rightDerivedFunctorPlusBaseChange] at hK ⊢
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) q
  have hA := Functor.rightDerivedFunctorPlusBaseChange_paste
    (Etale.lowerStarCompRestrictScalarsIso φ g).hom
    (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) K
  have hB := Functor.rightDerivedFunctorPlusBaseChange_paste
    (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)
    (Etale.lowerStarCompRestrictScalarsIso φ h).hom K
  have hN := Functor.rightDerivedFunctorPlusBaseChange_naturality
    (Functor.baseChangePaste (Etale.lowerStarCompRestrictScalarsIso φ g).hom
      (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))
    (Functor.baseChangePaste (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)
      (Etale.lowerStarCompRestrictScalarsIso φ h).hom)
    (asIso (Etale.upperStarRestrictScalars φ p))
    (asIso (Etale.upperStarRestrictScalars φ e)) (by
      ext M : 2
      simp only [Functor.baseChangePaste, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc, asIso_hom]
      exact Etale.baseChangeMap_restrictScalars φ sq.toCommSq M) K
  -- the homology of `res (BC' K)`
  have h₁ : IsIso (H.map ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map
      ((Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)).app K))) := by
    have w := ((Sheaf.restrictScalars X.smallEtaleTopology φ)
      |>.mapDerivedCategoryPlusHomologyFunctorIso
      q).hom.naturality ((Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)).app K)
    have : IsIso (((DerivedCategory.Plus.homologyFunctor _ q) ⋙
        Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)).app K)) := by
      rw [Functor.comp_map]
      infer_instance
    exact Etale.isIso_of_comm _ _ w.symm
  -- the homology of the base change morphism of the second pasting
  have h₂ := congr_arg H.map hB
  simp only [CategoryTheory.Functor.map_comp] at h₂
  have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
      (Functor.baseChangePaste (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)
        (Etale.lowerStarCompRestrictScalarsIso φ h).hom)).app K)) := by
    have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
        (Functor.baseChangePaste (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)
          (Etale.lowerStarCompRestrictScalarsIso φ h).hom)).app K) ≫
        H.map (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusCompIso ((e)^*[ModuleCat.{u + 1} Λ'])
            (Sheaf.restrictScalars Y.smallEtaleTopology φ)).hom.app K))) := by
      rw [h₂]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (H.map (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusCompIso ((e)^*[ModuleCat.{u + 1} Λ'])
            (Sheaf.restrictScalars Y.smallEtaleTopology φ)).hom.app K)))
  -- transport along the naturality square
  have h₃ := congr_arg H.map hN
  simp only [CategoryTheory.Functor.map_comp] at h₃
  have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
      (Functor.baseChangePaste (Etale.lowerStarCompRestrictScalarsIso φ g).hom
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))).app K)) := by
    have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
        (Functor.baseChangePaste (Etale.lowerStarCompRestrictScalarsIso φ g).hom
          (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))).app K) ≫
        H.map (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusNatIso
            (asIso (Etale.upperStarRestrictScalars φ e))).hom.app K))) := by
      rw [h₃]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (H.map (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusNatIso
            (asIso (Etale.upperStarRestrictScalars φ e))).hom.app K)))
  -- the homology of the base change morphism of the first pasting
  have h₄ := congr_arg H.map hA
  simp only [CategoryTheory.Functor.map_comp] at h₄
  have : IsIso (H.map ((Functor.mapDerivedCategoryPlusCompIso
      (Sheaf.restrictScalars S.smallEtaleTopology φ) ((p)^*[ModuleCat.{u + 1} Λ])).hom.app
        ((((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlus).obj K)) ≫
      H.map (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (Etale.lowerStarCompRestrictScalarsIso φ g).hom).app K)) ≫
      H.map ((Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)).app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K))) := by
    rw [← h₄]
    infer_instance
  have : IsIso (H.map (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (Etale.lowerStarCompRestrictScalarsIso φ g).hom).app K)) ≫
      H.map ((Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)).app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K))) :=
    IsIso.of_isIso_comp_left (H.map ((Functor.mapDerivedCategoryPlusCompIso
      (Sheaf.restrictScalars S.smallEtaleTopology φ) ((p)^*[ModuleCat.{u + 1} Λ])).hom.app
        ((((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlus).obj K))) _
  have : IsIso ((Functor.rightDerivedFunctorPlusBaseChange
      (Etale.lowerStarCompRestrictScalarsIso φ g).hom).app K) :=
    inferInstanceAs (IsIso ((Etale.rightDerivedLowerStarRestrictScalars φ g).app K))
  exact IsIso.of_isIso_comp_left (H.map (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (Etale.lowerStarCompRestrictScalarsIso φ g).hom).app K))) _

end ChangeOfRings

section Torsion

private lemma isIso_quotientCounit (n : ℕ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : n • 𝟙 F = 0) :
    IsIso ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {(n : Λ)}))).counit.app F) := by
  let c := (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology
    (Ideal.Quotient.mk (Ideal.span {(n : Λ)}))).counit.app F
  have (U : T.Etaleᵒᵖ) : IsIso (c.hom.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨?_, ?_⟩
    · exact (ModuleCat.mono_iff_injective _).1
        (ModuleCat.mono_coextendQuotientShortComplex_f (n : Λ) (F.obj.obj U))
    · intro x
      apply (ShortComplex.moduleCat_exact_iff _).1
        (ModuleCat.exact_coextendQuotientShortComplex (n : Λ) (F.obj.obj U)) x
      have hn : n • 𝟙 (F.obj.obj U) = 0 :=
        congrArg (fun α : F ⟶ F ↦ α.hom.app U) hF
      change (n : Λ) • x = 0
      have hx := congrArg (fun α : F.obj.obj U ⟶ F.obj.obj U ↦ α.hom x) hn
      simpa only [ModuleCat.hom_nsmul, LinearMap.smul_apply,
        ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply, Nat.cast_smul_eq_nsmul] using hx
  have : IsIso ((sheafToPresheaf _ _).map c) := NatIso.isIso_of_isIso_app c.hom
  exact isIso_of_reflects_iso c (sheafToPresheaf _ _)

/-- The change of rings `Λ ↝ Λ/nΛ` for the base-change map.

Let `F` be a sheaf of `Λ`-modules on `T_ét` killed by `n`. Then `F` is a sheaf of
`Λ/nΛ`-modules, restriction of scalars along `Λ ⟶ Λ/nΛ` commutes with `p^*`, `e^*` and with the
derived pushforwards (the cohomology of a sheaf of modules does not depend on the coefficient
ring), and identifies the base-change map of `F` over `Λ` with the one over `Λ/nΛ`. Hence the
base-change property `BC(p, Λ/nΛ, q)` makes the base-change map of `F` an isomorphism. 
(blueprint: lem-sbc-quotient-coefficients-base-change)
-/
theorem Etale.isIso_baseChangeHomologyMap_of_nsmul_eq_zero (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g] (q : ℤ) (n : ℕ)
    (hp : Etale.BaseChangeProperty (Λ ⧸ Ideal.span {(n : Λ)}) p q)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : n • 𝟙 F = 0) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let φ := Ideal.Quotient.mk (Ideal.span {(n : Λ)})
  have : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isRightAdjoint
  have : PreservesLimitsOfSize.{u, u + 1}
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).rightAdjoint_preservesLimits
  let G := (sheafCompose T.smallEtaleTopology
    (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)).obj F
  let c := (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).counit.app F
  have : IsIso c := isIso_quotientCounit Λ n F hF
  have : IsIso (Etale.baseChangeHomologyMap (Λ ⧸ Ideal.span {(n : Λ)}) sq q G) :=
    hp g e h sq G
  obtain ⟨a⟩ := Etale.exists_baseChangeHomologyMap_restrictScalars_arrow_iso φ sq q G
  have : IsIso (Etale.baseChangeHomologyMap Λ sq q
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)) :=
    (Arrow.isIso_iff_isIso_of_isIso a.hom).2 (by infer_instance)
  have hc := Etale.baseChangeHomologyMap_naturality Λ sq q c
  change Etale.baseChangeHomologyMap Λ sq q
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) ≫
      (Etale.baseChangeTargetFunctor Λ e h q).map c =
    (Etale.baseChangeSourceFunctor Λ p g q).map c ≫
      Etale.baseChangeHomologyMap Λ sq q F at hc
  have heq : Etale.baseChangeHomologyMap Λ sq q F =
      inv ((Etale.baseChangeSourceFunctor Λ p g q).map c) ≫
        Etale.baseChangeHomologyMap Λ sq q
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) ≫
        (Etale.baseChangeTargetFunctor Λ e h q).map c := by
    rw [hc, IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- *Filtered torsion*: to prove that the base-change map is an isomorphism at a sheaf which is
torsion of orders invertible on `S`, it suffices to do so at the sheaves killed by a single
positive integer `n` invertible on `S`. Such a sheaf is a filtered colimit of sheaves of that
kind, the source and the target of the base-change map commute with filtered colimits, and a
natural transformation between colimit-preserving functors which is an isomorphism on a
diagram is an isomorphism at its colimit. -/
theorem Etale.isIso_baseChangeHomologyMap_of_forall_nsmul_eq_zero (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g] (q : ℤ)
    (H : ∀ n : ℕ, 0 < n → IsUnit (n : Γ(S, ⊤)) →
      ∀ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), n • 𝟙 G = 0 →
        IsIso (Etale.baseChangeHomologyMap Λ sq q G))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq ‹_›
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq ‹_›
  obtain ⟨J, _, _, D, c, hc, rfl, hD⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit Λ S F
  have : EssentiallySmall.{u + 1} J := essentiallySmallSelf.{u + 1} J
  have := Etale.preservesColimitsOfShape_higherDirectImage Λ g q J
  have := Etale.preservesColimitsOfShape_higherDirectImage Λ h q J
  have : PreservesColimitsOfSize.{0, 0} ((p)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} ((e)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape J (Etale.baseChangeSourceFunctor Λ p g q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeSourceFunctorIso Λ p g q).symm
  have : PreservesColimitsOfShape J (Etale.baseChangeTargetFunctor Λ e h q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeTargetFunctorIso Λ e h q).symm
  have : IsIso (Functor.whiskerLeft D (Etale.baseChangeHomologyNatTrans Λ sq q)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    obtain ⟨n, hn, hnS, hnj⟩ := hD j
    exact H n hn hnS _ hnj
  exact isIso_app_coconePt_of_preservesColimit D _ c hc

end Torsion

end AlgebraicGeometry
