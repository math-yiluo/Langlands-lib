/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Localization

/-!
# Pro-étale direct images commute with coproducts of complexes of étale origin

Let `Λ` be a finite ring and `p : Z ⟶ Y` a morphism between finite-type `k`-schemes. On the
pro-étale derived categories, the direct image `Rp_*` does not commute with coproducts in general
(`not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`).
It does on complexes with cohomology sheaves of étale origin, when `p` is proper:

* `Rp_*` has finite amplitude on such complexes
  (`AlgebraicGeometry.ProEtale.exists_isLE_rightDerivedLowerStar_of_etaleOriginHomology`): on a
  bounded one, which is `ν^* G` for a bounded étale complex `G`, it is `ν^* Rp_*^{ét} G`, and
  `Rp_*^{ét}` has finite cohomological dimension; an arbitrary one is the homotopy limit of its
  truncations `τ_{≥ -n}`, the pro-étale derived category being left complete
  (`DerivedCategory.isHomotopyLimit_truncGECone`);
* on uniformly bounded families it commutes with coproducts, since `Rp_*^{ét}` does for proper
  `p` (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`) and
  `ν^*` preserves coproducts;
* hence it commutes with all coproducts of complexes with cohomology of étale origin
  (`AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology`,
  by `DerivedCategory.isIso_sigmaComparison_of_bounded`).

This is the finite-coefficient direct-sum statement of blueprint
`proposition-proper-direct-image-finite-coefficients`
(`corollary-proper-direct-image-finite-coefficients-localizing`), in the form used by
`proposition-construction-independence-rf-shriek`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme _root_.DerivedCategory.TStructure

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-- On complexes with cohomology sheaves of étale origin, the pro-étale direct image along a
morphism of finite-type `k`-schemes has finite amplitude. -/
theorem exists_isLE_rightDerivedLowerStar_of_etaleOriginHomology {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p] (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hp : p ≫ aY = aZ) :
    ∃ e : ℤ, ∀ (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} Λ))) (b : ℤ), DerivedCategory.etaleOriginHomology Λ Z K → K.IsLE b →
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj K).IsLE (b + e) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  obtain ⟨d, hd⟩ := Etale.hasFiniteCohomologicalDimensionMorphism Λ hΛ aZ aY p hp
  have hcd : ∀ (F : Sheaf _ (ModuleCat.{u + 1} Λ)) (q : ℕ), d.toNat < q →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerived q).obj F) := fun F q hq ↦
    Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia))
  -- the bounded case
  have hbdd (T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
      (b : ℤ) (hT : DerivedCategory.etaleOriginHomology Λ Z T) (hTb : t.bounded T)
      (hTle : T.IsLE b) :
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj T).IsLE
        (b + d.toNat) := by
    obtain ⟨G, hG, ⟨e⟩⟩ := DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology Λ Z hT hTb
    have : G.IsLE b := isLE_of_isLE_mapDerivedCategory_comparisonUpperStar
      (t.isLE_of_iso e.symm b)
    have := Functor.isLE_rightDerivedFunctor_obj _ d.toNat hcd G b
    have : ((DerivedCategory.Plus.ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor ⋙
          D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj ⟨G, hG⟩).IsLE (b + d.toNat) :=
      (ν^*(Y)[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj G) (b + d.toNat)
    exact t.isLE_of_iso (((rightDerivedLowerStarComparisonIso _ p).app ⟨G, hG⟩).symm ≪≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.mapIso e) _
  have := CountableAB4Star.ofShape (C := Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℕ
  have := CountableAB4Star.ofShape (C := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℕ
  have := (mapDerivedUpperStarLowerStarAdjunction Λ p).rightAdjoint_preservesLimits
  refine ⟨d.toNat + 1, fun K b hK hKb ↦ ?_⟩
  have := _root_.DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor K (b + d.toNat) fun n ↦
      hbdd _ b (_root_.DerivedCategory.homologyProperty_truncGE hK _)
        ⟨⟨-(n : ℤ), inferInstance⟩, ⟨b, inferInstance⟩⟩ inferInstance
  rwa [← add_assoc]

/-- On uniformly bounded families of pro-étale complexes with cohomology sheaves of étale origin,
the direct image along a proper morphism commutes with coproducts. -/
theorem isIso_sigmaComparison_rightDerivedLowerStar_of_bounded {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [IsProper p] {J : Type (u + 1)}
    (N : J → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
    (a b : ℤ) (hN : ∀ j, DerivedCategory.etaleOriginHomology Λ Z (N j) ∧ (N j).IsGE a ∧
      (N j).IsLE b) :
    IsIso (sigmaComparison (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor N) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  choose G hG e' using fun j ↦ DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology Λ Z
    (hN j).1 ⟨⟨a, (hN j).2.1⟩, ⟨b, (hN j).2.2⟩⟩
  let e (j : J) := (e' j).some
  have hGa (j : J) : (G j).IsGE a := by
    have := (hN j).2.1
    exact isGE_of_isGE_mapDerivedCategory_comparisonUpperStar (t.isGE_of_iso (e j).symm a)
  let c : Cofan G := Cofan.mk (∐ G) (Sigma.ι G)
  have hc : IsColimit c := coproductIsCoproduct G
  have hS : (∐ G).IsGE a := _root_.DerivedCategory.isGE_sigma G a hGa
  have := Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper Λ hΛ p J
  let α := rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} Λ) p
  let β : Discrete.functor G ⋙ D(ν^*(Z)[ModuleCat.{u + 1} Λ]) ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor ≅
      Discrete.functor G ⋙ (Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor ⋙
        D(ν^*(Y)[ModuleCat.{u + 1} Λ]) :=
    Discrete.natIso fun j ↦ α.app ⟨G j.as, hG j.as⟩
  have hc' : IsColimit ((D(ν^*(Z)[ModuleCat.{u + 1} Λ]) ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor).mapCocone c) :=
    ((IsColimit.precomposeHomEquiv β _).symm
      (isColimitOfPreserves ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor ⋙
        D(ν^*(Y)[ModuleCat.{u + 1} Λ])) hc)).ofIsoColimit
      (Cocone.ext (α.app ⟨∐ G, ⟨a, hS⟩⟩).symm fun j ↦ by
        have h := α.inv.naturality (X := ⟨G j.as, hG j.as⟩) (Y := ⟨∐ G, ⟨a, hS⟩⟩)
          (ObjectProperty.homMk (Sigma.ι G j.as))
        dsimp [β, c] at h ⊢
        simp only [Discrete.natIso_hom_app]
        rw [Category.assoc, h, Iso.app_hom, Iso.hom_inv_id_app_assoc])
  have : PreservesColimit (Discrete.functor G ⋙ D(ν^*(Z)[ModuleCat.{u + 1} Λ]))
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves D(ν^*(Z)[ModuleCat.{u + 1} Λ]) hc) hc'
  have : PreservesColimit (Discrete.functor N)
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
    preservesColimit_of_iso_diagram _
      (Discrete.natIso (F := Discrete.functor G ⋙ D(ν^*(Z)[ModuleCat.{u + 1} Λ]))
        (G := Discrete.functor N) fun j ↦ e j.as)
  infer_instance

/-- The direct image along a proper morphism of finite-type `k`-schemes commutes with coproducts
of pro-étale complexes with cohomology sheaves of étale origin. -/
theorem isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsProper p] (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hp : p ≫ aY = aZ) {J : Type (u + 1)}
    (M : J → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
    (hM : ∀ j, DerivedCategory.etaleOriginHomology Λ Z (M j)) :
    IsIso (sigmaComparison (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor M) := by
  obtain ⟨e, he⟩ := exists_isLE_rightDerivedLowerStar_of_etaleOriginHomology Λ p aZ aY hp
  exact _root_.DerivedCategory.isIso_sigmaComparison_of_bounded _
    (DerivedCategory.etaleOriginHomology Λ Z)
    (fun _ n hX ↦ ⟨_root_.DerivedCategory.homologyProperty_truncLE hX n,
      _root_.DerivedCategory.homologyProperty_truncGE hX n⟩)
    (DerivedCategory.etaleOriginHomology_sigma Λ Z) e he
    (fun X a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ X a)
    (isIso_sigmaComparison_rightDerivedLowerStar_of_bounded Λ p) M hM

end AlgebraicGeometry.ProEtale
