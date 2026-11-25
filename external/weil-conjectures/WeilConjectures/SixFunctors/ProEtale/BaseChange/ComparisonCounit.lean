/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Compatibility of canonical derived site comparisons

These statements use the defining expressions of the comparison isomorphisms of
`SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean`; they are the inputs of
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` there.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C'] [HasDerivedCategory D']
  [EnoughInjectives D] [EnoughInjectives D']
  {l : C ⥤ D} {r : D ⥤ C} {p : C' ⥤ D'} {t : D' ⥤ C'}
  {a : C ⥤ C'} {b : D ⥤ D'}
  [l.Additive] [r.Additive] [p.Additive] [t.Additive] [a.Additive] [b.Additive]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits b] [PreservesFiniteColimits b]

/-- The right-derived base change of the mate of `σ` is the mate, for the derived adjunctions,
of the comparison induced by `σ` on bounded-below derived categories. -/
theorem CategoryTheory.Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv (e : l ⊣ r)
    (d : p ⊣ t) (σ : a ⋙ p ≅ l ⋙ b) :
    let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
    Functor.rightDerivedFunctorPlusBaseChange (mateEquiv e d σ.hom) =
      (mateEquiv e.derivedPlus d.derivedPlus θ.hom) := by
  dsimp only
  let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
  have hθ (N : HomotopyCategory.Plus C) :
      θ.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        D+(b).map (l.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        b.mapDerivedCategoryPlusFactorsh.hom.app (l.mapHomotopyCategoryPlus.obj N) =
      D+(p).map (a.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        p.mapDerivedCategoryPlusFactorsh.hom.app (a.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh l b N]
    rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N]
    rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh a p N]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Functor.rightDerived_ext (R+(r) ⋙ D+(a))
    (Functor.whiskerRight r.rightDerivedFunctorPlusUnith D+(a) ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso D)
  apply NatTrans.ext
  funext M
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (mateEquiv e d σ.hom)) M
  have hm := Adjunction.derivedPlus_mateEquiv_app_fac e d σ.hom θ.hom hθ M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf ⊢
  rw [hf, hm]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]

omit [EnoughInjectives D] [EnoughInjectives D'] in
private theorem comparison_iso_restrict (σ : a ⋙ p ≅ l ⋙ b)
    (Z : DerivedCategory.Plus C) :
    let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
    let θD := Functor.mapDerivedCategoryCompIso a p ≪≫
      Functor.mapDerivedCategoryNatIso σ ≪≫ (Functor.mapDerivedCategoryCompIso l b).symm
    DerivedCategory.Plus.ι.map (θ.inv.app Z) = θD.inv.app Z.obj := by
  dsimp only
  have hc : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso l b).app Z) =
      (Functor.mapDerivedCategoryCompIso l b).symm.app Z.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ Z)
  have hn : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusNatIso σ).app Z) =
      (Functor.mapDerivedCategoryNatIso σ).app Z.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app _ Z)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp]
  rw [show DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso l b).inv.app Z) =
      (Functor.mapDerivedCategoryCompIso l b).hom.app Z.obj from congrArg Iso.inv hc]
  rw [show DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusNatIso σ).inv.app Z) =
      (Functor.mapDerivedCategoryNatIso σ).inv.app Z.obj from congrArg Iso.inv hn]
  rw [Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  rfl

end

namespace AlgebraicGeometry.ProEtale.ComparisonCore
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The underived direct-image comparison, pulled back and composed with the pro-étale counit,
is the comparison pullback of the étale counit. -/
theorem underived_comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app K) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) K
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj K) ≫ t) h

/-- The underived direct-image comparison is the mate of the pullback comparison
`comparisonUpperStarCompUpperStarIso`. -/
theorem underived_comparison_mate {U V : Scheme.{u}} (f : U ⟶ V) :
    lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ) =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom) := by
  apply NatTrans.ext
  funext K
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
    underived_comparison_counit Λ f K

/-- **The canonical comparison of direct images and the counits**, on bounded below derived
categories and for an arbitrary morphism `f : U ⟶ V`: the pullback comparison `a` (the inverse
of `ν^* f^* ≅ f^* ν^*` on `D⁺`) at `R⁺f_* K`, followed by `f^*` of the canonical base change
morphism `ν_V^* R⁺f_* K ⟶ R⁺f_* ν_U^* K` of right derived functors and the pro-étale counit at
`ν_U^* K`, is `ν_U^*` of the étale counit `f^* R⁺f_* K ⟶ K`. -/
theorem comparison_counit_plus {U V : Scheme.{u}} (f : U ⟶ V)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let a := (Functor.mapDerivedCategoryPlusCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
      (upperStar (ModuleCat.{u + 1} Λ) f)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
    a.inv.app (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      D+(upperStar (ModuleCat.{u + 1} Λ) f).map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))).app K) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.counit.app
        (D+(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) =
    D+(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.counit.app K) := by
  dsimp only
  rw [underived_comparison_mate Λ f,
    Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f)]
  rw [mateEquiv_counit]
  simp

/-- The direct-image comparison is the counit mate of the specified pullback comparison.
Reference: Stacks Project, Tag 0B65.

Proof: the underived direct-image comparison is the inverse mate of the restriction
comparison. The pullback comparison is the adjoint conjugate of the same restriction
comparison. The mate counit identity therefore holds on sheaves. Apply it to complexes;
the defining unit factorization of rightDerivedFunctorPlusBaseChange and uniqueness of
right derived transformations give the identity on D+. The Plus-to-unbounded compatibility
isomorphisms transport the two counits to the indicated unbounded counit. This identifies
these fixed maps, without choosing a new direct-image isomorphism. -/
theorem comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f Λ).hom.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((  (fun {U V : Scheme.{u}} (f : U ⟶ V) (A : Type _)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [QuasiCompact f] [QuasiSeparated f] ↦
    Functor.isoWhiskerLeft R+(Etale.lowerStar A f)
        (ν^*(V)[A]).mapDerivedCategoryPlusCompatibility.symm ≪≫
      Functor.isoWhiskerRight ((fun {U V : Scheme.{u}} (f : U ⟶ V) (A : Type _)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [QuasiCompact f] [QuasiSeparated f] ↦
  have := isIso_lowerStarComparisonUpperStarBaseChange f A
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f A)) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange f A))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective A f I)
  asIso (Functor.rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange f A))
) f A) DerivedCategory.Plus.ι ≪≫
      Functor.isoWhiskerLeft D+(ν^*(U)[A])
        (ProEtale.lowerStar A f).rightDerivedFunctorPlusCompatibility ≪≫
      Functor.isoWhiskerRight (ν^*(U)[A]).mapDerivedCategoryPlusCompatibility
        R(ProEtale.lowerStar A f)
) f (ModuleCat.{u + 1} Λ)).hom.app K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).obj K) =
    (DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have h := congrArg (fun z ↦ DerivedCategory.Plus.ι.map z)
    (comparison_counit_plus Λ f K)
  rw [← Adjunction.derivedAdjunctionPlus_eq_derivedPlus] at h
  simp only [Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_counit_app, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] at h
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f
  have hθ := comparison_iso_restrict σ (R+(Etale.lowerStar
    (ModuleCat.{u + 1} Λ) f).obj K)
  simp only [
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map] at *
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [Category.id_comp]
  rw [Functor.mapDerivedCategoryNatIso_symm]
  erw [← NatTrans.naturality_assoc]
  rw [CategoryTheory.Functor.map_comp]
  rw [hθ] at h
  rw [← (Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) f).derivedAdjunctionPlus_eq_derivedPlus] at h
  simpa only [σ, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc,
    asIso_hom,
    leftDerivedUpperStarIsoMapDerivedCategory, derivedUpperStarLowerStarAdjunction,
    Etale.derivedUpperStarLowerStarAdjunctionPlus, Functor.mapDerivedCategoryPlus,
    ObjectProperty.lift, DerivedCategory.Plus.ι, ObjectProperty.ι,
    inducedFunctor, ObjectProperty.homMk, Functor.comp_obj, Functor.id_obj,
    Functor.comp_map] using h
end AlgebraicGeometry.ProEtale.ComparisonCore
