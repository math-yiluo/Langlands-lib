/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverMilnorAb

/-!
# The integral identification on the universal cover, from cohomology towers on the base

- `AlgebraicGeometry.ProEtale.upperStarCompSheafComposeForget₂Iso`: for `f` weakly étale, the
  pullback `f^*` commutes with taking underlying abelian sheaves of sheaves of `Λ`-modules, both
  pullbacks being restrictions along the localization functor.
- `AlgebraicGeometry.Scheme.UniversalCovers.nonempty_iso_homologyUpperStar_continuousMapAddSheaf'`:
  the integral identification `Hⁱ(p^* R lim F) ≅ C(-, lim_n (H'ₙ)_y)` of
  `WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverMilnorAb`, with the cohomology
  towers of `F` identified on the base `Y` rather than on the universal cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {V U : Scheme.{u}} (f : V ⟶ U) [hf : WeaklyEtale f] (Λ : Type (u + 1)) [Ring Λ]

/-- Restriction along the localization functor commutes with taking underlying abelian sheaves. -/
noncomputable def localizationRestrictionCompSheafComposeForget₂Iso :
    ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) f hf ⋙
        sheafCompose (Scheme.ProEt.topology V) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology U) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙
        ProEtale.localizationRestriction Ab.{u + 1} f hf :=
  Iso.refl _

/-- **Pullback along a weakly étale morphism commutes with taking underlying abelian sheaves.** -/
noncomputable def upperStarCompSheafComposeForget₂Iso :
    ProEtale.upperStar (ModuleCat.{u + 1} Λ) f ⋙
        sheafCompose (Scheme.ProEt.topology V) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology U) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙
        ProEtale.upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction _ f hf) _ ≪≫
    localizationRestrictionCompSheafComposeForget₂Iso f Λ ≪≫
    Functor.isoWhiskerLeft _ (upperStarIsoLocalizationRestriction _ f hf).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]

/-- A cohomology tower identification on the base `Y` gives one on the universal cover. -/
noncomputable def UniversalCovers.homologyUpperStarTowerIso
    (F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology Y) Ab.{u + 1})) (k : ℤ)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : F ⋙ DerivedCategory.homologyFunctor _ k ≅
      H ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :
    (F ⋙ (ProEtale.upperStar Ab.{u + 1} (U.proj y)).mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor _ k ≅
      H ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ⋙
          sheafCompose (ProEt.topology (U.cover y))
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  have := U.weaklyEtale_proj y
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F ((ProEtale.upperStar Ab.{u + 1}
      (U.proj y)).mapDerivedCategoryHomologyFunctorIso k).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtale.upperStarCompSheafComposeForget₂Iso (U.proj y) Λ).symm)

open Pretriangulated in
/-- **The integral identification on the universal cover**, with the cohomology towers in
degrees `i - 1` and `i` of `F` identified on the base `Y` with the abelian towers underlying
`ν^* Hₙ` and `ν^* H'ₙ`, for towers of étale sheaves of `Λ`-modules with finite locally constant
underlying sheaves of sets: `Hⁱ(p^* R lim F) ≅ C(-, lim_n (H'ₙ)_y)` on `Ỹ_y`. -/
theorem UniversalCovers.nonempty_iso_homologyUpperStar_continuousMapAddSheaf'
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology Y) Ab.{u + 1})}
    {c : Cone F} (hc : IsHomotopyLimit c) (i : ℤ)
    (H H' : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) (hH' : ∀ n : ℕ, IsSetFLC (H'.obj (op n)))
    (e : F ⋙ DerivedCategory.homologyFunctor _ (i - 1) ≅
      H ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (e' : F ⋙ DerivedCategory.homologyFunctor _ i ≅
      H' ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :
    let St := (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have (n : ℕ) : Finite (St.obj (H'.obj (op n))) := (hH' n).finite_sheafFiber _
    Nonempty ((DerivedCategory.homologyFunctor _ i).obj
        ((ProEtale.upperStar Ab.{u + 1} (U.proj y)).mapDerivedCategory.obj c.pt) ≅
      ProEtale.continuousMapAddSheaf (U.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H'.obj (op n))))
          (fun n ↦ DiscreteShrink.map
            (St.map (H'.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom))) :=
  U.nonempty_iso_homologyUpperStar_continuousMapAddSheaf y hc i H H' hH hH'
    (U.homologyUpperStarTowerIso y F (i - 1) H e) (U.homologyUpperStarTowerIso y F i H' e')

end AlgebraicGeometry.Scheme
