/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineKernelAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-!
# Trace counits of `Rf_*` and of `Rf_!`

Let `f : X ⟶ Y` be proper, at finite coefficients. An adjunction `Rf_* ⊣ T' ⊗ᴸ Lf^*(-)` whose
counit is the trace counit `CategoryTheory.Adjunction.traceCounit` of `Lf^* ⊣ Rf_*` (for the
monoidal structure `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`) gives, through
`Rf_! ≅ Rf_*`, an isomorphism `T' ≅ T` and an isomorphism `G ≅ T ⊗ᴸ Lf^*(-)`, an adjunction
`Rf_! ⊣ G` whose counit is
`Rf_!(G K) ≅ Rf_!(T ⊗ᴸ Lf^* K) ≅ Rf_! T ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`, built from the projection map of
`Rf_!` (`AlgebraicGeometry.Etale.exists_adjunction_lowerShriek_of_traceCounit`). This is the
form of the counit `AlgebraicGeometry.Etale.lowerShriekTraceCounit` of the projective line.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- Search the braiding of `ModuleCat Λ` through its symmetric structure and braid étale sheaves
-- through `Etale.sheafBraidedCategory`, as the generic definitions of the derived tensor product
-- do, and as in `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunction`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, so that the
-- generic statements on the projection map specialise syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

attribute [local instance] leftDerivedUpperStarMonoidal

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- The projection map of `Rp_*` is the projection map of `Lp^* ⊣ Rp_*`, for the monoidal
structure of the derived category found through the symmetric structure of `ModuleCat Λ`. -/
lemma rightDerivedLowerStarProjectionMap_app_app_eq_monoidalProjection_moduleCat
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) p).app M).app L =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).monoidalProjection M L :=
  rfl

/-- The projection formula for the derived pushforward along a proper morphism, at finite
coefficients, in the form `CategoryTheory.Adjunction.monoidalProjection`, for the monoidal
structure of the derived category found through the symmetric structure of `ModuleCat Λ`. -/
instance isIso_monoidalProjection_of_isProper_moduleCat {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsProper p] (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).monoidalProjection M L) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ p
  rw [← rightDerivedLowerStarProjectionMap_app_app_eq_monoidalProjection_moduleCat]
  infer_instance

omit [Finite Λ] in
/-- For proper `f`, the projection map of `Rf_!` followed by `Rf_! ≅ Rf_*` is `Rf_! ≅ Rf_*`
followed by the projection map `CategoryTheory.Adjunction.monoidalProjection` of `Lf^* ⊣ Rf_*`. -/
lemma projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar_eq_monoidalProjection
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((projectionMap (ModuleCat.{u + 1} Λ) f).app T).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).hom.app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj T).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).hom.app T ▷ K ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).monoidalProjection T K := by
  have h := projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) f T K
  rw [rightDerivedLowerStarProjectionMap_app_app_eq_monoidalProjection_moduleCat,
    derivedTensor_map_app] at h
  exact h

/-- **Trace counits of `Rf_!` from trace counits of `Rf_*`.** Let `f : X ⟶ Y` be proper, `T` an
object of `D(X)` with a trace `t : Rf_! T ⟶ Λ_Y`, `G` a functor with `γ : G ≅ T ⊗ᴸ Lf^*(-)`, and
`θ : T' ≅ T`. If `Rf_*` is left adjoint to `T' ⊗ᴸ Lf^*(-)` with counit the trace counit of the
trace `Rf_* T' ≅ Rf_* T ≅ Rf_! T ⟶ Λ_Y`, then `Rf_!` is left adjoint to `G`, with counit
`Rf_!(G K) ≅ Rf_!(T ⊗ᴸ Lf^* K) ≅ Rf_! T ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`. -/
theorem exists_adjunction_lowerShriek_of_traceCounit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (T T' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (θ : T' ≅ T) (t : (R(f)_![ModuleCat.{u + 1} Λ]).obj T ⟶ 𝟙_ _)
    {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : G ≅ L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj T)
    (adj₀ : R((f)_*[ModuleCat.{u + 1} Λ]) ⊣ L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ tensorLeft T')
    (h₀ : adj₀.counit = (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).traceCounit
      T' ((R((f)_*[ModuleCat.{u + 1} Λ])).map θ.hom ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).inv.app T ≫ t)) :
    haveI := isIso_projectionMap_of_finite Λ f
    ∃ adj : R(f)_![ModuleCat.{u + 1} Λ] ⊣ G, ∀ K, adj.counit.app K =
      (R(f)_![ModuleCat.{u + 1} Λ]).map (γ.hom.app K) ≫
        inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app T).app K) ≫ t ▷ K ≫ (λ_ K).hom := by
  have := isIso_projectionMap_of_finite Λ f
  set φ := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f
  set adjf := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  refine ⟨(adj₀.ofNatIsoLeft φ.symm).ofNatIsoRight
    (Functor.isoWhiskerLeft _ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).mapIso θ) ≪≫ γ.symm),
    fun K => ?_⟩
  have hT {Z : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (h : (R((f)_*[ModuleCat.{u + 1} Λ])).obj T' ⊗ K ⟶ Z) :
      (R((f)_*[ModuleCat.{u + 1} Λ])).map (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map θ.inv).app
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫ inv (adjf.monoidalProjection T' K) ≫ h =
        inv (adjf.monoidalProjection T K) ≫ (R((f)_*[ModuleCat.{u + 1} Λ])).map θ.inv ▷ K ≫ h := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [derivedTensor_map_app, IsIso.comp_inv_eq,
      Category.assoc, adjf.monoidalProjection_naturality_left, IsIso.inv_hom_id_assoc]
  have hφ {Z : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (h : (R((f)_*[ModuleCat.{u + 1} Λ])).obj T ⊗ K ⟶ Z) :
      φ.hom.app (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj T).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫ inv (adjf.monoidalProjection T K) ≫ h =
        inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app T).app K) ≫ φ.hom.app T ▷ K ≫ h := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [IsIso.eq_inv_comp, ← Category.assoc,
      IsIso.comp_inv_eq,
      projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar_eq_monoidalProjection]
  have hn {Z : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (h : (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ tensorLeft T').obj K) ⟶ Z) :
      (R(f)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map θ.inv).app
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
          φ.hom.app ((L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ tensorLeft T').obj K) ≫ h =
        φ.hom.app (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj T).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
          (R((f)_*[ModuleCat.{u + 1} Λ])).map (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map θ.inv).app
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫ h := by
    rw [← Category.assoc, ← Category.assoc]
    exact φ.hom.naturality _ =≫ h
  simp only [Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft, h₀, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, Functor.mapIso_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    Iso.symm_hom, Adjunction.traceCounit_app]
  congr 1
  rw [hn, hT, hφ, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc,
    ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

end Etale

end AlgebraicGeometry
