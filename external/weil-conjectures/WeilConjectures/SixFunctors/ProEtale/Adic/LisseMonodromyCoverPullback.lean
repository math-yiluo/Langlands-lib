/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCover

/-!
# Monodromies from universal covers and pullback

Let `f : Y' ⟶ Y` be a morphism of connected schemes with universal profinite étale covers `U'`
on `Y'` and `U` on `Y`, related by a morphism of universal covers `Ỹ'_y ⟶ Ỹ_{y ≫ f}` over `f`
(`AlgebraicGeometry.Scheme.UniversalCovers.Hom`). Then the monodromies of lisse sheaves
obtained from `U` and `U'` (`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy`) are
compatible with `f`: under the identification `G_{y ≫ f} ≅ (f^* G)_y`, the transport along the
path `F_{y ≫ f} ≅ F_{z ≫ f}` induced by a path `τ : F_y ≅ F_z` of `Y'` is the transport of
`f^* G` along `τ`
(`AlgebraicGeometry.Scheme.UniversalCovers.Hom.lisseMonodromy_mono_upperStar`). This generalises
`AlgebraicGeometry.Scheme.UniversalCovers.monoIso_upperStar`, the case of an endomorphism of `Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.UniversalCovers.Hom

open ProEtale FiniteEtale

variable (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω] {f : Y' ⟶ Y}
  {U' : Scheme.UniversalCovers Y' Ω} {U : Scheme.UniversalCovers Y Ω} (φ : U'.Hom f U)

/-- The comparison `Γ(Ỹ_{y ≫ f}, p_{y ≫ f}^* F) ⟶ Γ(Ỹ'_y, p'_y^* f^* F)` along the morphism
`Ỹ'_y ⟶ Ỹ_{y ≫ f}` over `f`. -/
noncomputable def mapRes (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y')
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).obj ((U.proj (y ≫ f))^*[WeilCoefficients.{u} l].obj F) ⟶
      (Sheaf.Γ _ _).obj ((U'.proj y)^*[WeilCoefficients.{u} l].obj ((f)^*[_].obj F)) :=
  globalSectionsTransport _ (φ.map_proj y) (𝟙 _)

/-- The restriction to the base point over `y ≫ f`, followed by
`Γ(Spec Ω̄, (y ≫ f)^* F) ≅ Γ(Spec Ω̄, y^* f^* F)`, is the comparison along `Ỹ'_y ⟶ Ỹ_{y ≫ f}`
followed by the restriction to the base point over `y`. -/
lemma ptRes_app_comp_upperStarStalkIso (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y')
    (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.ptRes l (y ≫ f)).app F ≫ (upperStarStalkIso l f y F).hom =
      φ.mapRes l y F ≫ (U'.ptRes l y).app ((f)^*[_].obj F) := by
  have h₀ : U.pt (y ≫ f) ≫ U.proj (y ≫ f) = y ≫ f := U.pt_proj _
  rw [ptRes_app, ptRes_app, resOver_app_eq_transport, resOver_app_eq_transport, mapRes]
  refine Eq.trans ?_ (globalSectionsTransport_comp_eq _ _ _ h₀ (φ.pt_map y)
    (Category.id_comp f) _ _ (𝟙 _) ?_).symm
  · rw [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, globalSectionsTransport,
      globalSectionsTransport, Category.assoc, ← Functor.map_comp]
    refine congrArg (_ ≫ ·) (congrArg (Sheaf.Γ _ _).map ?_)
    rw [upperStarCompIso_hom_app, upperStarCompIso_hom_app]
    simp only [CategoryTheory.Functor.map_id, Category.assoc]
    rw [reassoc_of% upperStarComp_id_right_hom_app,
      reassoc_of% (upperStarCongr_hom_app_comp_hom_app _ _ _ h₀ F)]
    exact (Category.comp_id _).symm
  · simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    exact upperStarComp_id_left_hom_app _ f F

/-- The comparisons along `Ỹ'_y ⟶ Ỹ_{y ≫ f}` intertwine the transports along a path of `Y'` and
along the induced path of `Y`. -/
lemma transportRes_hom_app_comp_mapRes {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'}
    (τ : fiber y ≅ fiber z) (F : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (U.transportRes l (pullbackPathIso f τ)).hom.app F ≫ φ.mapRes l z F =
      φ.mapRes l y F ≫ (U'.transportRes l τ).hom.app ((f)^*[_].obj F) := by
  have hτ : (U'.transport τ).inv ≫ φ.map y =
      φ.map z ≫ (U.transport (pullbackPathIso f τ)).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, φ.map_transport, Iso.inv_hom_id_assoc]
  have h'' : (φ.map z ≫ (U.transport (pullbackPathIso f τ)).inv) ≫ U.proj (y ≫ f) =
      U'.proj z ≫ f := by
    rw [Category.assoc, U.transport_inv_proj, φ.map_proj]
  rw [transportRes_hom_app, transportRes_hom_app, resOver_app_eq_transport,
    resOver_app_eq_transport, mapRes, mapRes]
  refine (globalSectionsTransport_comp_eq _ _ _ h'' rfl (Category.comp_id f) _ _ (𝟙 _) ?_).trans
    (globalSectionsTransport_comp_eq _ _ _ h'' hτ (Category.id_comp f) _ _ (𝟙 _) ?_).symm
  · simp only [Category.comp_id]
    exact upperStarComp_id_right_hom_app _ f F
  · simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    exact upperStarComp_id_left_hom_app _ f F

variable {l}

/-- **Monodromies from related universal covers are compatible with pullback**: the transport
of stalks along the path `F_{y ≫ f} ≅ F_{z ≫ f}` induced by a path `τ : F_y ≅ F_z` of `Y'` is,
under the identifications `G_{y ≫ f} ≅ (f^* G)_y`, the transport of `f^* G` along `τ`. -/
lemma lisseMonodromy_mono_upperStar (φ : U'.Hom f U)
    (hU : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
      Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)))
    (hU' : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y') (G : LisseSheaf l Y'), ∃ n : ℕ,
      Nonempty ((U'.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U'.cover y)))
    {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'} (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y) :
    ((U.lisseMonodromy hU).mono (pullbackPathIso f τ)).hom.app G ≫
        (upperStarStalkIso l f z G.obj.X).hom =
      (upperStarStalkIso l f y G.obj.X).hom ≫
        ((U'.lisseMonodromy hU').mono τ).hom.app (G.upperStar l f) := by
  have := isIso_ptRes_app hU (y ≫ f) G
  rw [lisseMonodromy_mono, lisseMonodromy_mono, ← cancel_epi ((U.ptRes l (y ≫ f)).app G.obj.X),
    reassoc_of% ptRes_app_comp_monoIso_hom_app, φ.ptRes_app_comp_upperStarStalkIso l,
    reassoc_of% (φ.ptRes_app_comp_upperStarStalkIso l),
    reassoc_of% (φ.transportRes_hom_app_comp_mapRes l)]
  exact congrArg (φ.mapRes l y G.obj.X ≫ ·)
    (ptRes_app_comp_monoIso_hom_app hU' τ (G.upperStar l f)).symm

end AlgebraicGeometry.Scheme.UniversalCovers.Hom
