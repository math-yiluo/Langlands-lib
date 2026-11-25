/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension

/-!
# Stalks of lisse sheaves at geometric points with values in other fields

Let `Y` be a connected regular Noetherian scheme with the monodromy of lisse sheaves from
universal covers at the geometric points `t : Spec Ω̄₁ ⟶ Y`
(`AlgebraicGeometry.ProEtale.universalLisseMonodromy`), and let `η : Spec Ω ⟶ Y` be a geometric
point with values in another separably closed field, with a lift `ξ : Spec Ω ⟶ Ỹ_t` to the
universal cover at `t`. For a lisse sheaf `G`, restriction along `ξ` identifies the sections
`Γ(Ỹ_t, G) ≅ G_t` with `Γ(Spec Ω, η^* G)`
(`AlgebraicGeometry.ProEtale.liftStalkIso`). Under this identification:

* an automorphism `a` of `Spec Ω` over `Y` acts on `Γ(Spec Ω, η^* G)` as the monodromy of the
  loop `F_t ≅ F_η ≅ F_t` defined by the lifts `a ≫ ξ` and `ξ`
  (`AlgebraicGeometry.ProEtale.liftStalkIso_resOver`);
* for an endomorphism `f` of `Y`, a morphism `ψ : f^* G ⟶ G` and `a` with `a ≫ η = η ≫ f`, the
  transport of `Γ(Spec Ω, η^* G)` along the square `a ≫ η = η ≫ f` and `ψ` is the transport of
  `G_t` along the path `F_t ≅ F_{t ≫ f}` defined by the lifts `a ≫ ξ` and `ξ ≫ (Ỹ_t ⟶ Ỹ_{t ≫ f})`,
  followed by `G_{t ≫ f} = (f^* G)_t ⟶ G_t`
  (`AlgebraicGeometry.ProEtale.liftStalkIso_globalSectionsTransport`).

For `f` the Frobenius and `ψ` the Weil structure this compares the Frobenius at a generic
geometric point with the Weil fundamental representation (blueprint
`lemma-boundary-stalk--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

open Scheme Scheme.FiniteEtale

variable (l : ℕ) [Fact l.Prime] {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
  [IsRegular Y] [ConnectedSpace Y] {Ω₁ : Type u} [Field Ω₁] {Ω : Type u} [Field Ω]
  [IsSepClosed Ω]

local notation "𝒰" => Scheme.universalCovers Y Ω₁

/-- The restriction `Γ(Ỹ_t, p_t^* G) ⟶ Γ(Spec Ω, η^* G)` along a lift `ξ` of `η` to the universal
cover at `t`. -/
noncomputable def liftRes (t : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y) {η : Spec (.of Ω) ⟶ Y}
    (ξ : Spec (.of Ω) ⟶ (𝒰).cover t) (hξ : ξ ≫ (𝒰).proj t = η) :
    ((𝒰).proj t)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _ ⟶
      (η)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _ :=
  resOver _ ξ hξ

variable {l}

omit [IsSepClosed Ω] in
/-- The restriction along a lift is an isomorphism on lisse sheaves. -/
theorem isIso_liftRes_app (t : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y) {η : Spec (.of Ω) ⟶ Y}
    (ξ : Spec (.of Ω) ⟶ (𝒰).cover t) (hξ : ξ ≫ (𝒰).proj t = η)
    (G : LisseSheaf l Y) : IsIso ((liftRes l t ξ hξ).app G.obj.X) := by
  obtain ⟨n, ⟨E⟩⟩ := IsAdicLisseSheaf.exists_iso_upperStar_universalCover
    𝒰 t G.property
  have := (𝒰).connectedSpace t
  have h := isIso_globalSectionsToUpperStar_app_of_iso_biproduct ξ E
  rw [adicUpperStar_obj_X] at h
  rw [liftRes, resOver_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h inferInstance

/-- The identification `G_t ≅ Γ(Ỹ_t, p_t^* G) ≅ Γ(Spec Ω, η^* G)` of the stalk at `t` with the
sections at `η`, through a lift `ξ` of `η` to the universal cover at `t`. -/
noncomputable def liftStalkIso (t : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y) {η : Spec (.of Ω) ⟶ Y}
    (ξ : Spec (.of Ω) ⟶ (𝒰).cover t) (hξ : ξ ≫ (𝒰).proj t = η)
    (G : LisseSheaf l Y) :
    (lisseStalk l t).obj G ≅ (Sheaf.Γ _ _).obj ((η)^*[WeilCoefficients.{u} l].obj G.obj.X) :=
  have := Scheme.UniversalCovers.isIso_ptRes_app (U := 𝒰)
    (fun y G ↦ IsAdicLisseSheaf.exists_iso_upperStar_universalCover _ y G.property) t G
  have := isIso_liftRes_app t ξ hξ G
  (asIso (((𝒰).ptRes l t).app G.obj.X)).symm ≪≫
    asIso ((liftRes l t ξ hξ).app G.obj.X)

omit [IsSepClosed Ω] in
lemma ptRes_app_comp_liftStalkIso_hom (t : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y)
    {η : Spec (.of Ω) ⟶ Y} (ξ : Spec (.of Ω) ⟶ (𝒰).cover t)
    (hξ : ξ ≫ (𝒰).proj t = η) (G : LisseSheaf l Y) :
    ((𝒰).ptRes l t).app G.obj.X ≫ (liftStalkIso t ξ hξ G).hom =
      (liftRes l t ξ hξ).app G.obj.X := by
  simp [liftStalkIso]

omit [IsRegular Y] in
/-- The transport of the universal cover along the inverse path is the inverse transport. -/
lemma universalCover_transport_symm {t z : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y}
    (τ : fiber t ≅ fiber z) :
    (UniversalCover.transport τ.symm).hom = (UniversalCover.transport τ).inv :=
  rfl

/-- **Automorphisms of `Spec Ω` act through the monodromy.** For an automorphism `a` of `Spec Ω`
over `Y`, the restriction along `a` corresponds under `G_t ≅ Γ(Spec Ω, η^* G)` to the monodromy
of the loop `F_t ≅ F_η ≅ F_t` defined by the lifts `a ≫ ξ` and `ξ`. -/
theorem liftStalkIso_resOver (t : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y)
    {η : Spec (.of Ω) ⟶ Y} (ξ : Spec (.of Ω) ⟶ (𝒰).cover t)
    (hξ : ξ ≫ (𝒰).proj t = η) (a : Spec (.of Ω) ⟶ Spec (.of Ω)) (ha : a ≫ η = η)
    (haξ : (a ≫ ξ) ≫ (𝒰).proj t = η) (G : LisseSheaf l Y) :
    (liftStalkIso t ξ hξ G).hom ≫ (resOver _ a ha).app G.obj.X =
      ((universalLisseMonodromy l Y Ω₁).mono (UniversalCover.liftPath t (a ≫ ξ) haξ ≪≫
        (UniversalCover.liftPath t ξ hξ).symm)).hom.app G ≫ (liftStalkIso t ξ hξ G).hom := by
  have := Scheme.UniversalCovers.isIso_ptRes_app (U := 𝒰)
    (fun y G ↦ IsAdicLisseSheaf.exists_iso_upperStar_universalCover _ y G.property) t G
  set g := UniversalCover.liftPath t (a ≫ ξ) haξ ≪≫ (UniversalCover.liftPath t ξ hξ).symm
  rw [← cancel_epi (((𝒰).ptRes l t).app G.obj.X),
    reassoc_of% ptRes_app_comp_liftStalkIso_hom]
  erw [reassoc_of% (Scheme.UniversalCovers.ptRes_app_comp_monoIso_hom_app
    (U := 𝒰)
    (fun y G ↦ IsAdicLisseSheaf.exists_iso_upperStar_universalCover _ y G.property) g G)]
  -- `a ≫ ξ = ξ ≫ (transport g)⁻¹`
  have hp : a ≫ ξ = ξ ≫ ((𝒰).transport g).inv := by
    have h := UniversalCover.comp_transport_liftPath ξ hξ (a ≫ ξ) haξ
    rw [← h]
    congr 2
  have e₁ : (a ≫ ξ) ≫ (𝒰).proj t = η := haξ
  have e₂ : (ξ ≫ ((𝒰).transport g).inv) ≫ (𝒰).proj t = η := hp ▸ haξ
  have e₃ : ((𝒰).transport g).inv ≫ (𝒰).proj t =
      (𝒰).proj t := by
    rw [Iso.inv_comp_eq, (𝒰).transport_proj]
  rw [ptRes_app_comp_liftStalkIso_hom, Scheme.UniversalCovers.transportRes_hom_app, liftRes]
  erw [resOver_comp _ ξ ((𝒰).transport g).inv hξ e₃ e₂,
    resOver_comp _ a ξ ha hξ e₁]
  exact congrArg (fun F ↦ F.app G.obj.X) (resOver_congr _ hp e₁ e₂)

omit [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] [IsSepClosed Ω] in
/-- The transport along `a ≫ η = η ≫ f` and `ψ`, after the restriction along `ξ : S ⟶ P` over
`Y`, is the restriction along `T : P' ⟶ P`, the transport along `m : P ⟶ P'` over `f` with `ψ`,
and the restriction along `ξ`, if `a ≫ ξ = ξ ≫ m ≫ T`. -/
lemma resOver_comp_globalSectionsTransport {S P P' : Scheme.{u}} {η : S ⟶ Y} (ξ : S ⟶ P)
    {pr : P ⟶ Y} {pr' : P' ⟶ Y} (hξ : ξ ≫ pr = η) (f : Y ⟶ Y) (a : S ⟶ S)
    (ha : a ≫ η = η ≫ f) (m : P ⟶ P') (hm : m ≫ pr' = pr ≫ f) (T : P' ⟶ P)
    (hT : T ≫ pr = pr') (hδ : a ≫ ξ = ξ ≫ m ≫ T)
    (G : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l))
    (ψ : (f)^*[WeilCoefficients.{u} l].obj G ⟶ G) :
    (resOver _ ξ hξ).app G ≫ globalSectionsTransport _ ha ψ =
      (resOver _ T hT).app G ≫ globalSectionsTransport _ hm (𝟙 _) ≫
        (Sheaf.Γ _ _).map ((pr)^*[_].map ψ) ≫ (resOver _ ξ hξ).app G := by
  have hψr : (upperStarComp _ f (𝟙 Y)).hom.app G ≫ (f)^*[_].map ((upperStarId _ Y).hom.app G) ≫
      ψ = (upperStarCongr _ (Category.comp_id f)).hom.app G ≫ ψ := by
    rw [reassoc_of% upperStarComp_id_right_hom_app]
  have hψl : (upperStarComp _ (𝟙 Y) f).hom.app G ≫ ((𝟙 Y))^*[_].map ψ ≫
      (upperStarId _ Y).hom.app G = (upperStarCongr _ (Category.id_comp f)).hom.app G ≫ ψ := by
    have n := (upperStarId (WeilCoefficients.{u} l) Y).hom.naturality ψ
    simp only [Functor.id_map] at n
    rw [n, reassoc_of% upperStarComp_id_left_hom_app]
  have hξ' : ξ ≫ pr = η ≫ 𝟙 Y := hξ.trans (Category.comp_id η).symm
  have e₃ : T ≫ pr = pr' ≫ 𝟙 Y := hT.trans (Category.comp_id _).symm
  have h₁ : (a ≫ ξ) ≫ pr = η ≫ f := by rw [Category.assoc, hξ, ha]
  have h₂ : (m ≫ T) ≫ pr = pr ≫ f := by rw [Category.assoc, hT, hm]
  have h₃ : (ξ ≫ m ≫ T) ≫ pr = η ≫ f := by rw [Category.assoc, h₂, ← Category.assoc, hξ]
  have hM : globalSectionsTransport _ hm (𝟙 _) ≫ (Sheaf.Γ _ _).map ((pr)^*[_].map ψ) =
      globalSectionsTransport _ hm ψ := by
    rw [globalSectionsTransport, globalSectionsTransport, CategoryTheory.Functor.map_id]
    simp only [Category.assoc, ← Functor.map_comp]
    rfl
  rw [resOver_app_eq_transport, resOver_app_eq_transport,
    globalSectionsTransport_comp_eq _ hξ' ha h₁ rfl (Category.comp_id f) _ _ ψ hψr,
    reassoc_of% hM, reassoc_of% (globalSectionsTransport_comp_eq _ e₃ hm h₂ rfl
      (Category.comp_id f) _ _ ψ hψr),
    globalSectionsTransport_comp_eq _ h₂ hξ' h₃ rfl (Category.id_comp f) _ _ ψ hψl]
  exact globalSectionsTransport_congr_left _ h₁ hδ ψ

/-- **The Frobenius-type transport at `η` and the monodromy.** For an endomorphism `f` of `Y`,
`ψ : f^* G ⟶ G` and `a : Spec Ω ⟶ Spec Ω` with `a ≫ η = η ≫ f`, the transport of
`Γ(Spec Ω, η^* G)` along `a ≫ η = η ≫ f` and `ψ` corresponds under `G_t ≅ Γ(Spec Ω, η^* G)` to the
monodromy along the path `F_t ≅ F_η ≅ F_{t ≫ f}` defined by the lifts `a ≫ ξ` and
`ξ ≫ (Ỹ_t ⟶ Ỹ_{t ≫ f})`, followed by `G_{t ≫ f} = (f^* G)_t ⟶ G_t`. -/
theorem liftStalkIso_globalSectionsTransport (t : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y)
    {η : Spec (.of Ω) ⟶ Y} (ξ : Spec (.of Ω) ⟶ (𝒰).cover t)
    (hξ : ξ ≫ (𝒰).proj t = η) (f : Y ⟶ Y) (a : Spec (.of Ω) ⟶ Spec (.of Ω))
    (ha : a ≫ η = η ≫ f) (haξ : (a ≫ ξ) ≫ (𝒰).proj t = η ≫ f)
    (hmap : (ξ ≫ (𝒰).map f t) ≫ (𝒰).proj (t ≫ f) = η ≫ f)
    (G : LisseSheaf l Y) (ψ : (f)^*[WeilCoefficients.{u} l].obj G.obj.X ⟶ G.obj.X) :
    (liftStalkIso t ξ hξ G).hom ≫ globalSectionsTransport _ ha ψ =
      ((universalLisseMonodromy l Y Ω₁).mono (UniversalCover.liftPath t (a ≫ ξ) haξ ≪≫
        (UniversalCover.liftPath (t ≫ f) (ξ ≫ (𝒰).map f t) hmap).symm)).hom.app G ≫
        (upperStarStalkIso l f t G.obj.X).hom ≫ (stalkFunctor l t).map ψ ≫
        (liftStalkIso t ξ hξ G).hom := by
  have hU : ∀ (y : Spec (.of (AlgebraicClosure Ω₁)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
      Nonempty (((𝒰).proj y)^*ᵃ[l].obj G.obj ≅
        ⨁ fun _ : Fin n ↦ AdicSheaf.unit l ((𝒰).cover y)) :=
    fun y G ↦ IsAdicLisseSheaf.exists_iso_upperStar_universalCover _ y G.property
  have := Scheme.UniversalCovers.isIso_ptRes_app (U := 𝒰) hU t G
  set δ := UniversalCover.liftPath t (a ≫ ξ) haξ ≪≫
    (UniversalCover.liftPath (t ≫ f) (ξ ≫ (𝒰).map f t) hmap).symm
  have hδ : a ≫ ξ = ξ ≫ (𝒰).map f t ≫ ((𝒰).transport δ).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact UniversalCover.comp_transport_liftPath (a ≫ ξ) haξ (ξ ≫ (𝒰).map f t) hmap
  have nat : ((𝒰).ptRes l t).app ((f)^*[_].obj G.obj.X) ≫
      (stalkFunctor l t).map ψ = (Sheaf.Γ _ _).map (((𝒰).proj t)^*[_].map ψ) ≫
        ((𝒰).ptRes l t).app G.obj.X :=
    (((𝒰).ptRes l t).naturality ψ).symm
  rw [← cancel_epi (((𝒰).ptRes l t).app G.obj.X),
    reassoc_of% ptRes_app_comp_liftStalkIso_hom]
  erw [reassoc_of% (Scheme.UniversalCovers.ptRes_app_comp_monoIso_hom_app
    (U := 𝒰) hU δ G)]
  rw [reassoc_of% (Scheme.UniversalCovers.ptRes_app_comp_upperStarStalkIso
      (U := 𝒰) (l := l) f t G.obj.X)]
  erw [reassoc_of% nat]
  rw [ptRes_app_comp_liftStalkIso_hom]
  exact resOver_comp_globalSectionsTransport ξ hξ f a ha _ ((𝒰).map_proj f t) _
    (by rw [Iso.inv_comp_eq, (𝒰).transport_proj]) hδ G.obj.X ψ

end AlgebraicGeometry.ProEtale
