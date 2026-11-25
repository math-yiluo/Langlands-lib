/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.AdicSystem
public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalModelRestriction

/-!

# The étale exchange restriction pulled back to the strictly local model

Let `M` be a strictly local model of a curve (`AlgebraicGeometry.Etale.CurveLocalModel`) and
`ι ≫ graph = d ≫ diagonal` a cartesian square with fixed scheme `F`. This file collects the
ingredients of the identification of the geometric stalk of the étale exchange restriction
`ρ_P` with the strictly local supported restriction
(`AlgebraicGeometry.Etale.CurveLocalModel.exists_geometricStalk_map_exchangeRestriction`):

* `AlgebraicGeometry.Etale.CurveLocalModel.exists_map_exchangeRestriction_τY`: the pullback
  `Lτ_Y^* ρ_P`, followed by the base change map of `Rd^!` and the comparison
  `Lτ_B^* LΔ^* ≅ Lb^* Lτ^*`, factors through the exchange restriction of the square
  `Y = G ×_T B` at `Lτ^* P`;
* `AlgebraicGeometry.Etale.CurveLocalModel.geometricStalkIso`: the geometric stalk at a point
  `z` of `F` over `y` is `RΓ(Y, Lτ_Y^* -)`, since `Y` is strictly local with closed point over
  `z`;
* `AlgebraicGeometry.Etale.exchangeRestriction_naturality`: the étale exchange restriction is
  natural.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Naturality

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {S C X F : Scheme.{u}} {c : C ⟶ S}
  {Δ : X ⟶ S} {ι : F ⟶ C} {d : F ⟶ X} [HasCompactification c] [HasCompactification d]
  [QuasiCompact d]

/-- The étale exchange restriction `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` is natural in `P`. -/
@[reassoc]
lemma exchangeRestriction_naturality (sq : IsPullback ι d c Δ)
    {P P' : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (f : P ⟶ P') :
    exchangeRestriction Λ sq P ≫
        (R(d)^![Λ]).map ((L((Δ)^*[ModuleCat.{u + 1} Λ])).map f) =
      (L((ι)^*[ModuleCat.{u + 1} Λ])).map ((R(c)^![Λ]).map f) ≫
        exchangeRestriction Λ sq P' :=
  ((mateEquiv _ _ (TwoSquare.mk _ _ _ _ (lowerShriekBaseChangeIso Λ sq).inv)).naturality
    f).symm

end Naturality

section Restriction

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- If the restriction maps `RΓ(S, K) ⟶ RΓ(S', p^* K)` along `p : S' ⟶ S` are isomorphisms,
they form a natural isomorphism `RΓ(S, -) ≅ RΓ(S', Lp^* -)`. -/
noncomputable def globalSectionsRestrictionIso {S S' : Scheme.{u}} (p : S' ⟶ S)
    [∀ K, IsIso (globalSectionsRestriction (A := ModuleCat.{u + 1} Λ) p K)] :
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S ≅
      L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S' :=
  NatIso.ofComponents
    (fun K ↦ asIso (globalSectionsRestriction p K) ≪≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S').mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ p).symm.app K))
    (fun {K K'} φ ↦ by
      have h := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p).inv.naturality φ
      dsimp only [Functor.comp_map, Functor.comp_obj] at h ⊢
      simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
        Category.assoc]
      rw [globalSectionsRestriction_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp, h])

end Restriction

namespace CurveLocalModel

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (M : CurveLocalModel k) {F : Scheme.{u}} {ι d : F ⟶ M.X} [IsClosedImmersion d]
  (hsq : IsPullback ι d M.graph (pullback.diagonal M.f))

/-- The comparison `Lτ_B^* LΔ^* ≅ Lb^* Lτ^*` of derived pullbacks along the two sides of the
square `τ_B ≫ diagonal = b ≫ τ`. -/
noncomputable def diagonalPullbackIso :
    L((pullback.diagonal M.f)^*[ModuleCat.{u + 1} Λ]) ⋙ L((M.τB)^*[ModuleCat.{u + 1} Λ]) ≅
      L((M.τ)^*[ModuleCat.{u + 1} Λ]) ⋙ L((M.b)^*[ModuleCat.{u + 1} Λ]) :=
  (leftDerivedUpperStarComp _ M.τB (pullback.diagonal M.f)).symm ≪≫
    leftDerivedUpperStarComp _ M.b M.τ (M.τB ≫ pullback.diagonal M.f) M.isPullback_τB.w

/-- The derived lower shriek `Ry_B_!` along the closed immersion `y_B : Y ⟶ B` is full. -/
instance full_rightDerivedLowerShriek_yB : (R(M.yB)_![ModuleCat.{u + 1} Λ]).Full :=
  have (Q : DerivedCategory (Sheaf M.Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((rightDerivedUpperShriekAdjunction Λ M.yB).unit.app Q) :=
    isIso_rightDerivedUpperShriekAdjunction_unit_app Λ M.yB Q
  have : IsIso (rightDerivedUpperShriekAdjunction Λ M.yB).unit :=
    NatIso.isIso_of_isIso_app _
  ((rightDerivedUpperShriekAdjunction Λ M.yB).fullyFaithfulLOfIsIsoUnit).full

/-- **The exchange restriction pulled back to the strictly local model**: `Lτ_Y^*` of the étale
exchange restriction `ρ_P` of the fixed square, followed by the base change map
`Lτ_Y^* Rd^! ⟶ Ry_B^! Lτ_B^*` and `Ry_B^!` of `Lτ_B^* LΔ^* ≅ Lb^* Lτ^*`, factors through the
exchange restriction of the square `Y = G ×_T B` at `Lτ^* P`
(`CategoryTheory.Adjunction.exists_map_mateEquiv_app_comp_eq`, `Ry_B_!` being full). -/
theorem exists_map_exchangeRestriction_τY
    (P : DerivedCategory (Sheaf (pullback M.f M.f).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ s : (L((M.τY hsq)^*[ModuleCat.{u + 1} Λ])).obj ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(M.graph)^![Λ]).obj P)) ⟶
        (L((M.ιY)^*[ModuleCat.{u + 1} Λ])).obj ((R(M.a)^![Λ]).obj
          ((L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj P)),
      (L((M.τY hsq)^*[ModuleCat.{u + 1} Λ])).map (exchangeRestriction Λ hsq P) ≫
          (rightDerivedUpperShriekBaseChangeMap Λ (M.isPullback_τY hsq)).app
            ((L((pullback.diagonal M.f)^*[ModuleCat.{u + 1} Λ])).obj P) ≫
          (R(M.yB)^![Λ]).map ((M.diagonalPullbackIso Λ).hom.app P) =
        s ≫ exchangeRestriction Λ M.isPullback_ιY ((L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj P) :=
  Adjunction.exists_map_mateEquiv_app_comp_eq
    (a := rightDerivedUpperShriekAdjunction Λ M.graph) (g := rightDerivedUpperShriekAdjunction Λ d)
    (ι := L((ι)^*[ModuleCat.{u + 1} Λ])) (Δ := L((pullback.diagonal M.f)^*[ModuleCat.{u + 1} Λ]))
    (σ := lowerShriekBaseChangeIso Λ hsq) (a' := rightDerivedUpperShriekAdjunction Λ M.a)
    (g' := rightDerivedUpperShriekAdjunction Λ M.yB) (ι' := L((M.ιY)^*[ModuleCat.{u + 1} Λ]))
    (Δ' := L((M.b)^*[ModuleCat.{u + 1} Λ])) (σ' := lowerShriekBaseChangeIso Λ M.isPullback_ιY)
    (T₂ := L((M.τ)^*[ModuleCat.{u + 1} Λ])) (TC := L((M.τG)^*[ModuleCat.{u + 1} Λ]))
    (TF := L((M.τY hsq)^*[ModuleCat.{u + 1} Λ])) (TX := L((M.τB)^*[ModuleCat.{u + 1} Λ]))
    (τc := lowerShriekBaseChangeIso Λ M.isPullback_τG)
    (τd := lowerShriekBaseChangeIso Λ (M.isPullback_τY hsq)) (τΔ := M.diagonalPullbackIso Λ) P

/-- **The geometric stalk at a point over `y` is computed on `Y`**: for a point `z` of the fixed
scheme over `y`, the geometric stalk `RΓ(Spec k, Lz^* -)` is `RΓ(Y, Lτ_Y^* -)`, as `Y` is
strictly local with closed point `t_Y` and `z = t_Y ≫ τ_Y`. -/
noncomputable def geometricStalkIso (z : Spec (.of k) ⟶ F) (hz : z ≫ d = M.y) :
    L((M.τY hsq)^*[ModuleCat.{u + 1} Λ]) ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.Y ≅
      geometricStalk Λ z :=
  Functor.isoWhiskerLeft _ (globalSectionsRestrictionIso M.tY) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarComp _ M.tY (M.τY hsq) z (M.eq_tY_comp_τY hsq z hz)).symm _

end CurveLocalModel

/-- **Bookkeeping for the stalk of the exchange restriction.** Let `ψ : T ⋙ Γ ≅ G` be a natural
isomorphism and `x : A₁ ⟶ A₂`. Suppose that `T(x)`, followed by maps `β` (with `Γ(β)`
invertible) and an isomorphism `γ`, factors as `s₁ ≫ ρ₁`; that `ρ₁` followed by an isomorphism
`δ` is `ε ≫ ρ₂`; and that `ρ = t ≫ r ≫ Γ(ζ ≫ ρ₂) ≫ e₂` with `t`, `r`, `ζ`, `e₂` isomorphisms.
Then `G(x)`, followed by an isomorphism, factors through `ρ`. -/
lemma exists_map_comp_eq_of_factorization {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟]
    [Category* ℰ] (T : 𝒞 ⥤ 𝒟) (Γ : 𝒟 ⥤ ℰ) (G : 𝒞 ⥤ ℰ) (ψ : T ⋙ Γ ≅ G) {A₁ A₂ : 𝒞}
    (x : A₁ ⟶ A₂) {B₀ B₁ B₂ B₃ B₄ B₅ : 𝒟} (β : T.obj A₂ ⟶ B₂) [IsIso (Γ.map β)] (γ : B₂ ⟶ B₃)
    [IsIso γ] (s₁ : T.obj A₁ ⟶ B₁) (ρ₁ : B₁ ⟶ B₃) (h₁ : T.map x ≫ β ≫ γ = s₁ ≫ ρ₁)
    (δ : B₃ ⟶ B₄) [IsIso δ] (ε : B₁ ⟶ B₅) (ρ₂ : B₅ ⟶ B₄) (h₂ : ρ₁ ≫ δ = ε ≫ ρ₂)
    (ζ : B₀ ⟶ B₅) [IsIso ζ] {S₁ S₂ G₀ : ℰ} (t : S₁ ≅ G₀) (r : G₀ ⟶ Γ.obj B₀) [IsIso r]
    (e₂ : Γ.obj B₄ ≅ S₂) (ρ : S₁ ⟶ S₂) (h₃ : ρ = t.hom ≫ r ≫ Γ.map (ζ ≫ ρ₂) ≫ e₂.hom) :
    ∃ (e : G.obj A₂ ≅ S₂) (s : G.obj A₁ ⟶ S₁), G.map x ≫ e.hom = s ≫ ρ := by
  refine ⟨ψ.symm.app A₂ ≪≫ asIso (Γ.map β) ≪≫ Γ.mapIso (asIso γ ≪≫ asIso δ) ≪≫ e₂,
    ψ.inv.app A₁ ≫ Γ.map (s₁ ≫ ε ≫ inv ζ) ≫ inv r ≫ t.inv, ?_⟩
  have hψ := ψ.inv.naturality x
  dsimp only [Functor.comp_map] at hψ
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom, Functor.mapIso_hom, h₃,
    Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
  rw [reassoc_of% hψ]
  congr 1
  simp only [← Functor.map_comp_assoc, Category.assoc, IsIso.inv_hom_id_assoc]
  rw [reassoc_of% h₁, h₂]

end AlgebraicGeometry.Etale
