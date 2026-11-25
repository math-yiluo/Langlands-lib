/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.LocalExchangeRestriction
public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalUpperShriek
public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalExchangeRestriction

/-!

# The stalk of the étale supported restriction at a fixed point

Let `M` be a strictly local model of a curve (`AlgebraicGeometry.Etale.CurveLocalModel`) and
`ι ≫ graph = d ≫ diagonal` a cartesian square, the fixed square of the transposed graph `(h, id)`
of `X ×_k X`, with fixed scheme `F` and a point `z` of `F` over the fixed point `y`. This file
proves that the geometric stalk at `z` of the étale exchange restriction
`ρ_P : Lι^* R(graph)^! P ⟶ Rd^! LΔ^* P` (`AlgebraicGeometry.Etale.exchangeRestriction`) factors,
through an identification of its target with `RΓ_Y(B, b^* P|_T)`, through the classical supported
restriction `ρ_{a,b}` on the strict localization `T` of `X ×_k X` at `(y, y)`
(`AlgebraicGeometry.Etale.sectionsWithSupportRestriction`). This is the identification of the
stalk of the supported restriction with the strictly local `ρ_{a,b}` used in blueprint
`lemma-local-term-restriction-map`.

The proof pulls the fixed square back along `τ : T ⟶ X ×_k X`
(`CategoryTheory.Adjunction.exists_map_mateEquiv_app_comp_eq`, with compact-support base
change for the closed immersions), uses that the exceptional pullback commutes with this pullback
on global sections over `Y`
(`CurveLocalModel.isIso_rightDerivedGlobalSections_map_rightDerivedUpperShriekBaseChangeMap`),
and compares with `ρ_{a,b}` on `T`
(`AlgebraicGeometry.Etale.CurveLocalModel.exists_sectionsWithSupportRestriction_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (M : CurveLocalModel k) {F : Scheme.{u}} {ι d : F ⟶ M.X} [IsClosedImmersion d]
  (hsq : IsPullback ι d M.graph (pullback.diagonal M.f))

/-- **The stalk of the étale supported restriction at a fixed point**: the geometric stalk at a
point `z` of the fixed scheme over `y` of the étale exchange restriction of the fixed square
factors, through an identification of its target with `RΓ_Y(B, b^* P|_T)`, through the classical
supported restriction `ρ_{a,b}` of `P|_T` on the strictly local model. -/
theorem exists_geometricStalk_map_exchangeRestriction (z : Spec (.of k) ⟶ F) (hz : z ≫ d = M.y)
    (P : DerivedCategory.Plus
      (Sheaf (pullback M.f M.f).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (e : (geometricStalk Λ z).obj ((R(d)^![Λ]).obj
          ((L((pullback.diagonal M.f)^*[ModuleCat.{u + 1} Λ])).obj P.obj)) ≅
        ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
          ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).obj
            ((Functor.mapDerivedCategoryPlus (M.τ)^*[ModuleCat.{u + 1} Λ]).obj P))).obj₁)
      (s : (geometricStalk Λ z).obj ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(M.graph)^![Λ]).obj P.obj)) ⟶
        ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj
          ((Functor.mapDerivedCategoryPlus (M.τ)^*[ModuleCat.{u + 1} Λ]).obj P)).obj₁),
      (geometricStalk Λ z).map (exchangeRestriction Λ hsq P.obj) ≫ e.hom =
        s ≫ sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB
          M.openComplement_yB_le
            ((Functor.mapDerivedCategoryPlus (M.τ)^*[ModuleCat.{u + 1} Λ]).obj P) := by
  obtain ⟨s₁, h₁⟩ := M.exists_map_exchangeRestriction_τY Λ hsq P.obj
  obtain ⟨t, e₂, h₃⟩ := M.exists_sectionsWithSupportRestriction_eq Λ
    ((Functor.mapDerivedCategoryPlus (M.τ)^*[ModuleCat.{u + 1} Λ]).obj P)
  let N : DerivedCategory.Plus (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨(L((pullback.diagonal M.f)^*[ModuleCat.{u + 1} Λ])).obj P.obj,
      DerivedCategory.TStructure.t.plus.prop_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ (pullback.diagonal M.f)).app P.obj).symm
        ((Functor.mapDerivedCategoryPlus
          (pullback.diagonal M.f)^*[ModuleCat.{u + 1} Λ]).obj P).property⟩
  have := M.isIso_rightDerivedGlobalSections_map_rightDerivedUpperShriekBaseChangeMap Λ hsq N
  have := M.isIso_globalSectionsRestriction_ιY ((R(M.a)^![Λ]).obj
    ((Functor.mapDerivedCategoryPlus (M.τ)^*[ModuleCat.{u + 1} Λ]).obj P).obj)
  let φ := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) M.τ).app P.obj
  exact exists_map_comp_eq_of_factorization _ _ _ (M.geometricStalkIso Λ hsq z hz) _ _
    ((R(M.yB)^![Λ]).map ((M.diagonalPullbackIso Λ).hom.app P.obj)) s₁ _ h₁
    ((R(M.yB)^![Λ]).map ((L((M.b)^*[ModuleCat.{u + 1} Λ])).map φ.hom))
    ((L((M.ιY)^*[ModuleCat.{u + 1} Λ])).map ((R(M.a)^![Λ]).map φ.hom)) _
    (exchangeRestriction_naturality Λ M.isPullback_ιY φ.hom)
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) M.ιY).inv.app _) t
    (globalSectionsRestriction M.ιY _) e₂ _ h₃

end AlgebraicGeometry.Etale.CurveLocalModel
