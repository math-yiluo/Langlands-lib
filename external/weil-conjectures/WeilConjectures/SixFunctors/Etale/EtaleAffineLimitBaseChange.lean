/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange

/-!
# Base change along a limit of étale morphisms

Let `D : I ⥤ Scheme` be a cofiltered diagram with affine étale transition maps and `c` a limit
cone of `D`. For a stage `i` and an open `V ⊆ Dᵢ`, the projection `c.pt ⊇ πᵢ⁻¹(V) ⟶ V` is the
limit of the étale `V`-schemes `Dⱼ ⊇ D(j ⟶ i)⁻¹(V)`, `j ⟶ i`
(`AlgebraicGeometry.isLimitOpensCone`). Smooth base change in the limit form (blueprint
`corollary-open-direct-image-over-field--2`,
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth'`) therefore holds along it:
the base change maps `π⁻¹ R^q g_* F ⟶ R^q g'_* F'` are isomorphisms for quasi-compact
quasi-separated `g : T ⟶ V` and sheaves `F` which are torsion of orders invertible on `V` (blueprint
`lemma-punctured-surface-punctured-curve--1`, base change to a local chart of an étale limit of
surfaces).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- **Base change along a limit of étale morphisms.** Let `D` be a cofiltered diagram of
schemes with affine étale transition maps, `c` a limit cone, `i` a stage and `V ⊆ Dᵢ` open.
For a Cartesian square of a quasi-compact quasi-separated `g : T ⟶ V` along the projection
`πᵢ⁻¹(V) ⟶ V`, the base change maps of sheaves which are torsion of orders invertible on `V` are
isomorphisms. -/
theorem isIso_baseChangeHomologyMap_of_isLimit_of_etale (Λ : Type (u + 1)) [CommRing Λ]
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (hD : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Etale (D.map f)) (c : Cone D)
    (hc : IsLimit c) (i : I) (V : (D.obj i).Opens) {T Y : Scheme.{u}} (g : T ⟶ V)
    [QuasiCompact g] [QuasiSeparated g] {e : Y ⟶ T} {h : Y ⟶ c.π.app i ⁻¹ᵁ V}
    (sq : IsPullback e h g (c.π.app i ∣_ V)) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder V F] :
    IsIso (baseChangeHomologyMap Λ sq q F) := by
  let p : opensDiagram D i V ⟶ (Functor.const (Over i)).obj V.toScheme :=
    { app j := D.map j.hom ∣_ V
      naturality j k f := by
        simp only [opensDiagram_map, Functor.const_obj_obj,
          Functor.const_obj_map, Category.comp_id, ← Scheme.Hom.resLE_eq_morphismRestrict,
          Scheme.Hom.resLE_comp_resLE, ← Functor.map_comp, Over.w f] }
  have (j : Over i) : AlgebraicGeometry.Etale (D.map j.hom) := hD j.hom
  have (j : Over i) : Smooth (p.app j) := inferInstanceAs (Smooth (D.map j.hom ∣_ V))
  have (j : Over i) : QuasiCompact (p.app j) := inferInstanceAs (QuasiCompact (D.map j.hom ∣_ V))
  have (j : Over i) : QuasiSeparated (p.app j) :=
    inferInstanceAs (QuasiSeparated (D.map j.hom ∣_ V))
  refine isIso_baseChangeHomologyMap_of_isLimit_smooth' Λ g (opensDiagram D i V) p
    (isLimitOpensCone D c hc i V) (c.π.app i ∣_ V) (fun j ↦ ?_) sq q F
  simp only [opensCone_π_app, p, ← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_comp_resLE, Cone.w]

end AlgebraicGeometry.Etale
