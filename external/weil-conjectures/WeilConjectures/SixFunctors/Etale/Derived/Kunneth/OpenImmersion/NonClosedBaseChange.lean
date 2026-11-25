/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.NonClosedLimit
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Base change along open immersions: base change to a strict localization

Two inputs of the "stalks over points with positive transcendence degree" part of the proof of
blueprint `corollary-open-direct-image-over-field--2`:

* `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization`: the
  base change `W' = W ×_S S_(s) ⟶ W` of the strict localization `S_(s) ⟶ S` at a geometric
  point is a limit of étale `W`-schemes, so smooth base change in the limit form (blueprint
  `corollary-open-direct-image-over-field--2`) holds along it.
* `AlgebraicGeometry.Etale.isIso_sheafFiber_map_of_isIso_upperStar`: if the pullback of a map
  of sheaves along `u : W' ⟶ W` is an isomorphism and the geometric point of `W` at `z` lifts
  to `W'`, then the map is an isomorphism on the geometric stalk at `z` (blueprint
  `lem-kun-stalk-as-pullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Smooth base change along the base change of a strict localization (blueprint
`corollary-open-direct-image-over-field--2`): let `s` be a geometric point of a quasi-separated
scheme `S`, `f : W ⟶ S` a morphism and `W' = W ×_S S_(s)`. The projection `W' ⟶ W` is the limit of
the étale `W`-schemes `W ×_S V` for the affine pointed étale neighbourhoods `(V, v)` of `s`, so the
base change maps along `W' ⟶ W` of a quasi-compact quasi-separated `g : T ⟶ W` are isomorphisms for
sheaves which are torsion of orders invertible on `W`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization {S : Scheme.{u}}
    [QuasiSeparatedSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {W W' : Scheme.{u}} (f : W ⟶ S) (uW : W' ⟶ W) (r : W' ⟶ strictLocalization s)
    (hW' : IsPullback uW r f (strictLocalizationToBase s)) {T Y : Scheme.{u}} (g : T ⟶ W)
    [QuasiCompact g] [QuasiSeparated g] {e : Y ⟶ T} {h : Y ⟶ W'} (sq : IsPullback e h g uW)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder W F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let I₀ := InitiallySmall.CofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood s)
  let ι₀ := InitiallySmall.fromCofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood s)
  have : IsConnected I₀ := IsCofiltered.isConnected _
  let D₀ := ι₀ ⋙ affineNeighborhoodDiagramOver s
  let cO := (strictLocalizationConeOver s).whisker ι₀
  have hcO : IsLimit cO :=
    (Functor.Initial.isLimitWhiskerEquiv ι₀ _).symm (isLimitStrictLocalizationConeOver s)
  let cD := (CategoryTheory.Over.forget S).mapCone cO
  have hcD : IsLimit cD := isLimitOfPreserves (CategoryTheory.Over.forget S) hcO
  let w : D₀ ⋙ CategoryTheory.Over.forget S ⟶ (Functor.const I₀).obj S :=
    { app k := (D₀.obj k).hom
      naturality k k' a := (CategoryTheory.Over.w (D₀.map a)).trans (Category.comp_id _).symm }
  have hw (k : I₀) : cD.π.app k ≫ w.app k = strictLocalizationToBase s :=
    CategoryTheory.Over.w (cO.π.app k)
  let cP := constPullbackCone f w cD uW r hw hW'.w
  have hP : IsLimit cP := isLimitConstPullbackCone f w hcD uW r hw hW'
  let P := pullback ((Functor.const I₀).map f) w
  let D' : I₀ ⥤ CategoryTheory.Over W :=
    P.toOver W (fun k ↦ (pullback.fst ((Functor.const I₀).map f) w).app k)
      (fun a ↦ ((pullback.fst ((Functor.const I₀).map f) w).naturality a).trans
        (Category.comp_id _))
  let c' : Cone D' :=
    { pt := CategoryTheory.Over.mk uW
      π :=
        { app k := CategoryTheory.Over.homMk (cP.π.app k)
            (constPullbackCone_π_app_fst f w cD uW r hw hW'.w k)
          naturality k k' a := CategoryTheory.Over.OverMorphism.ext (cP.π.naturality a) } }
  have hc' : IsLimit ((CategoryTheory.Over.forget W).mapCone c') := hP
  have hiso (k : I₀) := isPullback_pullback_evaluation ((Functor.const I₀).map f) w k
  have haffk (k : I₀) : IsAffine ((D₀ ⋙ CategoryTheory.Over.forget S).obj k) := (ι₀.obj k).2
  have hét (k : I₀) : Etale (w.app k) := (ι₀.obj k).obj.1.prop
  have hqsS (k : I₀) : QuasiSeparatedSpace (((Functor.const I₀).obj S).obj k) :=
    inferInstanceAs (QuasiSeparatedSpace S)
  have hsm (k : I₀) : Smooth (D'.obj k).hom :=
    MorphismProperty.of_isPullback (P := @Smooth) (hiso k).flip inferInstance
  have hqc (k : I₀) : QuasiCompact (D'.obj k).hom :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hiso k).flip
      (quasiCompact_of_compactSpace _)
  have hqs (k : I₀) : QuasiSeparated (D'.obj k).hom :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (hiso k).flip
      (QuasiSeparated.of_quasiSeparatedSpace _)
  have haff {k k' : I₀} (a : k ⟶ k') : IsAffineHom (D'.map a).left :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_map_pullback_const f w a).flip (isAffineHom_of_isAffine _)
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth Λ g D' c' hc' (h := h) sq q F

/-- Stalks are computed by pullback (blueprint `lem-kun-stalk-as-pullback`): if the pullback
along `u : W' ⟶ W` of a morphism `φ` of sheaves on `W` is an isomorphism and the geometric point
of `W` at `z` factors through `u`, then `φ` is an isomorphism on the geometric stalk at `z`. -/
theorem Etale.isIso_sheafFiber_map_of_isIso_upperStar {W W' : Scheme.{u}} (uX : W' ⟶ W)
    {F G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    (hφ : IsIso (((uX)^*[ModuleCat.{u + 1} Λ]).map φ)) (z : W)
    (z' : Spec (.of (AlgebraicClosure (W.residueField z))) ⟶ W')
    (hz' : z' ≫ uX = W.algClosurePoint z) :
    IsIso ((W.uliftPointSmallEtale z).sheafFiber.map φ) := by
  rw [uliftPointSmallEtale, ← hz']
  refine (NatIso.isIso_map_iff
    (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) uX z') φ).1 ?_
  rw [Functor.comp_map]
  infer_instance

end AlgebraicGeometry
