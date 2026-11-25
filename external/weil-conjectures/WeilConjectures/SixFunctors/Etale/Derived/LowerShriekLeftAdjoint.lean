/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# The derived lower shriek is a left adjoint

For a finite coefficient ring `Λ` and a compactification `X ⟶[i] Z ⟶[g] Y` of `f : X ⟶ Y`, the
derived lower shriek `Rf_! = D(i_!) ⋙ Rg_*` on the unbounded derived categories of étale sheaves
of `Λ`-modules is a left adjoint (blueprint `theorem-existence-exceptional-inverse-image--1`). The
right adjoint is the exceptional inverse image `Rf^!` of
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`, where the result is registered as the
instance `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`.

The proof follows the blueprint:

* the proper direct image `Rg_*` preserves coproducts (blueprint
`corollary-proper-direct-image-finite-coefficients-localizing`):
  the higher direct images `R^q g_*` commute with direct sums, and at each geometric point of
  `Y` they vanish above twice the dimension of the geometric fibre
  (`AlgebraicGeometry.Etale.exists_isZero_upperStar_rightDerived_lowerStar_of_isProper`), so
  `g_*` sends exact complexes of `g_*`-acyclic sheaves to exact complexes and the unbounded
  `Rg_*` is computed termwise on complexes of injectives. Only this pointwise bound is used: the
  fibre dimension of `g` need not be globally bounded, as `Y` is arbitrary;
* the extension by zero `D(i_!)` is a left adjoint, hence preserves coproducts;
* Brown representability for the derived category of a Grothendieck abelian category
  (`DerivedCategory.isLeftAdjoint_of_preservesCoproducts`, Stacks `0F5Y`).

The file deliberately does not import the commutation with shifts of `Rf_!`
(`WeilConjectures.SixFunctors.Etale.Derived.Shift`), which itself imports `UpperShriek`: being a
left adjoint is a property, so any triangulated structure on `Rf_!` will do, and the one
induced by the adjunction `D(g^*) ⊣ Rg_*` is rebuilt locally.

## Main statements

- `CategoryTheory.Functor.preservesColimitsOfShape_rightDerivedFunctor_of_map_acyclic`: `RF`
  commutes with coproducts if `F` does, `F` sends exact complexes of `F`-acyclic objects to exact
  complexes, and coproducts of `F`-acyclic objects are `F`-acyclic.
- `AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`
  (`corollary-proper-direct-image-finite-coefficients-localizing`).
- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`
  (`theorem-existence-exceptional-inverse-image--1`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

-- This file brings the instance of `GrothendieckTopology.W.IsMonoidal` through enough points
-- of the site into scope for all importers of `Rf^!`; it is tried before the direct instance
-- `GrothendieckTopology.W.monoidal` and makes instance search time out. Prefer the latter.
attribute [instance high] GrothendieckTopology.W.monoidal

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

/-- **Right derived functors commute with coproducts**, under an abstract finiteness condition.
Let `C` be a Grothendieck abelian category and `F : C ⥤ D` a left exact additive functor which
commutes with coproducts of shape `J`, sends exact (unbounded) complexes of `F`-acyclic objects to
exact complexes, and such that coproducts of shape `J` of `F`-acyclic objects are `F`-acyclic.
Then `RF : D(C) ⥤ D(D)` commutes with coproducts of shape `J`.

This is `Functor.preservesColimitsOfShape_rightDerivedFunctor` with the global bound on the
cohomological dimension replaced by its only consequence used in the proof, so that it applies to
functors of *pointwise* finite cohomological dimension
(`HomologicalComplex.Acyclic.map_of_rightAcyclic_of_forall_isZero`). -/
theorem preservesColimitsOfShape_rightDerivedFunctor_of_map_acyclic
    [PreservesFiniteLimits F] [IsGrothendieckAbelian.{w} C] [HasInjectiveResolutions C]
    [Abelian.HasKInjectiveResolutions D] (J : Type*) [HasColimitsOfShape (Discrete J) C]
    [HasColimitsOfShape (Discrete J) D] [PreservesColimitsOfShape (Discrete J) F]
    (hF : ∀ M : CochainComplex C ℤ, M.Acyclic → (∀ n, F.rightAcyclic (M.X n)) →
      ((F.mapHomologicalComplex _).obj M).Acyclic)
    (hJ : ∀ X : J → C, (∀ j, F.rightAcyclic (X j)) → F.rightAcyclic (∐ X)) :
    PreservesColimitsOfShape (Discrete J) F.rightDerivedFunctor where
  preservesColimit {G} := by
    let I (j : J) := (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj
      (DerivedCategory.Q.objPreimage (G.obj ⟨j⟩))
    have hι (j : J) : IsIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{w}
        C).app (DerivedCategory.Q.objPreimage (G.obj ⟨j⟩)))) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C _) _
        ((CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C _).2)
    let e : Discrete.functor (fun j ↦ DerivedCategory.Q.obj (I j)) ≅ G :=
      Discrete.natIso fun j ↦ (asIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{w} C).app
          (DerivedCategory.Q.objPreimage (G.obj ⟨j.as⟩))))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso _
    suffices PreservesColimit (Discrete.functor fun j ↦ DerivedCategory.Q.obj (I j))
        F.rightDerivedFunctor from preservesColimit_of_iso_diagram _ e
    have hinj (j : J) (n : ℤ) : Injective ((I j).X n) :=
      CochainComplex.injective_kInjectiveResolutionFunctor_obj_X.{w} _ n
    -- the coproduct of the complexes `I j` is a complex of `F`-acyclic objects
    have hP (n : ℤ) : F.rightAcyclic ((∐ I).X n) :=
      F.rightAcyclic.prop_of_iso
        (PreservesCoproduct.iso (HomologicalComplex.eval C (.up ℤ) n) I).symm
        (hJ _ fun j ↦ have := hinj j n; rightAcyclic_of_injective ((I j).X n))
    -- the comparison maps `F(K) ⟶ RF(K)`, natural in `K`
    let v (K : CochainComplex C ℤ) : DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj K) ⟶
        F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)
    have nat {K L : CochainComplex C ℤ} (f : K ⟶ L) :
        DerivedCategory.Q.map ((F.mapHomologicalComplex _).map f) ≫ v L =
          v K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
      have h := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient C (.up ℤ)).map f)
      simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
      simp only [v, DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
      rw [reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp,
        DerivedCategory.quotientCompQhIso_hom_naturality]
    have hv (K : CochainComplex C ℤ) (hK : ∀ n, F.rightAcyclic (K.X n)) : IsIso (v K) := by
      have := F.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic_of_map_acyclic hF K hK
      dsimp only [v]
      infer_instance
    have hu (j : J) : IsIso (v (I j)) :=
      hv _ fun n ↦ have := hinj j n; rightAcyclic_of_injective _
    have huP : IsIso (v (∐ I)) := hv _ hP
    -- the image under `F` of the coproduct cofan is a coproduct in `D(D)`
    have hFc : IsColimit (Cofan.mk (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (∐ I)))
        fun j ↦ DerivedCategory.Q.map ((F.mapHomologicalComplex _).map (Sigma.ι I j))) :=
      DerivedCategory.isColimitCofanMkQObj
        ((isColimitMapCoconeCofanMkEquiv (F.mapHomologicalComplex (.up ℤ)) I (Sigma.ι I)).1
          (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) (coproductIsCoproduct I)))
    refine preservesColimit_of_preserves_colimit_cocone
      (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct I))
      ((isColimitMapCoconeCofanMkEquiv _ _ _).2 ?_)
    refine (IsColimit.equivOfNatIsoOfIso (Discrete.natIso fun j ↦ asIso (v (I j.as))) _ _
      (Cocone.ext (asIso (v (∐ I))) fun j ↦ ?_)) hFc
    dsimp
    rw [Category.assoc, nat]
    simp

/-- **Right derived functors commute with coproducts**, when `F` sends exact complexes of
`F`-acyclic objects to exact complexes and all the classical right derived functors `R^n F`
(`n ≥ 0`) commute with coproducts of shape `J`
(`Functor.preservesColimitsOfShape_rightDerivedFunctor_of_map_acyclic`). -/
theorem preservesColimitsOfShape_rightDerivedFunctor_of_map_acyclic_of_rightDerived
    [PreservesFiniteLimits F] [IsGrothendieckAbelian.{w} C] [HasInjectiveResolutions C]
    [Abelian.HasKInjectiveResolutions D] (J : Type*) [HasColimitsOfShape (Discrete J) C]
    [HasColimitsOfShape (Discrete J) D]
    (hF : ∀ M : CochainComplex C ℤ, M.Acyclic → (∀ n, F.rightAcyclic (M.X n)) →
      ((F.mapHomologicalComplex _).obj M).Acyclic)
    (hJ : ∀ n, PreservesColimitsOfShape (Discrete J) (F.rightDerived n)) :
    PreservesColimitsOfShape (Discrete J) F.rightDerivedFunctor :=
  have : PreservesColimitsOfShape (Discrete J) F :=
    have := hJ 0
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  F.preservesColimitsOfShape_rightDerivedFunctor_of_map_acyclic.{w} J hF fun X hX q ↦
    have := hJ (q + 1)
    IsZero.of_iso ((IsZero.iff_id_eq_zero _).2
        (Sigma.hom_ext _ _ fun j ↦ (hX j q).eq_of_src _ _))
      (PreservesCoproduct.iso (F.rightDerived (q + 1)) X)

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `corollary-proper-direct-image-finite-coefficients-localizing`: proper direct image
preserves arbitrary coproducts.

For a coefficient ring `Λ` which is torsion as an additive group and a proper morphism
`g : X ⟶ Y`, the derived pushforward `Rg_* : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` on the unbounded derived
categories commutes with coproducts. The higher direct images commute with direct sums
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerived_lowerStar`), and at each
geometric point of `Y` they vanish in degrees above twice the dimension of the geometric fibre
(`AlgebraicGeometry.Etale.exists_isZero_upperStar_rightDerived_lowerStar_of_isProper`), so `g_*`
sends exact complexes of `g_*`-acyclic sheaves to exact complexes. -/
theorem preservesColimitsOfShape_rightDerivedLowerStar_of_isProper (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι) (R((g)_*[ModuleCat.{u + 1} Λ])) := by
  choose d hd using Etale.exists_isZero_upperStar_rightDerived_lowerStar_of_isProper Λ hΛ g
  refine ((g)_*[ModuleCat.{u + 1} Λ])
    |>.preservesColimitsOfShape_rightDerivedFunctor_of_map_acyclic_of_rightDerived ι
      (fun M hM hM' ↦ ?_) fun n ↦ inferInstance
  exact hM.map_of_rightAcyclic_of_forall_isZero _
    (fun y ↦ Etale.upperStar (ModuleCat.{u + 1} Λ) (Y.algClosurePoint y))
    (Etale.isZero_of_forall_isZero_upperStar_algClosurePoint Λ) d hd hM'

/-- Blueprint `theorem-existence-exceptional-inverse-image--1`: the ordinary ambient exceptional
adjoint.

For a finite coefficient ring `Λ` and a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, the
derived lower shriek `Rf_! = D(i_!) ⋙ Rg_*` on the unbounded derived categories of étale sheaves
of `Λ`-modules is a left adjoint. It is triangulated and preserves coproducts: `D(i_!)` is a
left adjoint and `Rg_*` preserves coproducts
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`). Brown
representability (`DerivedCategory.isLeftAdjoint_of_preservesCoproducts`, Stacks `0F5Y`)
concludes. -/
theorem isLeftAdjoint_rightDerivedLowerShriekOfCompactification [Finite Λ] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) :
    (Rf_!(c)[ModuleCat.{u + 1} Λ]).IsLeftAdjoint := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g
  let : (R((c.g)_*[ModuleCat.{u + 1} Λ])).CommShift ℤ := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have : (R((c.g)_*[ModuleCat.{u + 1} Λ])).IsTriangulated := adj.isTriangulated_rightAdjoint
  have : (D((c.i)_!open[ModuleCat.{u + 1} Λ])).IsLeftAdjoint :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) c.i).isLeftAdjoint
  have (J : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete J) (R((c.g)_*[ModuleCat.{u + 1} Λ])) :=
    preservesColimitsOfShape_rightDerivedLowerStar_of_isProper Λ hΛ c.g J
  exact DerivedCategory.isLeftAdjoint_of_preservesCoproducts (Rf_!(c)[ModuleCat.{u + 1} Λ])

end Etale

end AlgebraicGeometry
