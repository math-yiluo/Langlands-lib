/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.SixFunctors.Etale.Derived.UnitLerayQuotient

/-!
# Restriction of derived global sections when global sections are exact

Let `f : Y ⟶ X` be a morphism of schemes such that the global sections functors on the small
étale sites of `X` and `Y` are exact (for instance, `X` and `Y` spectra of strictly henselian
local rings). For `K ∈ D(X_ét)`, the derived global sections of the unit
`K ⟶ Rf_* f^* K` is an isomorphism as soon as the pullback of global sections
`Γ(X, Hⁿ(K)) ⟶ Γ(Y, f^* Hⁿ(K))` is an isomorphism for every `n`
(`AlgebraicGeometry.Etale.isIso_rightDerivedGlobalSections_map_unit_of_isIso`).

Similarly, if global sections on `X` are exact, `RΓ(X, K)` vanishes as soon as all the
`Γ(X, Hⁿ(K))` vanish (`AlgebraicGeometry.Etale.isZero_rightDerivedGlobalSections_obj`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- If the global sections functor on `X` is exact, an object `K` of `D(X_ét)` has vanishing
derived global sections as soon as the global sections of its cohomology sheaves vanish. -/
lemma isZero_rightDerivedGlobalSections_obj {X : Scheme.{u}}
    [PreservesFiniteLimits (Sheaf.Γ X.smallEtaleTopology A)]
    [PreservesFiniteColimits (Sheaf.Γ X.smallEtaleTopology A)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : ∀ n : ℤ, IsZero ((Sheaf.Γ X.smallEtaleTopology A).obj
      ((DerivedCategory.homologyFunctor _ n).obj K))) :
    IsZero ((rightDerivedGlobalSections A X).obj K) := by
  have : IsIso (0 : (rightDerivedGlobalSections A X).obj K ⟶ 0) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    refine isIso_of_source_target_iso_zero _ ?_ ?_
    · exact ((hK n).of_iso (((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorHomologyFunctorIso
        n).app K).symm).isoZero
    · exact (Functor.map_isZero _ (isZero_zero _)).isoZero
  exact IsZero.of_iso (isZero_zero _) (asIso (0 : (rightDerivedGlobalSections A X).obj K ⟶ 0))


/-- The morphism of complexes `Γ(X, K) ⟶ Γ(Y, f^* K)` given degreewise by the pullback of
global sections is a quasi-isomorphism as soon as the pullback of global sections of each
homology sheaf is an isomorphism, provided that the global sections functors are exact. -/
lemma quasiIso_mapHomologicalComplex_globalSectionsUpperStarNatTrans {X Y : Scheme.{u}}
    (f : Y ⟶ X)
    [PreservesFiniteLimits (Sheaf.Γ X.smallEtaleTopology A)]
    [PreservesFiniteColimits (Sheaf.Γ X.smallEtaleTopology A)]
    [PreservesFiniteLimits (Sheaf.Γ Y.smallEtaleTopology A)]
    [PreservesFiniteColimits (Sheaf.Γ Y.smallEtaleTopology A)]
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    (hK : ∀ n : ℤ, IsIso (globalSectionsUpperStarMap A f (K.homology n))) :
    QuasiIso ((NatTrans.mapHomologicalComplex (globalSectionsUpperStarNatTrans A f)
      (.up ℤ)).app K) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hn : IsIso ((globalSectionsUpperStarNatTrans A f).app (K.sc n).homology) := by
    rw [globalSectionsUpperStarNatTrans_app]
    exact hK n
  rw [NatTrans.app_homology (globalSectionsUpperStarNatTrans A f) (K.sc n), isIso_comp_left_iff,
    isIso_comp_right_iff] at hn
  exact hn

/-- **Restriction of derived global sections when global sections are exact.** Let `f : Y ⟶ X`
be a morphism of schemes such that the global sections functors on `X_ét` and `Y_ét` are exact,
and `K ∈ D(X_ét)` such that the pullback `Γ(X, Hⁿ(K)) ⟶ Γ(Y, f^* Hⁿ(K))` of global sections is
an isomorphism for every `n`. Then the derived global sections of the unit `K ⟶ Rf_* f^* K` is
an isomorphism. -/
theorem isIso_rightDerivedGlobalSections_map_unit_of_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [PreservesFiniteLimits (Sheaf.Γ X.smallEtaleTopology A)]
    [PreservesFiniteColimits (Sheaf.Γ X.smallEtaleTopology A)]
    [PreservesFiniteLimits (Sheaf.Γ Y.smallEtaleTopology A)]
    [PreservesFiniteColimits (Sheaf.Γ Y.smallEtaleTopology A)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : ∀ n : ℤ, IsIso (globalSectionsUpperStarMap A f
      ((DerivedCategory.homologyFunctor _ n).obj K))) :
    IsIso ((rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app K)) := by
  let K₀ := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K₀) ≅ K :=
    (DerivedCategory.quotientCompQhIso _).app K₀ ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hK₀ (n : ℤ) : IsIso (globalSectionsUpperStarMap A f (K₀.homology n)) := by
    have := hK n
    rw [← globalSectionsUpperStarNatTrans_app] at this ⊢
    exact NatTrans.isIso_app_of_iso _ (((DerivedCategory.homologyFunctorFactors _ n).app K₀).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso (DerivedCategory.Q.objObjPreimageIso K))
  have hQ : IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (globalSectionsUpperStarNatTrans A f) (.up ℤ)).app K₀)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_mapHomologicalComplex_globalSectionsUpperStarNatTrans A f K₀ hK₀)
  have key : IsIso ((rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K₀)))) := by
    have h := rightDerivedGlobalSections_map_unit_quotient A f K₀
    have : IsIso ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj K₀) ≫
        (rightDerivedGlobalSections A X).map
          ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K₀))) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app
            (((f)^*[A]).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K₀))) ≫
        (rightDerivedGlobalSections A Y).map
          (((f)^*[A]).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ _).obj K₀))) := by
      rw [h]
      infer_instance
    rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]
      at this
    exact this
  exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _
    (Functor.whiskerRight (mapDerivedUpperStarLowerStarAdjunction A f).unit
      (rightDerivedGlobalSections A X)) _ _ e.symm key

end AlgebraicGeometry.Etale
