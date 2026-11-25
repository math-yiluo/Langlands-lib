/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Detection
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived

/-!
# Detection of pro-étale complexes supported at closed points

Let `k` be a separably closed field, `X` a scheme locally of finite type over `k` with structure
morphism `p`, and `T` a finite discrete ring. A complex `C` of modules over the condensed
coefficient ring `T̲` on `X_proét` which is bounded below of étale origin vanishes as soon as
its pullbacks to (neighbourhoods of) the non-closed points of `X` vanish and `Rp_* C = 0`
(Stacks 0F1G). Writing the comparison of `C` with pro-étale sheaves of `T`-modules as `ν^* G`
for a bounded below étale complex `G`, this is reduced to the étale statement
`AlgebraicGeometry.Etale.isZero_iff_forall_isZero_homology_rightDerivedGlobalSections_of_isGE`:
the pullbacks of `G` to the geometric points over the non-closed points vanish, and
`RΓ(X_ét, G) = RΓ(Spec k, Rp_* G)` with `Rp_* G ≅ Rν_* Rp_* ν^* G = 0`.

## Main statements

- `AlgebraicGeometry.ProEtale.CondensedRing.isZero_of_isZero_leftDerivedUpperStar_of_not_isClosed`
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Detection of pro-étale complexes supported at closed points** (Stacks 0F1G, finite
coefficients). Let `k` be a separably closed field, `p : X ⟶ Spec k` locally of finite type and
`C` a complex of `T̲`-modules on `X_proét` which is bounded below of étale origin. If for every
non-closed point `x` some `h : W ⟶ X` through `x` has `Lh^* C = 0`, and `Rp_* C = 0`, then
`C = 0`.

Write `Φ C ≅ ν^* G` with `G` a bounded below étale complex. Then `Lh^* G = 0` (`ν^*` commutes
with pullback and reflects zero objects), so the stalks of `ℋ^q(G)` at the geometric points over
the non-closed points vanish, and `RΓ(X_ét, G) ≅ RΓ(Spec k, Rp_* G)` with
`Rp_* G ≅ Rp_* Rν_* ν^* G ≅ Rν_* Rp_* Φ C ≅ Rν_* Φ (Rp_* C) = 0`; hence `G = 0` by
`AlgebraicGeometry.Etale.isZero_iff_forall_isZero_homology_rightDerivedGlobalSections_of_isGE`.
-/
theorem isZero_of_isZero_leftDerivedUpperStar_of_not_isClosed {k : Type u} [Field k]
    [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj C))
    (hpt : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ (W : Scheme.{u}) (h : W ⟶ X) (w : W),
      h w = x ∧ IsZero ((L((h)^*⟦Profinite.continuousMapRingObj T⟧)).obj C))
    (hΓ : IsZero ((R((p)_*⟦Profinite.continuousMapRingObj T⟧)).obj C)) : IsZero C := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} T)
  obtain ⟨G, ⟨m, hm⟩, ⟨e⟩⟩ := hC
  have : G.IsGE m := hm
  suffices hG : IsZero G by
    have h0 : IsZero ((finiteCoefficientDerivedEquivalence X T).functor.obj C) :=
      ((D(ν^*(X)[A])).map_isZero hG).of_iso e.symm
    exact ((finiteCoefficientDerivedEquivalence X T).inverse.map_isZero h0).of_iso
      ((finiteCoefficientDerivedEquivalence X T).unitIso.app C)
  refine (Etale.isZero_iff_forall_isZero_homology_rightDerivedGlobalSections_of_isGE p G m
    fun q x hx ↦ ?_).2 fun i ↦ ?_
  · obtain ⟨W, h, w, rfl, hz⟩ := hpt x hx
    have h1 : IsZero ((L(ProEtale.upperStar A h)).obj (D(ν^*(X)[A]).obj G)) :=
      (((finiteCoefficientDerivedEquivalence W T).functor.map_isZero hz).of_iso
        ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso h T).app C).symm).of_iso
        ((L(ProEtale.upperStar A h)).mapIso e)
    have h2 : IsZero ((L(Etale.upperStar A h)).obj G) := by
      refine (DerivedCategory.isZero_iff _).2 fun n ↦ ?_
      exact Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        (ν^*(W)[A]) ((DerivedCategory.homologyFunctor _ n).map_isZero
          (h1.of_iso ((derivedComparisonUpperStarUpperStarIso A h).app G).symm))
    have h3 : IsZero ((L(Etale.upperStar A (W.algClosurePoint w ≫ h))).obj G) :=
      ((L(Etale.upperStar A (W.algClosurePoint w))).map_isZero h2).of_iso
        ((Etale.leftDerivedUpperStarComp A (W.algClosurePoint w) h).app G)
    refine (Etale.isZero_sheafFiber_iff_of_apply_eq _ (W.algClosurePoint w ≫ h)
      (X.algClosurePoint (h w)) (by simp)).1 ?_
    exact (((sheafSections _ _).obj _).map_isZero
      ((DerivedCategory.homologyFunctor _ q).map_isZero h3)).of_iso
      (Etale.sheafFiberHomologyIso (ULift.{u + 1} T) (W.algClosurePoint w ≫ h) G q)
  · have hunit := isIso_derivedComparisonAdjunction_unit_app A X G ⟨m, hm⟩
    have h1 : IsZero ((R(ProEtale.lowerStar A p)).obj (D(ν^*(X)[A]).obj G)) :=
      ((finiteCoefficientDerivedEquivalence _ T).functor.map_isZero hΓ).of_iso
        ((R(ProEtale.lowerStar A p)).mapIso e ≪≫ (finiteCoefficientDerivedLowerStarIso T p).app C)
    have h2 : IsZero ((R(Etale.lowerStar A p)).obj G) :=
      ((R(ν_*(Spec (.of k))[A])).map_isZero h1).of_iso
        ((R(Etale.lowerStar A p)).mapIso (asIso ((derivedComparisonAdjunction A X).unit.app G)) ≪≫
          ((rightDerivedLowerStarCompComparisonLowerStarIso A p).app _).symm)
    exact (DerivedCategory.homologyFunctor _ i).map_isZero
      (((Etale.rightDerivedGlobalSections A (Spec (.of k))).map_isZero h2).of_iso
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A p).app G).symm)

/-- **Detection of isomorphisms by pullbacks to non-closed points and global sections**
(Stacks 0F1G, morphism form). A morphism `a : K ⟶ L` of complexes of `T̲`-modules on `X_proét`
which are bounded below of étale origin is an isomorphism as soon as `Lh^* a` is one for some
`h : W ⟶ X` through each non-closed point of `X`, and `Rp_* a` is one: apply
`isZero_of_isZero_leftDerivedUpperStar_of_not_isClosed` to the cone of `a`, which is again
bounded below of étale origin, these complexes forming a triangulated subcategory. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed {k : Type u} [Field k]
    [IsSepClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))} (a : K ⟶ L)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj K))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj L))
    (hpt : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ (W : Scheme.{u}) (h : W ⟶ X) (w : W),
      h w = x ∧ IsIso ((L((h)^*⟦Profinite.continuousMapRingObj T⟧)).map a))
    (hΓ : IsIso ((R((p)_*⟦Profinite.continuousMapRingObj T⟧)).map a)) : IsIso a := by
  obtain ⟨M, b, c, hT⟩ := Pretriangulated.distinguished_cocone_triangle a
  refine (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  refine isZero_of_isZero_leftDerivedUpperStar_of_not_isClosed T p M
    ((DerivedCategory.plusEtaleOrigin _ X).ext_of_isTriangulatedClosed₃ _
      (D((finiteCoefficientModEquivalence X T).functor).map_distinguished _ hT) hK hL)
    (fun x hx ↦ ?_) ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((R((p)_*⟦Profinite.continuousMapRingObj T⟧)).map_distinguished _ hT)).2 hΓ)
  obtain ⟨W, h, w, hw, ha⟩ := hpt x hx
  exact ⟨W, h, w, hw, (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    ((L((h)^*⟦Profinite.continuousMapRingObj T⟧)).map_distinguished _ hT)).2 ha⟩

end AlgebraicGeometry.ProEtale.CondensedRing
