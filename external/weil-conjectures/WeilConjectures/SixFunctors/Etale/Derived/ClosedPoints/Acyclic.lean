/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Approximation
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts

/-!
# Sheaves supported at closed points are acyclic

Let `K` be a separably closed field, `X` a quasi-compact scheme locally of finite type over `K`
and `F` an étale sheaf of `Λ`-modules on `X` whose stalks vanish at the non-closed points. Then
`H^q(X_ét, F) = 0` for `q ≠ 0` (blueprint `lemma-sheaves-finite-support-finite-morphisms--1`): `F`
is the filtered colimit of its subsheaves `F_S` supported on finite sets of closed points
(`lemma-sheaves-finite-support-finite-morphisms--1`), these are acyclic, and étale cohomology of the
quasi-compact quasi-separated scheme `X` commutes with filtered colimits.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber`
  (`lemma-sheaves-finite-support-finite-morphisms--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- On a quasi-compact quasi-separated scheme, the higher derived functors of the global
sections commute with filtered colimits indexed by a `u + 1`-small category. -/
lemma preservesColimitsOfShape_rightDerived_globalSections_of_isFiltered (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (q : ℕ) (J : Type (u + 1)) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q) :=
  have := Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject Λ X q J
  have : PreservesColimitsOfShape J
      ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat) :=
    preservesColimitsOfShape_of_natIso (shiftedHomFunctorFreeSheafFinalObjectIso Λ X q)
  preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat)

attribute [local instance] IsFiltered.isConnected in
/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`: **vanishing for sheaves supported
on closed points.** Let `K` be a separably closed field, `X` a quasi-compact scheme locally of
finite type over `K` and `F` an étale sheaf of `Λ`-modules on `X` whose stalks at the geometric
points over the non-closed points vanish. Then `H^q(X_ét, F) = 0` for all `q ≠ 0`. -/
theorem isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    [CompactSpace X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  rcases lt_or_gt_of_ne hq with hq | hq
  · have : ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).IsGE 0 :=
      Γ.isGE_rightDerivedFunctor_obj_singleFunctor F
    exact _root_.DerivedCategory.isZero_of_isGE _ 0 q hq
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let J := AsSmall.{u + 1} (FiniteClosedPoints X)
  have : IsFiltered J := IsFiltered.of_equivalence AsSmall.equiv
  have := preservesColimitsOfShape_rightDerived_globalSections_of_isFiltered Λ X n J
  have hc := isColimitOfPreserves (Γ.rightDerived n) (isColimitSupportedSectionsCocone p F hF)
  -- each `F_S` is acyclic
  have hz (S : J) : IsZero ((Γ.rightDerived n).obj
      (supportedSections F (FiniteClosedPoints.openCompl (AsSmall.down.obj S)))) := by
    let T := AsSmall.down.obj S
    refine (isZero_homology_rightDerivedGlobalSections_of_isZero_upperStar Λ
      (FiniteClosedPoints.openCompl T) ?_ (fun x hx ↦ ?_) (fun x hx ↦ ?_) _
      (isZero_upperStar_supportedSections F _) (by exact_mod_cast hq.ne')).of_iso
        (Γ.homologyRightDerivedFunctorObjSingleFunctorIso _ n).symm
    · simpa [FiniteClosedPoints.openCompl, ← SetLike.mem_coe, coe_openComplOfFinite] using T.2.1
    · have hx' : x ∈ T.1 := by
        simpa [FiniteClosedPoints.openCompl, ← SetLike.mem_coe, coe_openComplOfFinite] using hx
      exact T.2.2 hx'
    · have hx' : x ∈ T.1 := by
        simpa [FiniteClosedPoints.openCompl, ← SetLike.mem_coe, coe_openComplOfFinite] using hx
      exact (p.residueField_of_isClosed_of_isSepClosed x (T.2.2 hx')).2.2
  have h0 : IsZero ((Γ.rightDerived n).obj F) :=
    (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun S ↦ (hz S).eq_of_src _ _)
  exact h0.of_iso (Γ.homologyRightDerivedFunctorObjSingleFunctorIso F n)

end Etale

end AlgebraicGeometry
