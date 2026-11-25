/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterionAux

/-!
# The induction step of Deligne's finiteness criterion at closed points

If the cohomology sheaves of a bounded below complex `G` on a proper scheme over a separably
closed field are constructible below degree `q`, if `RΓ(X, G)` has finite cohomology and if
`ℋ^q(G)` has a constructible subsheaf with quotient supported at closed points, then `ℋ^q(G)` is
constructible (`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_of_forall_lt`). This is the
inductive step of `WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterion`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory.TStructure (t)


variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- The induction step of Deligne's finiteness criterion: if the cohomology sheaves of `G` in
degrees `< q` are constructible, so is `ℋ^q(G)`. -/
theorem isConstructibleSheaf_homology_of_forall_lt {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {ι : Type*} [Finite ι] {W : ι → Scheme.{u}}
    [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ X)
    (hcov : ∀ x ∉ closedPoints X, ∃ (i : ι) (w : W i), h i w = x)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m q : ℤ)
    [G.IsGE m]
    (hpull : ∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (h i)).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj G)))
    (hΓ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj G))
    (hlt : ∀ j < q, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ j).obj G)) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj G) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
    inferInstanceAs
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  let Γ := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let F := (_root_.DerivedCategory.homologyFunctor _ q).obj G
  have hfin {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (hK : _root_.DerivedCategory.boundedFiniteCohomology Λ (RΓ.obj K)) (n : ℤ) :
      Finite ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).obj (RΓ.obj K)) :=
    ((_root_.DerivedCategory.boundedFiniteCohomology_iff_finite _).1 hK).2 n
  -- `Γ(X, F)` is finite
  have hΓF : Finite (Γ.obj F) := by
    have hT := RΓ.map_distinguished _ (t.triangleLTGE_distinguished q G)
    have h₃ := finite_X₂_of_exact
      (_root_.DerivedCategory.HomologySequence.exact₃ _ hT q (q + 1))
      (hfin (boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar p hΓ) q)
      (hfin (boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper p
        (boundedConstructible_truncLT_of_isGE G m q hlt)) (q + 1))
    obtain ⟨e⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ X
      ((t.truncGE q).obj G) q
    have := _root_.DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app G q q le_rfl
    exact @Finite.of_equiv _ _ h₃ (e ≪≫ Γ.mapIso (asIso
      ((_root_.DerivedCategory.homologyFunctor _ q).map
        ((t.truncGEπ q).app G))).symm).toLinearEquiv.toEquiv
  -- Deligne's approximation `F₀ ⊆ F`
  obtain ⟨F₀, a, ha, hF₀, hcok⟩ := exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel F h
    hpull
  let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel a) }
  have hQ : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj (cokernel a)) := by
    intro x hx
    obtain ⟨i, w, rfl⟩ := hcov x hx
    exact hcok i w
  -- `Γ(X, F / F₀)` is finite, as `Γ(X, F)` and `H¹(X, F₀)` are
  have hΓQ : Finite ((cokernel a).obj.obj (op (etaleTerminal X))) := by
    have hT := RΓ.map_distinguished _ hS.singleTriangle_distinguished
    obtain ⟨e₂⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) 0
    obtain ⟨e₃⟩ := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE Λ X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (cokernel a)) 0
    have h₂ : Finite ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).obj
        (RΓ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
      @Finite.of_equiv _ _ hΓF (e₂ ≪≫ Γ.mapIso
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
          F)).symm.toLinearEquiv.toEquiv
    have h₁ : Finite ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 1).obj
        (RΓ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F₀))) :=
      hfin (boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper p
        (DerivedCategory.boundedConstructible_singleFunctor_obj F₀ 0)) 1
    have h₃ := finite_X₂_of_exact
      (_root_.DerivedCategory.HomologySequence.exact₃ _ hT 0 1) h₂ h₁
    exact @Finite.of_equiv _ _ h₃ (e₃ ≪≫ Γ.mapIso
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (cokernel a)) ≪≫
      (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleTerminal X)).app _).toLinearEquiv.toEquiv
  have : IsConstructibleSheaf S.X₁ := hF₀
  have : IsConstructibleSheaf S.X₃ :=
    isConstructibleSheaf_of_isZero_sheafFiber_of_finite p (cokernel a) hQ hΓQ
  exact IsConstructibleSheaf.of_shortExact hS

end Etale

end AlgebraicGeometry
