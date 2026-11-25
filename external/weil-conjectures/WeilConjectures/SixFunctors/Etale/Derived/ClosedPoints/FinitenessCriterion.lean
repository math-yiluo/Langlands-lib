/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterionStep


/-!
# Deligne's finiteness criterion at closed points

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`p : X ⟶ Spec k` proper. Let `hᵢ : Wᵢ ⟶ X` be finitely many morphisms from Noetherian schemes
whose images contain all the non-closed points of `X`. A bounded below complex `G` of étale
sheaves of `Λ`-modules on `X` is bounded constructible as soon as its pullbacks `Lhᵢ^* G` and its
cohomology `Rp_* G` are bounded constructible
(`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper`).

This is the form of Deligne's argument (SGA 4½, [Th. finitude], proof of 3.2) used for the
finiteness of nearby cycles, the `hᵢ` being the geometric generic fibres of the coordinates of
the charts of the special fibre of `ℙⁿ`.

## Proof

Let `F = ℋ^q(G)`. By Deligne's approximation
(`AlgebraicGeometry.Etale.exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel`) it has a
constructible subsheaf `F₀` with `F / F₀` supported at closed points; for `q` larger than the
amplitudes of the `Lhᵢ^* G`, `F` itself is supported at closed points.
* By induction on `q` from below, `τ^{≤ q} G` is bounded constructible: if `τ^{< q} G` is, so is
  its cohomology (`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`),
  hence `H^q(X, τ^{≥ q} G) = Γ(X, F)` is finite
  (`AlgebraicGeometry.Etale.nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE`);
  then `Γ(X, F / F₀)` is finite, as `H¹(X, F₀)` is, so `F / F₀` is constructible
  (`AlgebraicGeometry.Etale.isConstructibleSheaf_of_isZero_sheafFiber_of_finite`), and so is `F`.
* For `N` beyond the amplitudes, `τ^{≥ N} G` has cohomology sheaves supported at closed points,
  which are acyclic
  (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber`), so
  `H^q(X, τ^{≥ N} G) = Γ(X, ℋ^q(G))` vanishes for large `q`, and `ℋ^q(G) = 0` for large `q`
  (`AlgebraicGeometry.Etale.isZero_of_isZero_sheafFiber_of_subsingleton`).
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

omit [Finite Λ] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))] in
/-- In a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶` of complexes of `Λ`-modules, `Hᵠ(T₃) = 0` as
soon as `Hᵠ(T₂) = 0` and `Hᵠ⁺¹(T₁) = 0`. -/
lemma isZero_homology_obj₃_of_distinguished
    (T : Pretriangulated.Triangle (_root_.DerivedCategory (ModuleCat.{u + 1} Λ)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) (q : ℤ)
    (h₂ : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj T.obj₂))
    (h₁ : IsZero ((_root_.DerivedCategory.homologyFunctor _ (q + 1)).obj T.obj₁)) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj T.obj₃) :=
  (_root_.DerivedCategory.HomologySequence.exact₃ T hT q (q + 1)).isZero_X₂ (h₂.eq_of_src _ _)
    (h₁.eq_of_tgt _ _)

omit [Finite Λ] in
/-- Above the amplitudes of the pullbacks `Lhᵢ^* G`, the cohomology sheaves of `G` have vanishing
stalks at the non-closed points, which are in the images of the `hᵢ`. -/
lemma exists_isZero_sheafFiber_homology_of_upperStar {X : Scheme.{u}} {ι : Type*} [Finite ι]
    {W : ι → Scheme.{u}} (h : ∀ i, W i ⟶ X)
    (hcov : ∀ x ∉ closedPoints X, ∃ (i : ι) (w : W i), h i w = x)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hG : ∀ i, Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (W i)
      ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G)) :
    ∃ N : ℤ, ∀ q, N < q → ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj G)) := by
  choose b hb using fun i ↦ (hG i).1.2
  obtain ⟨N, hN⟩ := (Set.finite_range b).bddAbove
  refine ⟨N, fun q hq x hx ↦ ?_⟩
  obtain ⟨i, w, rfl⟩ := hcov x hx
  have := hb i
  have hz := _root_.DerivedCategory.isZero_of_isLE
    ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G) (b i) q
    (lt_of_le_of_lt (hN ⟨i, rfl⟩) hq)
  exact isZero_sheafFiber_algClosurePoint_apply_of_isZero_sheafFiber_upperStar (h i) w _
    ((pointSmallEtale _).sheafFiber.map_isZero (hz.of_iso
      (((Etale.upperStar (ModuleCat.{u + 1} Λ) (h i)).leftDerivedFunctorHomologyFunctorIso q).app
        G)))

/-- Under the hypotheses of Deligne's criterion, all the cohomology sheaves of `G` are
constructible, by induction from below
(`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_of_forall_lt`). -/
lemma isConstructibleSheaf_homology_of_upperStar_of_rightDerivedLowerStar {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {ι : Type*} [Finite ι] {W : ι → Scheme.{u}}
    [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ X)
    (hcov : ∀ x ∉ closedPoints X, ∃ (i : ι) (w : W i), h i w = x)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m : ℤ)
    [G.IsGE m]
    (hG : ∀ i, Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (W i)
      ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G))
    (hΓ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj G)) (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj G) := by
  suffices H : ∀ n : ℕ, ∀ q, q < m + n →
      IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj G) from
    H (q - m + 1).toNat q (by lia)
  intro n
  induction n with
  | zero =>
    intro q hq
    exact IsConstructibleSheaf.of_isZero
      (_root_.DerivedCategory.isZero_of_isGE G m q (by simpa using hq))
  | succ n ih =>
    intro q hq
    rcases lt_or_eq_of_le (show q ≤ m + n by push_cast at hq; lia) with hq' | rfl
    · exact ih q hq'
    · refine isConstructibleSheaf_homology_of_forall_lt p h hcov G m _ (fun i ↦ ?_) hΓ
        (fun j hj ↦ ih j hj)
      have := (hG i).2 (m + n)
      exact IsConstructibleSheaf.of_iso
        (F := (_root_.DerivedCategory.homologyFunctor _ (m + n)).obj
          ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G))
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) (h i)).leftDerivedFunctorHomologyFunctorIso
          (m + n)).app G).symm

/-- If the cohomology sheaves of `G` are constructible, supported at closed points above `N`, and
`Rp_* G` is bounded constructible, then `G` is bounded above: above `N`, `H^q(X, τ^{≥ N + 1} G)`
is `Γ(X, ℋ^q(G))`, and it vanishes for large `q`. -/
lemma exists_isLE_of_isZero_sheafFiber_homology {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsProper p] (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (m : ℤ) [G.IsGE m] (N : ℤ)
    (hstalk : ∀ q, N < q → ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj G)))
    (hc : ∀ q, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj G))
    (hΓ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj G)) :
    ∃ b : ℤ, G.IsLE b := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
    inferInstanceAs
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  -- the truncation `τ^{≥ N + 1} G` has cohomology sheaves supported at closed points
  let B := (t.truncGE (N + 1)).obj G
  have eB (q : ℤ) (hq : N + 1 ≤ q) :=
    have := _root_.DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app G (N + 1) q hq
    asIso ((_root_.DerivedCategory.homologyFunctor _ q).map ((t.truncGEπ (N + 1)).app G))
  have hBstalk (q : ℤ) (x : X) (hx : x ∉ closedPoints X) :
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj B)) := by
    rcases lt_or_ge q (N + 1) with hq | hq
    · exact (pointSmallEtale _).sheafFiber.map_isZero
        (_root_.DerivedCategory.isZero_of_isGE B (N + 1) q hq)
    · exact (hstalk q (by lia) x hx).of_iso ((pointSmallEtale _).sheafFiber.mapIso (eB q hq)).symm
  -- so `H^q(X, τ^{≥ N + 1} G) = Γ(X, ℋ^q(τ^{≥ N + 1} G))`
  have hB (q : ℤ) := nonempty_homology_rightDerivedGlobalSections_obj_iso_of_acyclic Λ X B (N + 1)
    (fun q r hr ↦ isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber Λ p _
      (hBstalk q) hr.ne') q
  -- vanishing of `H^q(X, G)` and of `H^{q + 1}(X, τ^{< N + 1} G)` for large `q`
  obtain ⟨b₁, hb₁⟩ :=
    (boundedFiniteCohomology_rightDerivedGlobalSections_of_rightDerivedLowerStar p hΓ).1.2
  obtain ⟨b₂, hb₂⟩ := (boundedFiniteCohomology_rightDerivedGlobalSections_of_isProper p
    (boundedConstructible_truncLT_of_isGE G m (N + 1) fun j _ ↦ hc j)).1.2
  have hT := RΓ.map_distinguished _ (t.triangleLTGE_distinguished (N + 1) G)
  refine ⟨max (max b₁ b₂) (N + 1), (_root_.DerivedCategory.isLE_iff G _).2 fun q hq ↦ ?_⟩
  have h₁ : IsZero
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj (RΓ.obj G)) :=
    _root_.DerivedCategory.isZero_of_isLE _ b₁ q (by lia)
  have h₃ : IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (q + 1)).obj
      (RΓ.obj ((t.truncLT (N + 1)).obj G))) :=
    _root_.DerivedCategory.isZero_of_isLE _ b₂ (q + 1) (by lia)
  have h₂ := isZero_homology_obj₃_of_distinguished _ hT q h₁ h₃
  obtain ⟨e'⟩ := hB q
  refine IsZero.of_iso ?_ (eB q (by lia))
  refine isZero_of_isZero_sheafFiber_of_subsingleton _ p (hBstalk q) ?_
  exact ModuleCat.isZero_iff_subsingleton.1 ((h₂.of_iso e'.symm).of_iso
    ((Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleTerminal X)).app _).symm)

/-- **Deligne's finiteness criterion at closed points** (SGA 4½, [Th. finitude], proof of 3.2).
Over a separably closed field `k`, let `p : X ⟶ Spec k` be proper and `hᵢ : Wᵢ ⟶ X` finitely many
morphisms from Noetherian schemes whose images contain the non-closed points of `X`. A bounded
below complex `G` of étale sheaves of modules over a finite ring with invertible exponent is
bounded constructible as soon as the pullbacks `Lhᵢ^* G` and the direct image `Rp_* G` are. -/
theorem boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {ι : Type*} [Finite ι] {W : ι → Scheme.{u}}
    [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ X)
    (hcov : ∀ x ∉ closedPoints X, ∃ (i : ι) (w : W i), h i w = x)
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m : ℤ)
    [G.IsGE m]
    (hG : ∀ i, Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (W i)
      ((L(Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))).obj G))
    (hΓ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj G)) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X G := by
  obtain ⟨N, hN⟩ := exists_isZero_sheafFiber_homology_of_upperStar h hcov G hG
  have hc := isConstructibleSheaf_homology_of_upperStar_of_rightDerivedLowerStar p h hcov G m hG hΓ
  obtain ⟨b, hb⟩ := exists_isLE_of_isZero_sheafFiber_homology p G m N hN hc hΓ
  exact ⟨⟨⟨m, ‹_›⟩, ⟨b, hb⟩⟩, hc⟩

end Etale

end AlgebraicGeometry
