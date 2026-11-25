/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.Curve.ExtensionInvariance
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen

/-!
# Betti cardinalities of smooth proper curves and of smooth projective curve families

Let `Y` be a smooth proper scheme of relative dimension one over an algebraically closed field
`k`, with `c` connected components, and let `ℓ` be invertible in `k`. Each connected component
of `Y` is open and closed and a smooth proper connected curve, so cohomology splits over the
components, and the curve computation gives

`|H⁰(Y, ℤ/ℓ)| = |H²(Y, ℤ/ℓ)| = ℓ^c`, `|H¹(Y, ℤ/ℓ)| = ℓ^{2 g}`, `|Hʳ(Y, ℤ/ℓ)| = 1` for `r > 2`,

where `g = dim_k H¹(Y, 𝒪_Y)` is the arithmetic genus, the sum of the genera of the components.
Moreover `dim_k H⁰(Y, 𝒪_Y) = c`.

Applied to the geometric fibres of a smooth projective family `f : X ⟶ S`, together with the
constructibility of the geometric fibre dimensions of `𝒪_X`
(`AlgebraicGeometry.Scheme.Modules.finite_range_and_isConstructible_finrankH_geometricFibre`),
this gives blueprint `proposition-proper-direct-image-finite-coefficients`.

## Main statements

- `AlgebraicGeometry.Scheme.natCard_sheafH_constantZMod_of_smoothOfRelativeDimension_one`
- `AlgebraicGeometry.Scheme.finrankH_unit_zero_eq_natCard_connectedComponents`
- `AlgebraicGeometry.Etale.natCard_sheafH_constantZMod_geometricFibre_of_smooth`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

section ConnectedComponents

variable {X : Scheme.{u}} [DiscreteTopology (_root_.ConnectedComponents X)]

/-- The connected component `c` of a scheme whose connected components are open, as an open
subscheme. -/
noncomputable def connectedComponentOpens (c : _root_.ConnectedComponents X) : X.Opens :=
  ⟨_root_.ConnectedComponents.mk ⁻¹' {c},
    (isOpen_discrete {c}).preimage _root_.ConnectedComponents.continuous_coe⟩

lemma isClosed_connectedComponentOpens (c : _root_.ConnectedComponents X) :
    IsClosed (X.connectedComponentOpens c : Set X) :=
  (isClosed_discrete {c}).preimage _root_.ConnectedComponents.continuous_coe

lemma mem_connectedComponentOpens (x : X) :
    x ∈ X.connectedComponentOpens (_root_.ConnectedComponents.mk x) :=
  rfl

lemma pairwise_disjoint_connectedComponentOpens :
    Pairwise fun c d ↦ Disjoint (X.connectedComponentOpens c : Set X)
      (X.connectedComponentOpens d) := fun _ _ hcd ↦
  (Set.disjoint_singleton.mpr hcd).preimage _root_.ConnectedComponents.mk

lemma pairwise_disjoint_on_connectedComponentOpens :
    _root_.Pairwise (Function.onFun Disjoint X.connectedComponentOpens) := fun _ _ hcd ↦
  TopologicalSpace.Opens.coe_disjoint.mp (pairwise_disjoint_connectedComponentOpens hcd)

lemma iSup_connectedComponentOpens : ⨆ c, X.connectedComponentOpens c = ⊤ :=
  eq_top_iff.mpr fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨_, mem_connectedComponentOpens x⟩

lemma connectedSpace_connectedComponentOpens (c : _root_.ConnectedComponents X) :
    ConnectedSpace (X.connectedComponentOpens c) := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  have : (X.connectedComponentOpens x : Set X) = connectedComponent x :=
    connectedComponents_preimage_singleton
  exact isConnected_iff_connectedSpace.mp (this ▸ isConnected_connectedComponent)

end ConnectedComponents

variable {k : Type u} [Field k]

/-- A smooth proper connected scheme of relative dimension one over a field is a connected
curve. -/
lemma isConnectedCurve_of_smoothOfRelativeDimension_one {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [ConnectedSpace C] : IsConnectedCurve f :=
  have h := topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1
  { krullDim_le_one := h.le
    connectedSpace := inferInstance
    krullDim_eq_one := h }

/-- The étale cohomology of `ℤ/ℓ` on a scheme with finitely many open connected components is the
product of the cohomologies of the components. -/
lemma natCard_sheafH_constantZMod_eq_prod {X : Scheme.{u}}
    [DiscreteTopology (_root_.ConnectedComponents X)] [Fintype (_root_.ConnectedComponents X)]
    (ℓ q : ℕ) :
    Nat.card (Sheaf.H (X.constantZMod ℓ) q) =
      ∏ c, Nat.card (Sheaf.H ((X.connectedComponentOpens c).toScheme.constantZMod ℓ) q) := by
  obtain ⟨e⟩ := Etale.nonempty_equiv_pi_H_of_isClopen X.connectedComponentOpens
    isClosed_connectedComponentOpens pairwise_disjoint_connectedComponentOpens
    (fun x ↦ ⟨_, mem_connectedComponentOpens x⟩) (X.constantZMod ℓ) q
  rw [Nat.card_congr e, Nat.card_pi]
  exact Finset.prod_congr rfl fun c _ ↦
    Nat.card_congr ((X.connectedComponentOpens c).ι.sheafHUpperStarConstantZModAddEquiv ℓ q).toEquiv

/-- An open subscheme of a scheme smooth of relative dimension `n` over a field is smooth of
relative dimension `n`. -/
lemma smoothOfRelativeDimension_ι_comp {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (U : C.Opens) : SmoothOfRelativeDimension n (U.ι ≫ f) := by
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) U.ι f
  rwa [zero_add] at this

/-- An open and closed subscheme of a proper scheme over a field is proper. -/
lemma isProper_ι_comp {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] {U : C.Opens}
    (hU : IsClosed (U : Set C)) : IsProper (U.ι ≫ f) :=
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  inferInstance

/-- A proper scheme over a field is Noetherian. -/
lemma isNoetherian_of_isProper {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] :
    IsNoetherian C :=
  isNoetherian_of_locallyOfFiniteType f

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]

/-- On a smooth proper scheme of relative dimension one over an algebraically closed field `k`,
every connected component `D` is a smooth proper connected curve; we record `h⁰(D, 𝒪) = 1`,
`g(D) = h¹(D, 𝒪)`, and the curve computation of the étale cohomology of `ℤ/ℓ` on `D`. -/
lemma connectedComponentOpens_facts [IsAlgClosed k]
    [DiscreteTopology (_root_.ConnectedComponents Y)]
    (c : _root_.ConnectedComponents Y) (ℓ : ℕ) (hℓ : (ℓ : k) ≠ 0) :
    letI : (Y.connectedComponentOpens c).toScheme.Over (Spec (.of k)) :=
      ⟨(Y.connectedComponentOpens c).ι ≫ Y ↘ Spec (.of k)⟩
    Modules.finrankH k (SheafOfModules.unit (Y.connectedComponentOpens c).toScheme.ringCatSheaf)
        0 = 1 ∧
      Nat.card (Sheaf.H ((Y.connectedComponentOpens c).toScheme.constantZMod ℓ) 0) = ℓ ∧
      Nat.card (Sheaf.H ((Y.connectedComponentOpens c).toScheme.constantZMod ℓ) 1) =
        ℓ ^ (2 * arithmeticGenus k (Y.connectedComponentOpens c).toScheme) ∧
      Nat.card (Sheaf.H ((Y.connectedComponentOpens c).toScheme.constantZMod ℓ) 2) = ℓ ∧
      ∀ r, 2 < r →
        Nat.card (Sheaf.H ((Y.connectedComponentOpens c).toScheme.constantZMod ℓ) r) = 1 := by
  set U := Y.connectedComponentOpens c
  let : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ Y ↘ Spec (.of k)⟩
  have := connectedSpace_connectedComponentOpens c
  have : SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_ι_comp (Y ↘ Spec (.of k)) 1 U
  have : IsProper (U.toScheme ↘ Spec (.of k)) :=
    isProper_ι_comp (Y ↘ Spec (.of k)) (isClosed_connectedComponentOpens c)
  have : Smooth (U.toScheme ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsConnectedCurve (U.toScheme ↘ Spec (.of k)) :=
    isConnectedCurve_of_smoothOfRelativeDimension_one _
  have : GlobalSectionsBijective k U.toScheme := GlobalSectionsBijective.of_isSepClosed
  obtain ⟨⟨e₀⟩, ⟨e₁⟩, ⟨e₂⟩, h₃⟩ :=
    IsConnectedCurve.sheafH_constantZMod_of_isProper (U.toScheme ↘ Spec (.of k)) ℓ hℓ
  refine ⟨Modules.finrankH_unit_zero, ?_, ?_, ?_, fun r hr ↦ ?_⟩
  · rw [Nat.card_congr e₀.toEquiv, Nat.card_zmod]
  · rw [Nat.card_congr e₁.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
      genus_eq_arithmeticGenus]
  · rw [Nat.card_congr e₂.toEquiv, Nat.card_zmod]
  · have := h₃ r hr
    exact Nat.card_of_subsingleton 0

/-- **`h⁰(Y, 𝒪_Y)` counts connected components.** On a smooth proper scheme `Y` of relative
dimension one over an algebraically closed field `k`, `dim_k H⁰(Y, 𝒪_Y)` is the number of
connected components of `Y`: cohomology splits over the components, each of which is a smooth
proper connected curve with `H⁰(D, 𝒪_D) = k`. -/
theorem finrankH_unit_zero_eq_natCard_connectedComponents [IsAlgClosed k] :
    Modules.finrankH k (SheafOfModules.unit Y.ringCatSheaf) 0 =
      Nat.card (_root_.ConnectedComponents Y) := by
  classical
  have := isNoetherian_of_isProper (Y ↘ Spec (.of k))
  have : Fintype (_root_.ConnectedComponents Y) := Fintype.ofFinite _
  have : (SheafOfModules.unit Y.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Modules.finiteDimensional_H_of_isProper (k := k)
    (SheafOfModules.unit Y.ringCatSheaf) 0
  rw [Modules.finrankH_eq_sum_of_pairwise_disjoint k _ pairwise_disjoint_on_connectedComponentOpens
    iSup_connectedComponentOpens _ 0, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  let : (Y.connectedComponentOpens c).toScheme.Over (Spec (.of k)) :=
    ⟨(Y.connectedComponentOpens c).ι ≫ Y ↘ Spec (.of k)⟩
  rw [Modules.finrankH_congr k (Modules.pullbackObjUnitIso _) 0]
  exact (connectedComponentOpens_facts c 1 (by simp)).1

/-- **Betti cardinalities of a smooth proper curve, possibly disconnected.** Let `Y` be smooth
proper of relative dimension one over an algebraically closed field `k`, with `c` connected
components and arithmetic genus `g = dim_k H¹(Y, 𝒪_Y)`, and let `ℓ` be invertible in `k`. Then
`|H⁰(Y, ℤ/ℓ)| = |H²(Y, ℤ/ℓ)| = ℓ^c`, `|H¹(Y, ℤ/ℓ)| = ℓ^{2g}` and `|Hʳ(Y, ℤ/ℓ)| = 1` for
`r > 2`. Cohomology splits over the connected components, which are smooth proper connected
curves, and `g` is the sum of their genera. -/
theorem natCard_sheafH_constantZMod_of_smoothOfRelativeDimension_one [IsAlgClosed k] (ℓ : ℕ)
    (hℓ : (ℓ : k) ≠ 0) :
    Nat.card (Sheaf.H (Y.constantZMod ℓ) 0) = ℓ ^ Nat.card (_root_.ConnectedComponents Y) ∧
      Nat.card (Sheaf.H (Y.constantZMod ℓ) 1) = ℓ ^ (2 * arithmeticGenus k Y) ∧
      Nat.card (Sheaf.H (Y.constantZMod ℓ) 2) = ℓ ^ Nat.card (_root_.ConnectedComponents Y) ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H (Y.constantZMod ℓ) r) = 1 := by
  classical
  have := isNoetherian_of_isProper (Y ↘ Spec (.of k))
  have : Fintype (_root_.ConnectedComponents Y) := Fintype.ofFinite _
  have hcard (q : ℕ) (hq : ∀ c, Nat.card (Sheaf.H
      ((Y.connectedComponentOpens c).toScheme.constantZMod ℓ) q) = ℓ) :
      Nat.card (Sheaf.H (Y.constantZMod ℓ) q) = ℓ ^ Nat.card (_root_.ConnectedComponents Y) := by
    rw [natCard_sheafH_constantZMod_eq_prod, Finset.prod_congr rfl fun c _ ↦ hq c,
      Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  refine ⟨hcard 0 fun c ↦ (connectedComponentOpens_facts c ℓ hℓ).2.1, ?_,
    hcard 2 fun c ↦ (connectedComponentOpens_facts c ℓ hℓ).2.2.2.1, fun r hr ↦ ?_⟩
  · have : (SheafOfModules.unit Y.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have : (SheafOfModules.unit Y.ringCatSheaf).IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
    have := Modules.finiteDimensional_H_of_isProper (k := k)
      (SheafOfModules.unit Y.ringCatSheaf) 1
    rw [natCard_sheafH_constantZMod_eq_prod, Finset.prod_congr rfl fun c _ ↦
      (connectedComponentOpens_facts c ℓ hℓ).2.2.1, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum,
      arithmeticGenus, Modules.finrankH_eq_sum_of_pairwise_disjoint k _
        pairwise_disjoint_on_connectedComponentOpens iSup_connectedComponentOpens _ 1]
    congr 2
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    let : (Y.connectedComponentOpens c).toScheme.Over (Spec (.of k)) :=
      ⟨(Y.connectedComponentOpens c).ι ≫ Y ↘ Spec (.of k)⟩
    exact (Modules.finrankH_congr k (Modules.pullbackObjUnitIso _) 1).symm
  · rw [natCard_sheafH_constantZMod_eq_prod]
    exact Finset.prod_eq_one fun c _ ↦ (connectedComponentOpens_facts c ℓ hℓ).2.2.2.2 r hr

end Scheme
namespace Etale

open Scheme

variable {X S : Scheme.{u}}

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Betti cardinalities in a smooth
projective curve family.

Let `S` be Noetherian, `f : X ⟶ S` smooth of relative dimension one and projective
(`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), and `ℓ` a prime invertible on `S`. For a
point `s` of `S` let `X_{s̄} = X ×_S Spec κ(s)‾` be the geometric fibre, `c_s` the number of its
connected components and `g_s = dim H¹(X_{s̄}, 𝒪)` its arithmetic genus. Then
`|H⁰(X_{s̄}, 𝔽_ℓ)| = |H²(X_{s̄}, 𝔽_ℓ)| = ℓ^{c_s}`, `|H¹(X_{s̄}, 𝔽_ℓ)| = ℓ^{2 g_s}` and
`|Hʳ(X_{s̄}, 𝔽_ℓ)| = 1` for `r > 2`, and `c` and `g` are constructible functions on `S`.

The cardinalities are
`AlgebraicGeometry.Scheme.natCard_sheafH_constantZMod_of_smoothOfRelativeDimension_one`; since
`c_s = h⁰(X_{s̄}, 𝒪)` (`AlgebraicGeometry.Scheme.finrankH_unit_zero_eq_natCard_connectedComponents`)
and `g_s = h¹(X_{s̄}, 𝒪)`, constructibility is the coherent base change statement
`AlgebraicGeometry.Scheme.Modules.finite_range_and_isConstructible_finrankH_geometricFibre` for
`𝒢 = 𝒪_X`, which is flat over `S`. -/
theorem natCard_sheafH_constantZMod_geometricFibre_of_smooth [IsNoetherian S] (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    let Xs : S → Scheme.{u} := fun s ↦ Limits.pullback f (S.geometricPointAt s)
    let c : S → ℕ := fun s ↦ Nat.card (_root_.ConnectedComponents (Xs s))
    let g : S → ℕ := fun s ↦
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      arithmeticGenus (AlgebraicClosure (S.residueField s)) (Xs s)
    (∀ s : S,
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 0) = ℓ ^ c s ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 1) = ℓ ^ (2 * g s) ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 2) = ℓ ^ c s ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) r) = 1) ∧
    ((Set.range c).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (c ⁻¹' {m})) ∧
    ((Set.range g).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (g ⁻¹' {m})) := by
  intro Xs c g
  have : IsProper f := hi ▸ inferInstance
  have hfib (s : S) :
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      SmoothOfRelativeDimension 1 (Xs s ↘ Spec (.of (AlgebraicClosure (S.residueField s)))) ∧
        IsProper (Xs s ↘ Spec (.of (AlgebraicClosure (S.residueField s)))) :=
    ⟨(smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›,
      IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›⟩
  -- `c s = h⁰(X_{s̄}, 𝒪)` and `g s = h¹(X_{s̄}, 𝒪)` are geometric fibre dimensions of `𝒪_X`
  have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit X.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hflat : Modules.IsFlatOver (SheafOfModules.unit X.ringCatSheaf) f :=
    Modules.isFlatOver_of_isInvertible f _
  have hrank (r : ℕ) := Modules.finite_range_and_isConstructible_finrankH_geometricFibre f i hi
    (SheafOfModules.unit X.ringCatSheaf) hflat r
  have hpull (s : S) (r : ℕ) :
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      ((Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj
        (SheafOfModules.unit X.ringCatSheaf)).finrankH (AlgebraicClosure (S.residueField s)) r =
        Modules.finrankH (AlgebraicClosure (S.residueField s))
          (SheafOfModules.unit (Xs s).ringCatSheaf) r :=
    by
    let : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
      ⟨pullback.snd f (S.geometricPointAt s)⟩
    exact Modules.finrankH_congr _ (Modules.pullbackObjUnitIso _) r
  have hc : c = fun s ↦
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      ((Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj
        (SheafOfModules.unit X.ringCatSheaf)).finrankH (AlgebraicClosure (S.residueField s)) 0 := by
    funext s
    let : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
      ⟨pullback.snd f (S.geometricPointAt s)⟩
    obtain ⟨_, _⟩ := hfib s
    rw [hpull s 0, finrankH_unit_zero_eq_natCard_connectedComponents]
  have hg : g = fun s ↦
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      ((Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj
        (SheafOfModules.unit X.ringCatSheaf)).finrankH (AlgebraicClosure (S.residueField s)) 1 := by
    funext s
    exact (hpull s 1).symm
  refine ⟨fun s ↦ ?_, hc ▸ hrank 0, hg ▸ hrank 1⟩
  let : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
    ⟨pullback.snd f (S.geometricPointAt s)⟩
  obtain ⟨_, _⟩ := hfib s
  -- `ℓ` is invertible in `κ(s)‾`
  have hℓs : (ℓ : AlgebraicClosure (S.residueField s)) ≠ 0 := by
    have h := hℓ.map ((algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s))).comp
      (S.presheaf.germ ⊤ s trivial ≫ S.residue s).hom)
    rw [map_natCast] at h
    exact h.ne_zero
  exact natCard_sheafH_constantZMod_of_smoothOfRelativeDimension_one ℓ hℓs

end Etale

end AlgebraicGeometry
