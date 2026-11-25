/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Data.Int.Interval
public import WeilConjectures.ConstructibleSheaf.Simple
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Complexes supported at closed points

A step of the proof of blueprint `theorem-verdier-biduality--1`: each cohomology sheaf of
the cone `Δ` has constructible support, and a constructible subset of a Noetherian finite type
`k`-scheme consisting of closed points is finite. Hence all the cohomology of `Δ` is supported
on a finite set of closed points, which is the underlying set of a closed subscheme finite over
`k`.

## Main statements

- `Set.Finite.of_isClosed_constructibleTopology`: in a Noetherian quasi-sober space, a subset of
  the closed points which is closed in the constructible topology is finite.
- `AlgebraicGeometry.Etale.finite_compl_stalkZeroLocus`: for a constructible sheaf `F` on a
  quasi-compact scheme locally of finite type over a field whose stalks vanish at all
  non-closed points, the support of `F` is a finite set of closed points.
- `AlgebraicGeometry.exists_opens_isFinite_closedComplement`: a finite set of closed points of a
  scheme locally of finite type over a field is the underlying set of a closed subscheme which
  is finite over the field.
- `AlgebraicGeometry.Etale.exists_isFinite_isZero_upperStar_of_boundedConstructible`: a bounded
  constructible complex whose homology sheaves vanish at all non-closed points restricts to
  zero on the complement of a closed subscheme finite over the base field.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

open scoped CategoryTheory.Functor

/-- In a Noetherian quasi-sober space, a set of closed points which is closed in the
constructible topology is finite: it is compact in the constructible topology, in which closed
points are open (their complements are quasi-compact opens). Used in the proof of blueprint
`theorem-verdier-biduality--1`. -/
theorem Set.Finite.of_isClosed_constructibleTopology {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {s : Set X} (hs : IsClosed[constructibleTopology X] s)
    (hs' : s ⊆ closedPoints X) : s.Finite := by
  let φ : WithConstructibleTopology X → X := WithTopology.ofTopology
  let ψ : X → WithConstructibleTopology X := WithTopology.toTopology _
  have hK : IsClosed (φ ⁻¹' s) := WithConstructibleTopology.isClosed_iff.2 hs
  have hopen (x : X) (hx : x ∈ s) : IsOpen ({ψ x} : Set (WithConstructibleTopology X)) := by
    rw [WithConstructibleTopology.isOpen_iff]
    have : WithTopology.toTopology _ ⁻¹' ({ψ x} : Set (WithConstructibleTopology X)) = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ congrArg WithTopology.ofTopology h, fun h ↦ h ▸ rfl⟩
    rw [this]
    exact (NoetherianSpace.isCompact _).isOpen_constructibleTopology_of_isClosed (hs' hx)
  obtain ⟨t, ht⟩ := hK.isCompact.elim_finite_subcover (fun y : φ ⁻¹' s ↦ {ψ (φ y)})
    (fun y ↦ hopen _ y.2) fun y hy ↦ Set.mem_iUnion.2 ⟨⟨y, hy⟩, rfl⟩
  refine ((t.finite_toSet.image fun y ↦ φ y.1)).subset fun x hx ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (show ψ x ∈ φ ⁻¹' s from hx))
  exact ⟨y, hy, congrArg WithTopology.ofTopology (Set.mem_singleton_iff.1 hxy).symm⟩

namespace AlgebraicGeometry

open Scheme

/-- A closed immersion with finitely many points into a scheme locally of finite type over a
field `k` is finite over `k`: it is quasi-compact, of finite type and has finite fibres, and
`Spec k` is Artinian. Used in the proof of blueprint `theorem-verdier-biduality--1`. -/
theorem isFinite_comp_of_finite_range {k : Type u} [Field k] {X Z : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : (Set.range i.base).Finite) : IsFinite (i ≫ a) := by
  have : Finite Z := Set.finite_range_iff i.isEmbedding.injective |>.1 hi
  have : QuasiCompact (i ≫ a) := inferInstance
  have : LocallyQuasiFinite (i ≫ a) :=
    (locallyQuasiFinite_iff_finite_preimage_singleton).2 fun _ ↦ Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite _

/-- A finite set of closed points of a scheme locally of finite type over a field `k` is the
underlying set of a closed subscheme finite over `k`: the closed complement of the open
complement. It has finitely many points and is of finite type over `k`, hence finite. Used in
the proof of blueprint `theorem-verdier-biduality--1`. -/
theorem exists_opens_isFinite_closedComplement {k : Type u} [Field k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] {S : Set X} (hS : S.Finite)
    (hS' : S ⊆ closedPoints X) :
    ∃ U : X.Opens, (U : Set X) = Sᶜ ∧ IsFinite (U.closedComplement ≫ a) := by
  have hcl : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hS.isClosed_biUnion fun x hx ↦ hS' hx
  refine ⟨⟨Sᶜ, hcl.isOpen_compl⟩, rfl, ?_⟩
  set U : X.Opens := ⟨Sᶜ, hcl.isOpen_compl⟩
  have hrange : Set.range U.closedComplement.base = S := by
    rw [Scheme.Opens.range_closedComplement]
    exact compl_compl S
  exact isFinite_comp_of_finite_range a U.closedComplement (hrange ▸ hS)

namespace Etale

variable {Λ : Type (u + 1)}

/-- Blueprint `theorem-verdier-biduality--1`: let `X` be quasi-compact and locally of
finite type over a field, and let `F` be a constructible sheaf of `Λ`-modules on `X_ét` whose
stalks vanish at all non-closed points. Then the support of `F` is a finite set of closed
points. The support is closed in the constructible topology
(`AlgebraicGeometry.Etale.isOpen_constructibleTopology_stalkZeroLocus`), and `X` is
Noetherian. -/
theorem finite_compl_stalkZeroLocus [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] [CompactSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)) :
    (stalkZeroLocus F)ᶜ.Finite ∧ (stalkZeroLocus F)ᶜ ⊆ closedPoints X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : IsNoetherian X := {}
  have hsub : (stalkZeroLocus F)ᶜ ⊆ closedPoints X := by
    intro x hx
    by_contra h
    refine hx ?_
    have := mem_stalkZeroLocus_of_isZero_sheafFiber F (X.algClosurePoint x) (hF x h)
    rwa [X.algClosurePoint_base] at this
  refine ⟨Set.Finite.of_isClosed_constructibleTopology ?_ hsub, hsub⟩
  exact @IsOpen.isClosed_compl X (constructibleTopology X) _
    (isOpen_constructibleTopology_stalkZeroLocus F)

/-- Blueprint `theorem-verdier-biduality--1`: let `X` be quasi-compact and locally of
finite type over a field `k`, with structure morphism `a`, and let `K ∈ D(X_ét, Λ)` be bounded
with constructible homology sheaves whose stalks vanish at all non-closed points. Then the
homology of `K` is supported on a finite set of closed points: there are a closed immersion
`i : Z ⟶ X` with `i ≫ a` finite and an open immersion `j : U ⟶ X` onto the complement of its
image with `j^* K = 0`. -/
theorem exists_isFinite_isZero_upperStar_of_boundedConstructible [CommRing Λ] {k : Type u}
    [Field k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] [CompactSpace X]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (h : ∀ (q : ℤ), ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K))) :
    ∃ (Z U : Scheme.{u}) (i : Z ⟶ X) (j : U ⟶ X), IsClosedImmersion i ∧ IsFinite (i ≫ a) ∧
      IsOpenImmersion j ∧ Set.range i.base = (Set.range j.base)ᶜ ∧
      IsZero (D((j)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨⟨⟨n₀, hn₀⟩, ⟨n₁, hn₁⟩⟩, hc⟩ := hK
  let H (q : ℤ) := (_root_.DerivedCategory.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj K
  let S : Set X := ⋃ q ∈ Finset.Icc n₀ n₁, (stalkZeroLocus (H q))ᶜ
  have hS : S.Finite := (Finset.Icc n₀ n₁).finite_toSet.biUnion fun q _ ↦
    have := hc q
    (finite_compl_stalkZeroLocus a (H q) (h q)).1
  have hS' : S ⊆ closedPoints X := Set.iUnion₂_subset fun q _ ↦
    have := hc q
    (finite_compl_stalkZeroLocus a (H q) (h q)).2
  have hsub (q : ℤ) : (stalkZeroLocus (H q))ᶜ ⊆ S := by
    by_cases hq : q ∈ Finset.Icc n₀ n₁
    · exact Set.subset_biUnion_of_mem (u := fun q ↦ (stalkZeroLocus (H q))ᶜ) hq
    · have hz : IsZero (H q) := by
        have hq' : q < n₀ ∨ n₁ < q := by
          rw [Finset.mem_Icc] at hq
          omega
        rcases hq' with h' | h'
        · exact (_root_.DerivedCategory.isGE_iff K n₀).1 hn₀ q h'
        · exact (_root_.DerivedCategory.isLE_iff K n₁).1 hn₁ q h'
      rw [(isZero_iff_stalkZeroLocus_eq_univ _).1 hz, Set.compl_univ]
      exact Set.empty_subset _
  obtain ⟨U, hU, hfin⟩ := exists_opens_isFinite_closedComplement a hS hS'
  refine ⟨_, U, U.closedComplement, U.ι, inferInstance, hfin, inferInstance, ?_, ?_⟩
  · rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
  refine _root_.DerivedCategory.isZero_of_forall_isZero_homology _ fun q ↦ ?_
  refine IsZero.of_iso ?_ ((((U.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso
    q).app K).symm
  refine (isZero_iff_stalkZeroLocus_eq_univ _).2 (Set.eq_univ_of_forall fun y ↦ ?_)
  refine mem_stalkZeroLocus_upperStar _ _ ?_
  by_contra hy
  have := hsub q hy
  rw [← compl_compl S, ← hU] at this
  exact this y.2

end Etale

end AlgebraicGeometry
