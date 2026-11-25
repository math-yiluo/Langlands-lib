/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import WeilConjectures.Mathlib.Topology.Compactification.StoneCech
public import WeilConjectures.Mathlib.Topology.ExtremallyDisconnected
public import WeilConjectures.Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
public import WeilConjectures.SixFunctors.ProEtale.Comparison

/-!
# The comparison direct image has unbounded cohomological dimension on all sheaves

Blueprint `rem-sf-fullcd-counterexample`: the comparison morphism `ν_U : U_proét ⟶ U_ét` can
have higher direct images `R^q ν_{U,*} F ≠ 0` in arbitrarily large degrees `q`, for sheaves `F`
that are not of étale origin. Hence the form `(G)` of the comparison bound, asked for *all*
pro-étale sheaves and uniformly over the pro-étale base changes, is false
(blueprints `rem-sf-fullcd-general-form` (2), `rem-ptr-weil-ambient-exceptional-adjoint-13`).

Let `K` be an algebraically closed field, `I` a discrete set of cardinality `ℵ_ω` and
`S = βI × βI`. Then `U = Spec C_lc(S, K)` is an affine pro-étale object of `(Spec K)_proét`
(`AlgebraicGeometry.ProEtale.locallyConstantProEt`): `C_lc(S, K)` is the filtered colimit of the
finite products `K^{S_i}` over the finite quotients `S_i` of `S`. Its étale topos is the topos of
sheaves on `S`, and for a finite field `Λ` of odd characteristic the constant sheaf `Λ` on
`βI × βI` has infinite injective dimension (Bergfalk–Lambie-Hanson, arXiv:2412.19605, Theorem
4.3). For `G` a sheaf on `S` with `Ext^q(G, Λ) ≠ 0` and `F_G = Hom_Λ(ν_U^* G, Λ)` one finds
`Γ(U_ét, R^q ν_{U,*} F_G) = Ext^q_{Sh(S, Λ)}(G, Λ) ≠ 0`.

Blueprint `rem-sf-fullcd-counterexample-locus` (i): the object `U` lives at a pro-étale limit.
It is a cofiltered limit of zero-dimensional finite-type `K`-schemes, but is itself not locally
of finite type over `K` (`AlgebraicGeometry.ProEtale.not_locallyOfFiniteType_locallyConstantProEt`),
so no finite-type bound applies to it.

## Main definitions

- `AlgebraicGeometry.ProEtale.locallyConstantProEt`: `Spec C_lc(T, K)` as an object of
  `(Spec K)_proét`, for a profinite `T`.

## Main statements

- `AlgebraicGeometry.ProEtale.exists_not_isZero_homology_rightDerivedComparisonLowerStar`:
  for every `M` there is a sheaf `F` on `U_proét` with `R^q ν_{U,*} F ≠ 0` for some `q > M`.
- `AlgebraicGeometry.ProEtale.not_exists_forall_isZero_homology_rightDerivedComparisonLowerStar`:
  the uniform form `(G)` of the comparison bound is false.
- `AlgebraicGeometry.ProEtale.not_locallyOfFiniteType_locallyConstantProEt`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

section LocallyConstant

variable (K : Type u) [Field K] (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T]

instance weaklyEtale_spec_map_algebraMap_locallyConstant :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K (LocallyConstant T K)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @WeaklyEtale)]
  exact RingHom.weaklyEtale_algebraMap_iff.2 inferInstance

/-- Blueprint `rem-sf-fullcd-counterexample` (i): for a profinite space `T`, the affine scheme
`Spec C_lc(T, K)` of locally constant `K`-valued functions on `T`, as an object of the small
pro-étale site of `Spec K`. The ring `C_lc(T, K)` is the filtered colimit of the finite products
`K^{T_i}` over the finite quotients `T_i` of `T`, hence ind-Zariski and in particular weakly étale
over `K`. -/
noncomputable def locallyConstantProEt : (Spec (.of K)).ProEt :=
  Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap K (LocallyConstant T K))))

end LocallyConstant

variable (K : Type u) [Field K] (I : Type u) [TopologicalSpace I] [DiscreteTopology I]

/-- Blueprint `rem-sf-fullcd-counterexample-locus` (i): for an infinite discrete set `I`, the
pro-étale object `U = Spec C_lc(βI × βI, K)` of `(Spec K)_proét` is not locally of finite type
over `K`. The clopen subsets `stoneCechClopen i ×ˢ univ`, `i ∈ I`, are pairwise disjoint and
nonempty, so `C_lc(βI × βI, K)` has infinitely many orthogonal nonzero idempotents and is not
Noetherian, whereas a `K`-algebra of finite type is. -/
theorem not_locallyOfFiniteType_locallyConstantProEt [Infinite I] :
    ¬ LocallyOfFiniteType (locallyConstantProEt K (StoneCech I × StoneCech I)).hom := by
  intro h
  have hft : (algebraMap K (LocallyConstant (StoneCech I × StoneCech I) K)).FiniteType :=
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).1 h
  have : Algebra.FiniteType K (LocallyConstant (StoneCech I × StoneCech I) K) :=
    RingHom.finiteType_algebraMap.1 hft
  have := Algebra.FiniteType.isNoetherianRing K (LocallyConstant (StoneCech I × StoneCech I) K)
  refine not_finite_iff_infinite.2 ‹_› (LocallyConstant.finite_of_isNoetherianRing (R := K)
    (U := fun i ↦ stoneCechClopen i ×ˢ Set.univ)
    (fun i ↦ (isClopen_stoneCechClopen i).prod isClopen_univ)
    (fun i ↦ ⟨(stoneCechUnit i, stoneCechUnit i), stoneCechUnit_mem_stoneCechClopen i, trivial⟩)
    fun i j hij ↦ ?_)
  exact Set.disjoint_prod.2 (.inl (pairwise_disjoint_stoneCechClopen hij))

/-- The pro-étale object `Spec C_lc(βI × βI, K)` of `(Spec K)_proét` of blueprint
`rem-sf-fullcd-counterexample`, for a discrete set `I`. -/
noncomputable abbrev stoneCechProdProEt : (Spec (.of K)).ProEt :=
  locallyConstantProEt K (StoneCech I × StoneCech I)

variable (Λ : Type (u + 1)) [Field Λ] [Finite Λ]

/-- Blueprint `rem-sf-fullcd-counterexample` (iv)–(vi): let `K` be algebraically closed, `I` a
discrete set of cardinality `ℵ_ω`, `U = Spec C_lc(βI × βI, K)` and `Λ` a finite field of odd
characteristic. For every `M` there are a sheaf `F` of `Λ`-modules on `U_proét` and `q > M` with
`R^q ν_{U,*} F ≠ 0`.

By Bergfalk–Lambie-Hanson (arXiv:2412.19605, Theorem 4.3) the constant sheaf `Λ` on `βI × βI`
has infinite injective dimension, so there are a sheaf `G` on `βI × βI` (equivalently on `U_ét`)
and `q > M` with `Ext^q(G, Λ) ≠ 0`. The sheaf `F_G = Hom_Λ(ν_U^* G, Λ)` has no higher derived
`Hom` (the constant sheaf `Λ` is injective on the extremally disconnected basis objects of
`U_proét`), so `RΓ(U_proét, F_G) = RHom(G, Rν_{U,*} Λ) = RHom(G, Λ)`; as `Γ(U_ét, -)` is exact,
`Γ(U_ét, R^q ν_{U,*} F_G) = Ext^q(G, Λ) ≠ 0`. -/
theorem exists_not_isZero_homology_rightDerivedComparisonLowerStar [IsAlgClosed K]
    (hΛ : ringChar Λ ≠ 2) (hI : Cardinal.mk I = Cardinal.aleph Ordinal.omega0) (M : ℕ) :
    ∃ (F : Sheaf (Scheme.ProEt.topology (stoneCechProdProEt K I).left) (ModuleCat.{u + 1} Λ))
      (q : ℤ), M < q ∧ ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((R(ν_*((stoneCechProdProEt K I).left)[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

/-- Blueprints `rem-sf-fullcd-general-form` (2), `rem-ptr-weil-ambient-exceptional-adjoint-13`:
the all-sheaves, uniform-in-the-base-change form `(G)` of the comparison bound is false. Already
for `Y = Spec K` with `K` algebraically closed there is no `M` such that `R^q ν_{V,*} F = 0` for
all `q > M`, all objects `V` of `(Spec K)_proét` and all sheaves `F` of `Λ`-modules on
`V_proét`, `Λ` a finite field of odd characteristic: the object
`V = Spec C_lc(βI × βI, K)` with `|I| = ℵ_ω` violates every bound
(`AlgebraicGeometry.ProEtale.exists_not_isZero_homology_rightDerivedComparisonLowerStar`). -/
theorem not_exists_forall_isZero_homology_rightDerivedComparisonLowerStar [IsAlgClosed K]
    (hΛ : ringChar Λ ≠ 2) :
    ¬ ∃ M : ℕ, ∀ (V : (Spec (.of K)).ProEt)
      (F : Sheaf (Scheme.ProEt.topology V.left) (ModuleCat.{u + 1} Λ)) (q : ℤ), M < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((R(ν_*(V.left)[ModuleCat.{u + 1} Λ])).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  rintro ⟨M, hM⟩
  let J : Type u := (Cardinal.aleph Ordinal.omega0 : Cardinal.{u}).out
  let : TopologicalSpace J := ⊥
  have : DiscreteTopology J := ⟨rfl⟩
  obtain ⟨F, q, hq, hF⟩ := exists_not_isZero_homology_rightDerivedComparisonLowerStar K J Λ hΛ
    (Cardinal.mk_out _) M
  exact hF (hM _ F q hq)

end ProEtale

end AlgebraicGeometry
