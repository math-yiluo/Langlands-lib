/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import WeilConjectures.WeilSheaf.CondensedModelFiniteLevel

/-!
# Effective descent of objects along pro-étale coverings and Galois descent data

To realise a representation of the arithmetic fundamental group (or a Weil sheaf on the geometric
fibre `X̄`) as a lisse `ℚ̲̄_ℓ`-sheaf on the model `X₀` in the condensed model, one has to descend
*objects* along the coverings `X₀ ⊗_k K ⟶ X₀` and `X̄ ⟶ X₀`; descent of *morphisms* is
`WeilConjectures.WeilSheaf.CondensedModelDescent`. This file supplies the object-level tools.

## Effective descent (Beck)

* `CategoryTheory.Comonad.comonadicOfFaithfulOfPreservesFiniteLimits`,
  `CategoryTheory.Comonad.isEquivalence_comparison_of_faithful_of_preservesFiniteLimits`: a faithful
  left exact left adjoint out of an abelian category is comonadic; explicitly
  (`CategoryTheory.Comonad.isIso_map_equalizerι_comp_counit`) a coalgebra `(N, δ)` is `F M` for the
  equalizer `M` of `G δ, η_{G N} : G N ⇉ G F G N`.
* `AlgebraicGeometry.ProEtale.isEquivalence_comparison_upperStarLowerStarAdjunction_ab` and
  `AlgebraicGeometry.ProEtale.CondensedRing.isEquivalence_comparison_upperStarLowerStarAdjunction`:
  for a quasi-compact surjective weakly étale `q : Y ⟶ X`, abelian sheaves, resp. module objects
  over a condensed ring `Λ`, on `X` are equivalent to coalgebras over `q^* q_*`; in object form
  `AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_obj_iso_of_coalgebra`. This applies to
  the geometric fibre `X̄ ⟶ X₀` (`isEquivalence_comparison_geometricFiberProj`) and to the finite
  levels `X₀ ⊗_k K ⟶ X₀` (`isEquivalence_comparison_finiteLevelProj`).

## Galois descent data

For `L ⊣ R` and endofunctors `S σ` (`σ` in a monoid `Γ`) with `κ σ : L ⋙ S σ ≅ L`
(`L = q^*`, `S σ = (ρ σ)^*` for an action `ρ` of `Γ` on `Y` over `X`), a *Galois descent datum* on
`N` is a family `ψ σ : N ⟶ S σ N`, trivial at `1` and satisfying the cocycle condition
(`CategoryTheory.Adjunction.IsGaloisDescentDatum`). The *Galois comparison*
`L R N ⟶ ∏_σ S σ N` (`CategoryTheory.Adjunction.galoisComparison`) has components `(κ σ)⁻¹` followed
by `S σ` of the counit.

* `CategoryTheory.Adjunction.galoisCoalgebra`: if the Galois comparisons of `N` and `L R N` are
  isomorphisms, a Galois descent datum on `N` is a coalgebra structure over `L ⋙ R`.
* `CategoryTheory.Adjunction.exists_iso_of_isGaloisDescentDatum`: combined with Beck's theorem, the
  datum is then effective, `N ≅ L M` compatibly with the data.
* `AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_obj_iso_of_galoisDescentDatum`: the
  case of module objects over `Λ` along `q`, for an action `ρ` of a finite monoid `Γ` on `Y` over
  `X`, with the coherences of the canonical isomorphisms `(ρ σ)^* q^* ≅ q^*`
  (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_id`
  and its multiplicative analogue `…_of_eq_comp`).

## What remains

The hypothesis of the last theorem that the Galois comparison `q^* q_* N ⟶ ∏_σ (ρ σ)^* N` is an
isomorphism is the geometric input `Y ×_X Y ≅ ∐_σ Y` of a finite Galois covering: on the sections
over `W ⟶ Y` it is the restriction `N(W ×_X Y) ⟶ ∏_σ N(W)` along the graphs `(𝟙, ρ σ)`, which is
bijective when these graphs form a disjoint open covering
(`AlgebraicGeometry.ProEtale.isLimitSectionsFanOfIsColimitCofan`), i.e. for a free
`AlgebraicGeometry.ProEtale.IsGaloisAction`. It is not proved here.
-/

@[expose] public section

universe v u' u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Comonad

variable {C : Type u'} {D : Type*} [Category.{v} C] [Category.{v} D] [Abelian C]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Faithful] [PreservesFiniteLimits F]

/-- **Beck's comonadicity theorem for exact functors**: a faithful left adjoint `F` out of an
abelian category which preserves finite limits is comonadic. It reflects isomorphisms, being
faithful on the balanced category `C`, and preserves all equalizers. -/
@[instance_reducible]
noncomputable def comonadicOfFaithfulOfPreservesFiniteLimits : ComonadicLeftAdjoint F :=
  have : HasEqualizerOfIsCosplitPair F := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesLimitOfIsCosplitPair F := ⟨fun _ _ _ ↦ inferInstance⟩
  comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms adj

/-- The comparison functor from `C` to the coalgebras over the comonad `F ⋙ G` is an equivalence
for a faithful left adjoint `F` out of an abelian category which preserves finite limits. -/
lemma isEquivalence_comparison_of_faithful_of_preservesFiniteLimits :
    (comparison adj).IsEquivalence :=
  (comonadicOfFaithfulOfPreservesFiniteLimits adj).eqv

/-- **Effective descent**, explicit form: for a faithful left adjoint `F` out of an abelian
category which preserves finite limits and a coalgebra `(N, δ)` over `F ⋙ G`, the equalizer `M`
of `G δ, η_{G N} : G N ⇉ G F G N` satisfies `F M ≅ N`, by the composite
`F M ⟶ F G N ⟶ N` of the inclusion and the counit. -/
lemma isIso_map_equalizerι_comp_counit (A : adj.toComonad.Coalgebra) :
    IsIso (F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) ≫ adj.counit.app A.A) := by
  have := isEquivalence_comparison_of_faithful_of_preservesFiniteLimits adj
  have h := ComonadicityInternal.comparisonAdjunction_counit_f_aux (adj := adj) A
  rw [Adjunction.homEquiv_counit] at h
  rw [← h]
  exact (Comonad.forget _).map_isIso
    ((ComonadicityInternal.comparisonAdjunction adj).counit.app A)

/-- **Effective descent**, coalgebra form: every coalgebra over `F ⋙ G` is isomorphic to the
coalgebra `(F M, F η_M)` of an object `M` of `C`. -/
lemma exists_nonempty_comparison_obj_iso (A : adj.toComonad.Coalgebra) :
    ∃ M : C, Nonempty ((comparison adj).obj M ≅ A) :=
  have := isEquivalence_comparison_of_faithful_of_preservesFiniteLimits adj
  ⟨_, ⟨(comparison adj).objObjPreimageIso A⟩⟩

end CategoryTheory.Comonad

/-! ### Effective descent along pro-étale coverings -/

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [WeaklyEtale q] [Surjective q] [QuasiCompact q]

/-- **Effective descent of abelian sheaves along a pro-étale covering**: for a quasi-compact
surjective weakly étale `q : Y ⟶ X`, the pullback `q^*` of abelian pro-étale sheaves is
comonadic: abelian sheaves on `X` are equivalent to coalgebras over the comonad `q^* q_*`. -/
lemma isEquivalence_comparison_upperStarLowerStarAdjunction_ab :
    (Comonad.comparison (upperStarLowerStarAdjunction Ab.{u + 1} q)).IsEquivalence :=
  Comonad.isEquivalence_comparison_of_faithful_of_preservesFiniteLimits _

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Effective descent of module objects along a pro-étale covering**: for a quasi-compact
surjective weakly étale `q : Y ⟶ X`, the pullback `q^*` of module objects over `Λ` is
comonadic: module objects on `X` are equivalent to coalgebras over the comonad `q^* q_*`. -/
lemma isEquivalence_comparison_upperStarLowerStarAdjunction :
    (Comonad.comparison (upperStarLowerStarAdjunction Λ q)).IsEquivalence :=
  Comonad.isEquivalence_comparison_of_faithful_of_preservesFiniteLimits _

/-- **Effective descent of module objects**, object form: every coalgebra `(N, N ⟶ q^* q_* N)`
over the comonad `q^* q_*` is `q^* M` for a module object `M` on `X`, compatibly with the
coalgebra structures. -/
lemma exists_upperStar_obj_iso_of_coalgebra
    (A : (upperStarLowerStarAdjunction Λ q).toComonad.Coalgebra) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (e : (q)^*⟦Λ⟧.obj M ≅ A.A),
      (q)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ q).unit.app M) ≫
        (q)^*⟦Λ⟧.map ((q)_*⟦Λ⟧.map e.hom) = e.hom ≫ A.a := by
  obtain ⟨M, ⟨i⟩⟩ := Comonad.exists_nonempty_comparison_obj_iso _ A
  exact ⟨M, (Comonad.forget _).mapIso i, i.hom.h⟩

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- Effective descent of module objects along the projection `X̄ ⟶ X₀` of the geometric fibre
over a finite field: module objects on `X₀` are coalgebras over `p^* p_*` on `X̄`. -/
lemma isEquivalence_comparison_geometricFiberProj [Finite k] :
    (Comonad.comparison (upperStarLowerStarAdjunction Λ f.geometricFiberProj)).IsEquivalence :=
  isEquivalence_comparison_upperStarLowerStarAdjunction _ Λ

/-- Effective descent of module objects along the projection `X₀ ⊗_k K ⟶ X₀` of a finite level
(more generally of a separable algebraic extension `K / k`). -/
lemma isEquivalence_comparison_finiteLevelProj (K : Type u) [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] :
    (Comonad.comparison (upperStarLowerStarAdjunction Λ (f.finiteLevelProj K))).IsEquivalence :=
  isEquivalence_comparison_upperStarLowerStarAdjunction _ Λ

end CondensedRing

end AlgebraicGeometry.ProEtale

/-! ### Galois descent data and coalgebras -/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {Γ : Type*} (S : Γ → D ⥤ D) (κ : ∀ σ, L ⋙ S σ ≅ L)

/-- Let `L ⊣ R` and let `S σ` be endofunctors of `D` with isomorphisms `κ σ : L ⋙ S σ ≅ L` (for
`L` the pullback along a covering `q : Y ⟶ X`, `S σ` the pullback along an automorphism `σ` of
`Y` over `X` and `κ σ` the canonical isomorphism `σ^* q^* ≅ (σ ≫ q)^* = q^*`). The
*Galois component* `L R N ⟶ S σ N` is `(κ σ)⁻¹` followed by `S σ` of the counit; for a Galois
covering they form the isomorphism `q^* q_* N ≅ ∏_σ σ^* N`. -/
def galoisComponent (σ : Γ) (N : D) : L.obj (R.obj N) ⟶ (S σ).obj N :=
  (κ σ).inv.app (R.obj N) ≫ (S σ).map (adj.counit.app N)

@[reassoc]
lemma map_map_galoisComponent (σ : Γ) {N N' : D} (f : N ⟶ N') :
    L.map (R.map f) ≫ adj.galoisComponent S κ σ N' = adj.galoisComponent S κ σ N ≫ (S σ).map f := by
  rw [galoisComponent, galoisComponent, (κ σ).inv.naturality_assoc, Category.assoc,
    ← Functor.map_comp, ← adj.counit_naturality, Functor.map_comp]
  rfl

@[reassoc]
lemma map_unit_galoisComponent (σ : Γ) (M : C) :
    L.map (adj.unit.app M) ≫ adj.galoisComponent S κ σ (L.obj M) = (κ σ).inv.app M := by
  rw [galoisComponent]
  erw [(κ σ).inv.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp]
  simp

variable [Monoid Γ] (ε₀ : S 1 ≅ 𝟭 D) (μ : ∀ σ τ, S (σ * τ) ≅ S τ ⋙ S σ)

/-- A *Galois descent datum* on an object `N` of `D` relative to `(S, ε₀, μ)`: morphisms
`ψ σ : N ⟶ S σ N` which are the identity for `σ = 1` and satisfy the cocycle condition
`ψ σ ≫ S σ (ψ τ) = ψ (σ τ)` (up to `μ`). -/
structure IsGaloisDescentDatum {N : D} (ψ : ∀ σ, N ⟶ (S σ).obj N) : Prop where
  one : ψ 1 ≫ ε₀.hom.app N = 𝟙 N
  mul (σ τ : Γ) : ψ σ ≫ (S σ).map (ψ τ) = ψ (σ * τ) ≫ (μ σ τ).hom.app N

variable {S κ ε₀ μ}

lemma galoisComponent_one_comp (hκ₁ : ∀ M, (κ 1).hom.app M = ε₀.hom.app (L.obj M)) (N : D) :
    adj.galoisComponent S κ 1 N ≫ ε₀.hom.app N = adj.counit.app N := by
  rw [galoisComponent, Category.assoc, ε₀.hom.naturality, Functor.id_map, ← hκ₁,
    Iso.inv_hom_id_app_assoc]

lemma inv_app_comp_map_inv_app
    (hκ : ∀ σ τ M, (κ (σ * τ)).hom.app M =
      (μ σ τ).hom.app (L.obj M) ≫ (S σ).map ((κ τ).hom.app M) ≫ (κ σ).hom.app M)
    (σ τ : Γ) (M : C) :
    (κ σ).inv.app M ≫ (S σ).map ((κ τ).inv.app M) =
      (κ (σ * τ)).inv.app M ≫ (μ σ τ).hom.app (L.obj M) := by
  rw [← cancel_epi ((κ (σ * τ)).hom.app M), Iso.hom_inv_id_app_assoc, hκ σ τ M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Functor.comp_obj, Functor.map_id, Category.comp_id]

variable [HasLimitsOfShape (Discrete Γ) D]

variable (S κ) in
/-- The morphism `L R N ⟶ ∏_σ S σ N` with components the `galoisComponent`s; for a Galois
covering it is the isomorphism `q^* q_* N ≅ ∏_σ σ^* N`. -/
noncomputable def galoisComparison (N : D) : L.obj (R.obj N) ⟶ ∏ᶜ fun σ ↦ (S σ).obj N :=
  Pi.lift fun σ ↦ adj.galoisComponent S κ σ N

omit [Monoid Γ] in
@[reassoc (attr := simp)]
lemma galoisComparison_π (N : D) (σ : Γ) :
    adj.galoisComparison S κ N ≫ Pi.π _ σ = adj.galoisComponent S κ σ N :=
  Pi.lift_comp_π _ _

omit [Monoid Γ] in
/-- If the `galoisComparison` of `N` is an isomorphism and `S σ` preserves products, morphisms to
`S σ (L R N)` are determined by their composites with the `S σ` of the `galoisComponent`s. -/
lemma hom_ext_of_isIso_galoisComparison {N : D} [IsIso (adj.galoisComparison S κ N)] (σ : Γ)
    [PreservesLimitsOfShape (Discrete Γ) (S σ)] {Z : D} {f g : Z ⟶ (S σ).obj (L.obj (R.obj N))}
    (h : ∀ τ, f ≫ (S σ).map (adj.galoisComponent S κ τ N) =
      g ≫ (S σ).map (adj.galoisComponent S κ τ N)) : f = g := by
  rw [← cancel_mono ((S σ).map (adj.galoisComparison S κ N))]
  refine (isLimitOfPreserves (S σ)
    (limit.isLimit (Discrete.functor fun τ ↦ (S τ).obj N))).hom_ext fun ⟨τ⟩ ↦ ?_
  simp only [Functor.mapCone_π_app, limit.cone_π, Category.assoc, ← Functor.map_comp]
  erw [galoisComparison_π]
  exact h τ

variable (S κ) in
/-- The candidate coalgebra structure `N ⟶ L R N` of a family `ψ σ : N ⟶ S σ N`, when the
`galoisComparison` of `N` is an isomorphism: the unique morphism with `galoisComponent`s the
`ψ σ`. -/
noncomputable def galoisCoalgebraStr (N : D) [IsIso (adj.galoisComparison S κ N)]
    (ψ : ∀ σ, N ⟶ (S σ).obj N) : N ⟶ L.obj (R.obj N) :=
  Pi.lift ψ ≫ inv (adj.galoisComparison S κ N)

omit [Monoid Γ] in
@[reassoc (attr := simp)]
lemma galoisCoalgebraStr_galoisComponent (N : D) [IsIso (adj.galoisComparison S κ N)]
    (ψ : ∀ σ, N ⟶ (S σ).obj N) (σ : Γ) :
    adj.galoisCoalgebraStr S κ N ψ ≫ adj.galoisComponent S κ σ N = ψ σ := by
  rw [galoisCoalgebraStr, ← galoisComparison_π, Category.assoc, IsIso.inv_hom_id_assoc,
    Pi.lift_comp_π]

/-- **Galois descent data are coalgebras**: when the `galoisComparison`s of `N` and of `L R N` are
isomorphisms (for instance for a Galois covering, where `q^* q_* ≅ ∏_σ σ^*`), a Galois descent
datum `ψ` on `N` makes `N` a coalgebra over the comonad `L ⋙ R`, with structure morphism
`galoisCoalgebraStr`. -/
noncomputable def galoisCoalgebra (hκ₁ : ∀ M, (κ 1).hom.app M = ε₀.hom.app (L.obj M))
    (hκ : ∀ σ τ M, (κ (σ * τ)).hom.app M =
      (μ σ τ).hom.app (L.obj M) ≫ (S σ).map ((κ τ).hom.app M) ≫ (κ σ).hom.app M)
    [∀ σ, PreservesLimitsOfShape (Discrete Γ) (S σ)] (N : D)
    [IsIso (adj.galoisComparison S κ N)] [IsIso (adj.galoisComparison S κ (L.obj (R.obj N)))]
    {ψ : ∀ σ, N ⟶ (S σ).obj N} (hψ : IsGaloisDescentDatum S ε₀ μ ψ) :
    adj.toComonad.Coalgebra where
  A := N
  a := adj.galoisCoalgebraStr S κ N ψ
  counit := by
    rw [toComonad_ε, ← adj.galoisComponent_one_comp hκ₁ N,
      galoisCoalgebraStr_galoisComponent_assoc, hψ.one]
  coassoc := by
    have e : (adj.toComonad : D ⥤ D).map (adj.galoisCoalgebraStr S κ N ψ) =
        L.map (R.map (adj.galoisCoalgebraStr S κ N ψ)) := rfl
    rw [← cancel_mono (adj.galoisComparison S κ (L.obj (R.obj N)))]
    refine Pi.hom_ext _ _ fun σ ↦ ?_
    simp only [Category.assoc, galoisComparison_π, toComonad_δ, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    refine adj.hom_ext_of_isIso_galoisComparison (κ := κ) σ fun τ ↦ ?_
    simp only [Category.assoc]
    rw [e]
    erw [map_unit_galoisComponent_assoc]
    rw [map_map_galoisComponent_assoc,
      galoisCoalgebraStr_galoisComponent_assoc, ← Functor.map_comp,
      galoisCoalgebraStr_galoisComponent, hψ.mul, galoisComponent, Functor.map_comp]
    erw [reassoc_of% (inv_app_comp_map_inv_app hκ σ τ (R.obj N))]
    erw [← (μ σ τ).hom.naturality (adj.counit.app N)]
    rw [← adj.galoisCoalgebraStr_galoisComponent_assoc (κ := κ) N ψ (σ * τ), galoisComponent,
      Category.assoc]
    rfl

/-- **Effective Galois descent**, abstract form: let `L ⊣ R` with `L` faithful and left exact out
of an abelian category (so that `L` is comonadic,
`CategoryTheory.Comonad.isEquivalence_comparison_of_faithful_of_preservesFiniteLimits`). If the
`galoisComparison`s of `N` and `L R N` are isomorphisms, every Galois descent datum `ψ` on `N`
is effective: `N ≅ L M` for some `M`, the datum `ψ` corresponding to the canonical isomorphisms
`(κ σ)⁻¹ : L M ≅ S σ (L M)`. -/
theorem exists_iso_of_isGaloisDescentDatum [Abelian C] [L.Faithful] [PreservesFiniteLimits L]
    (hκ₁ : ∀ M, (κ 1).hom.app M = ε₀.hom.app (L.obj M))
    (hκ : ∀ σ τ M, (κ (σ * τ)).hom.app M =
      (μ σ τ).hom.app (L.obj M) ≫ (S σ).map ((κ τ).hom.app M) ≫ (κ σ).hom.app M)
    [∀ σ, PreservesLimitsOfShape (Discrete Γ) (S σ)] (N : D)
    [IsIso (adj.galoisComparison S κ N)] [IsIso (adj.galoisComparison S κ (L.obj (R.obj N)))]
    {ψ : ∀ σ, N ⟶ (S σ).obj N} (hψ : IsGaloisDescentDatum S ε₀ μ ψ) :
    ∃ (M : C) (e : L.obj M ≅ N), ∀ σ, e.hom ≫ ψ σ = (κ σ).inv.app M ≫ (S σ).map e.hom := by
  obtain ⟨M, ⟨i⟩⟩ :=
    Comonad.exists_nonempty_comparison_obj_iso adj (adj.galoisCoalgebra hκ₁ hκ N hψ)
  refine ⟨M, (Comonad.forget _).mapIso i, fun σ ↦ ?_⟩
  have h : L.map (adj.unit.app M) ≫ L.map (R.map i.hom.f) =
      i.hom.f ≫ adj.galoisCoalgebraStr S κ N ψ := i.hom.h
  rw [Functor.mapIso_hom, Comonad.forget_map,
    ← adj.galoisCoalgebraStr_galoisComponent (κ := κ) N ψ σ, ← Category.assoc, ← h,
    Category.assoc]
  erw [map_map_galoisComponent, map_unit_galoisComponent_assoc]
  rfl

end CategoryTheory.Adjunction

/-! ### Galois descent of module objects -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (q : Y ⟶ X)

/-- The canonical isomorphisms `s^* q^* ≅ (s ≫ q)^* = q^*` are multiplicative
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp_inv_upperStarCongr_hom_app_comp`, with an
arbitrary proof of `(s ≫ t) ≫ q = q`). -/
lemma upperStarComp_inv_app_upperStarCongr_hom_app_comp' {s t : Y ⟶ Y}
    (hs : s ≫ q = q) (ht : t ≫ q = q) (hst : (s ≫ t) ≫ q = q)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ (s ≫ t) q).inv.app M ≫ (upperStarCongr Λ hst).hom.app M =
      (upperStarComp Λ s t).hom.app ((q)^*⟦Λ⟧.obj M) ≫
        (s)^*⟦Λ⟧.map ((upperStarComp Λ t q).inv.app M ≫ (upperStarCongr Λ ht).hom.app M) ≫
        (upperStarComp Λ s q).inv.app M ≫ (upperStarCongr Λ hs).hom.app M := by
  rw [← cancel_epi ((upperStarComp Λ (s ≫ t) q).hom.app M), Iso.hom_inv_id_app_assoc,
    reassoc_of% (upperStarComp_hom_app_comp_upperStarComp_hom_app Λ s t q M),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc,
    upperStarComp_hom_app_map_upperStarCongr_hom_app_assoc, Iso.hom_inv_id_app_assoc]
  simp only [upperStarCongr_hom_app_eq_eqToHom, eqToHom_trans]

/-- The canonical isomorphism `(𝟙 Y)^* q^* ≅ (𝟙 Y ≫ q)^* = q^*` is the identity isomorphism
`(𝟙 Y)^* ≅ 𝟭`. -/
lemma upperStarComp_inv_app_upperStarCongr_hom_app_id
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ (𝟙 Y) q).inv.app M ≫ (upperStarCongr Λ (Category.id_comp q)).hom.app M =
      (upperStarId Λ Y).hom.app ((q)^*⟦Λ⟧.obj M) := by
  rw [upperStarComp_id_left]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  exact Category.comp_id _

lemma upperStarCongr_hom_app_upperStarComp_hom_app {a b : Y ⟶ Y} (e : a = b)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarCongr Λ (congrArg (· ≫ q) e)).hom.app M ≫ (upperStarComp Λ b q).hom.app M =
      (upperStarComp Λ a q).hom.app M ≫ (upperStarCongr Λ e).hom.app ((q)^*⟦Λ⟧.obj M) := by
  subst e
  simp [upperStarCongr_self]

/-- `upperStarComp_inv_app_upperStarCongr_hom_app_id` for an arbitrary proof of
`𝟙 Y ≫ q = q`. -/
lemma upperStarComp_inv_app_upperStarCongr_hom_app_id' (h : 𝟙 Y ≫ q = q)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ (𝟙 Y) q).inv.app M ≫ (upperStarCongr Λ h).hom.app M =
      (upperStarId Λ Y).hom.app ((q)^*⟦Λ⟧.obj M) := by
  obtain rfl : h = Category.id_comp q := rfl
  exact upperStarComp_inv_app_upperStarCongr_hom_app_id Λ q M

/-- Moving the canonical isomorphism `s^* q^* ≅ q^*` along an equation `s = s'`. -/
lemma upperStarComp_inv_app_upperStarCongr_hom_app_of_eq {s s' : Y ⟶ Y} (hs : s ≫ q = q)
    (hs' : s' ≫ q = q) (e : s = s')
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ s q).inv.app M ≫ (upperStarCongr Λ hs).hom.app M =
      (upperStarCongr Λ e).hom.app ((q)^*⟦Λ⟧.obj M) ≫
        (upperStarComp Λ s' q).inv.app M ≫ (upperStarCongr Λ hs').hom.app M := by
  rw [← cancel_epi ((upperStarComp Λ s q).hom.app M), Iso.hom_inv_id_app_assoc,
    ← reassoc_of% (upperStarCongr_hom_app_upperStarComp_hom_app Λ q e M),
    Iso.hom_inv_id_app_assoc]
  simp only [upperStarCongr_hom_app_eq_eqToHom, eqToHom_trans]

/-- `upperStarComp_inv_app_upperStarCongr_hom_app_id` for an endomorphism equal to `𝟙 Y`. -/
lemma upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_id {s : Y ⟶ Y} (hs : s ≫ q = q)
    (e : s = 𝟙 Y) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ s q).inv.app M ≫ (upperStarCongr Λ hs).hom.app M =
      (upperStarCongr Λ e).hom.app ((q)^*⟦Λ⟧.obj M) ≫
        (upperStarId Λ Y).hom.app ((q)^*⟦Λ⟧.obj M) := by
  rw [← upperStarComp_inv_app_upperStarCongr_hom_app_id' Λ q (Category.id_comp q),
    upperStarComp_inv_app_upperStarCongr_hom_app_of_eq Λ q hs (Category.id_comp q) e]

/-- `upperStarComp_inv_app_upperStarCongr_hom_app_comp'` for an endomorphism equal to
`s ≫ t`. -/
lemma upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_comp {s t w : Y ⟶ Y} (hs : s ≫ q = q)
    (ht : t ≫ q = q) (hw : w ≫ q = q) (e : w = s ≫ t)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ w q).inv.app M ≫ (upperStarCongr Λ hw).hom.app M =
      (upperStarCongr Λ e).hom.app ((q)^*⟦Λ⟧.obj M) ≫
        (upperStarComp Λ s t).hom.app ((q)^*⟦Λ⟧.obj M) ≫
        (s)^*⟦Λ⟧.map ((upperStarComp Λ t q).inv.app M ≫ (upperStarCongr Λ ht).hom.app M) ≫
        (upperStarComp Λ s q).inv.app M ≫ (upperStarCongr Λ hs).hom.app M := by
  rw [← upperStarComp_inv_app_upperStarCongr_hom_app_comp' Λ q hs ht (by rw [← e]; exact hw) M,
    upperStarComp_inv_app_upperStarCongr_hom_app_of_eq Λ q hw _ e]

variable [WeaklyEtale q] {Γ : Type*} [Monoid Γ] (ρ : Γ → (Y ⟶ Y)) (hρ : ∀ σ, ρ σ ≫ q = q)

/-- The comparison morphism `q^* q_* N ⟶ ∏_σ (ρ σ)^* N` of module objects for a finite monoid
`Γ` acting on `Y` over `X` through `ρ`: its components are the inverses of the canonical
isomorphisms `(ρ σ)^* q^* ≅ (ρ σ ≫ q)^* = q^*` at `q_* N`, followed by `(ρ σ)^*` of the counit
(`CategoryTheory.Adjunction.galoisComparison`). For a Galois covering it is an isomorphism. -/
noncomputable abbrev galoisComparison [Finite Γ]
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  (upperStarLowerStarAdjunction Λ q).galoisComparison (fun σ ↦ (ρ σ)^*⟦Λ⟧)
    (fun σ ↦ (upperStarComp Λ (ρ σ) q).symm ≪≫ upperStarCongr Λ (hρ σ)) N

/-- **Effective Galois descent of module objects**, conditional form. Let `q : Y ⟶ X` be a
quasi-compact surjective weakly étale morphism and `ρ` an action of a finite monoid `Γ` on `Y`
over `X` (e.g. of the Galois group of a finite Galois covering). Let `N` be a module object on
`Y` with a Galois descent datum `ψ σ : N ⟶ (ρ σ)^* N`: the identity for `σ = 1` and satisfying the
cocycle condition `ψ σ ≫ (ρ σ)^* (ψ τ) = ψ (σ τ)` (up to `(ρ σ ≫ ρ τ)^* ≅ (ρ τ)^* (ρ σ)^*`). If
the comparison morphisms `q^* q_* N ⟶ ∏_σ (ρ σ)^* N` and
`q^* q_* (q^* q_* N) ⟶ ∏_σ (ρ σ)^* (q^* q_* N)` are isomorphisms (the content of
`Y ×_X Y ≅ ∐_σ Y` for a Galois covering), then `N ≅ q^* M` for a module object `M` on `X`, and
`ψ` corresponds to the canonical descent datum `q^* M ≅ (ρ σ)^* q^* M` of `q^* M`. -/
theorem exists_upperStar_obj_iso_of_galoisDescentDatum [Surjective q] [QuasiCompact q]
    [Finite Γ] (hρ₁ : ρ 1 = 𝟙 Y) (hρmul : ∀ σ τ, ρ (σ * τ) = ρ σ ≫ ρ τ)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    [IsIso (galoisComparison Λ q ρ hρ N)]
    [IsIso (galoisComparison Λ q ρ hρ ((q)^*⟦Λ⟧.obj ((q)_*⟦Λ⟧.obj N)))]
    (ψ : ∀ σ, N ⟶ (ρ σ)^*⟦Λ⟧.obj N)
    (hψ₁ : ψ 1 ≫ (upperStarCongr Λ hρ₁).hom.app N ≫ (upperStarId Λ Y).hom.app N = 𝟙 N)
    (hψ : ∀ σ τ, ψ σ ≫ (ρ σ)^*⟦Λ⟧.map (ψ τ) =
      ψ (σ * τ) ≫ (upperStarCongr Λ (hρmul σ τ)).hom.app N ≫
        (upperStarComp Λ (ρ σ) (ρ τ)).hom.app N) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (e : (q)^*⟦Λ⟧.obj M ≅ N), ∀ σ, e.hom ≫ ψ σ =
        ((upperStarCongr Λ (hρ σ)).inv.app M ≫ (upperStarComp Λ (ρ σ) q).hom.app M) ≫
          (ρ σ)^*⟦Λ⟧.map e.hom := by
  have := Fintype.ofFinite Γ
  classical
  obtain ⟨M, e, he⟩ := (upperStarLowerStarAdjunction Λ q).exists_iso_of_isGaloisDescentDatum
    (S := fun σ ↦ (ρ σ)^*⟦Λ⟧)
    (κ := fun σ ↦ (upperStarComp Λ (ρ σ) q).symm ≪≫ upperStarCongr Λ (hρ σ))
    (ε₀ := upperStarCongr Λ hρ₁ ≪≫ upperStarId Λ Y)
    (μ := fun σ τ ↦ upperStarCongr Λ (hρmul σ τ) ≪≫ upperStarComp Λ (ρ σ) (ρ τ))
    (fun M ↦ by
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
      exact upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_id Λ q (hρ 1) hρ₁ M)
    (fun σ τ M ↦ by
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
      exact upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_comp Λ q (hρ σ) (hρ τ)
        (hρ (σ * τ)) (hρmul σ τ) M)
    N ⟨by simpa only [Iso.trans_hom, NatTrans.comp_app] using hψ₁,
      fun σ τ ↦ by simpa only [Iso.trans_hom, NatTrans.comp_app] using hψ σ τ⟩
  exact ⟨M, e, fun σ ↦ by simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app] using he σ⟩

end AlgebraicGeometry.ProEtale.CondensedRing
