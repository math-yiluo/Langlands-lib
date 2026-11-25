/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.Dualizing

/-!

# Cohomological correspondences and the Lefschetz–Verdier trace formula

Let `X` be a separated `k`-scheme of finite type and `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. A *cohomological
endocorrespondence* of `(X, K)` (blueprint `definition-correspondence`) consists of a scheme `C`
with two morphisms `c₁, c₂ : C ⟶ X` and a coefficient map
```
u : Lc₂^* K ⟶ Rc₁^! K
```
(`ProEtale.CondensedRing.Correspondence`). For `c₂` proper it acts on compactly supported
cohomology by the *global operator* (blueprint `definition-action-correspondence--1`)
```
T_c(u) : RΓ_c(X, K) ⟶ RΓ_c(X, Rc₂_* Lc₂^* K) ≅ RΓ_c(C, Lc₂^* K) --u--> RΓ_c(C, Rc₁^! K)
           ≅ RΓ_c(X, Rc₁_! Rc₁^! K) ⟶ RΓ_c(X, K),
```
the unit of `Lc₂^* ⊣ Rc₂_*`, the identification `Rc₂_* ≅ Rc₂_!`, the composition of the lower
shriek and the counit of `Rc₁_! ⊣ Rc₁^!`
(`ProEtale.CondensedRing.Correspondence.globalOperator`).

The *graph correspondence* of a Weil object `(K, φ)` for `Φ` in degree `m` is
`c_m = (𝟙, Φ_m)` with coefficient map `φ_m : LΦ_m^* K ≅ K ≅ R(𝟙)^! K`
(`ProEtale.CondensedRing.WeilBoundedConstructible.graph`, blueprint
`definition-frobenius-correspondences-their-operators`).
Its global operator is the global Frobenius `F_{c,m}` obtained from the compactly supported
cohomology of Weil objects
(`ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator_eq_correspondenceGlobalOperator`,
blueprint `lemma-scheme-frobenius-geometric-frobenius--3`).

## The Lefschetz–Verdier formula

The *fixed locus* `Fix(c)` of an endocorrespondence is the equalizer of `c₁` and `c₂`
(`ProEtale.CondensedRing.Correspondence.FixedLocus`). The *trace class* of `u` is a Borel–Moore
section `Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)` (`ProEtale.CondensedRing.Correspondence.traceClass`,
blueprint `definition-trace-class-local-terms--1`): the supported pairing of `u` against the
diagonal correspondence `(X, Δ, 1_K)`, through the Künneth–Verdier isomorphism
`RHom(p₂^* K, p₁^! K) ≅ K ⊠ D_X K` and the evaluation `K ⊗ D_X K ⟶ ω_X`. Then:

* for `X` proper and `c₂` proper, `tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)`
  (`ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_integral_traceClass`, blueprint
  `theorem-proper-pushforward-lefschetz-verdier--2`), the Lefschetz–Verdier formula; by
  `BorelMooreSection.integral_eq_sum_localTerm` the right hand side splits into local terms
  along the open and closed pieces of `Fix(c)`
  (blueprint `theorem-proper-pushforward-lefschetz-verdier`);
* over the base point the trace class of an endomorphism `v` integrates to its trace,
  `∫_s Tr(v) = tr(v)` (`ProEtale.CondensedRing.Correspondence.integral_traceClass_ofEnd`,
  blueprint `lemma-local-terms-point--1`);
* on a smooth curve the local term of the Frobenius correspondence at a fixed point is the trace
  of the local Frobenius on the geometric stalk
  (`ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`,
  blueprint `proposition-frobenius-local-term-curve--1`). The dualizing complex of the curve enters
  through smooth purity `ω_C ≅ ℚ̄_ℓ,C(1)[2]` (`dualizingComplexSmoothIso`), and that of the reduced
  point components of the fixed locus through the canonical purity for open immersions
  (`BorelMooreSection.restrict`).

The trace class and the theorems about it are in `WeilConjectures.TraceFormula.TraceClass`.

## Main definitions

- `ProEtale.CondensedRing.Correspondence`: an endocorrespondence of `(X, K)`.
- `ProEtale.CondensedRing.Correspondence.globalOperator`: its global operator `T_c(u)`.
- `ProEtale.CondensedRing.Correspondence.ofEnd`: the diagonal correspondence of an endomorphism.
- `ProEtale.CondensedRing.WeilBoundedConstructible.graph`: the Frobenius graph correspondence.
- `ProEtale.CondensedRing.Correspondence.FixedLocus`: the fixed locus, an equalizer of `c₁, c₂`.
- `ProEtale.CondensedRing.Correspondence.ofGraph`: the graph correspondence `(𝟙 X, h)` of a map
  `v : Lh^* K ⟶ K`.
- `ProEtale.CondensedRing.Correspondence.frobeniusGraph`: the graph map in degree `m` of a
  Frobenius coefficient morphism `ψ : LΦ^* K ⟶ K`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.globalOperator_naturality`,
  `ProEtale.CondensedRing.Correspondence.globalOperator_add`: naturality of `T_c(u)` in `(u, K)`
  and linearity in `u` (blueprint `lem-trf-global-operator-naturality`).
- `ProEtale.CondensedRing.Correspondence.nonempty_hasRightDual_globalOperator`: the complexes of
  the definition of `T_c(u)` are perfect (blueprint `lemma-perfect-complexes-geometric-point--4`).
- `ProEtale.CondensedRing.Correspondence.globalOperator_ofGraph` and its naturality and
  composition laws (blueprint `definition-frobenius-correspondences-their-operators--5`).
- `ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator_eq_correspondenceGlobalOperator`
  (blueprint `lemma-scheme-frobenius-geometric-frobenius--3`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}

section

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### Correspondences -/

/-- A *cohomological endocorrespondence* of `(X, K)` (blueprint `definition-correspondence`): a
separated `k`-scheme of finite type `C` with morphisms `c₁, c₂ : C ⟶ X`, the support map
`c = (c₁, c₂) : C ⟶ X × X`, and a coefficient map `u : Lc₂^* K ⟶ Rc₁^! K`. The leg `c₂` is the
ordinary pullback leg. -/
structure Correspondence (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) where
  /-- the support `C` of the correspondence. -/
  C : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType C.hom]
  [quasiCompact : QuasiCompact C.hom]
  [isSeparated : IsSeparated C.hom]
  /-- the exceptional leg `c₁ : C ⟶ X`. -/
  c₁ : C ⟶ X
  /-- the ordinary leg `c₂ : C ⟶ X`. -/
  c₂ : C ⟶ X
  /-- the coefficient map `u : Lc₂^* K ⟶ Rc₁^! K`. -/
  u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
    (boundedConstructibleUpperShriek ℓ c₁).obj K

namespace Correspondence

attribute [instance] locallyOfFiniteType quasiCompact isSeparated

variable {ℓ} {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The *global operator* `T_c(u)` of an endocorrespondence with proper ordinary leg `c₂` on
compactly supported cohomology `RΓ_c(X, K) = Ra_{X!} K` (blueprint
`definition-action-correspondence--1`, `definition-action-correspondence--1`):
```
Ra_{X!} K ⟶ Ra_{X!} Rc₂_* Lc₂^* K ≅ Ra_{X!} Rc₂_! Lc₂^* K ≅ Ra_{C!} Lc₂^* K
  --Ra_{C!} u--> Ra_{C!} Rc₁^! K ≅ Ra_{X!} Rc₁_! Rc₁^! K ⟶ Ra_{X!} K.
```
-/
noncomputable def globalOperator [IsProper c.c₂.left] :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K :=
  (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        c.c₂).unit.app K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
        c.c₂).inv.app _) ≫
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.c₂
      (toPoint X)).inv.app _ ≫
    eqToHom (by rw [comp_toPoint]) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint c.C)).map c.u ≫
    eqToHom (by rw [comp_toPoint]) ≫
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.c₁
      (toPoint X)).hom.app _ ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ
        c.c₁).counit.app K)

/-- The global operator `T_c(u)` in terms of the composition isomorphisms
`Rc_i_! ⋙ Ra_{X!} ≅ Ra_{C!}` (`ProEtale.CondensedRing.boundedConstructibleLowerShriekCompToPoint`):
```
Ra_{X!} K ⟶ Ra_{X!} Rc₂_* Lc₂^* K ≅ Ra_{X!} Rc₂_! Lc₂^* K ≅ Ra_{C!} Lc₂^* K
  --Ra_{C!} u--> Ra_{C!} Rc₁^! K ≅ Ra_{X!} Rc₁_! Rc₁^! K ⟶ Ra_{X!} K.
```
-/
lemma globalOperator_eq [IsProper c.c₂.left] :
    c.globalOperator =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            c.c₂).unit.app K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c.c₂).inv.app _) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ c.c₂).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint c.C)).map
          c.u ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ c.c₁).inv.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ
            c.c₁).counit.app K) := by
  rw [globalOperator, boundedConstructibleLowerShriekCompToPoint_hom_app,
    boundedConstructibleLowerShriekCompToPoint_inv_app]
  simp only [Category.assoc]

variable (K) in
/-- The global operator of the correspondence with support `C`, legs `c₁, c₂` and coefficient
map `u`, as an explicit composite of its fields (see `globalOperator_eq_globalOperatorMk`). -/
noncomputable def globalOperatorMk (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (c₁ c₂ : C ⟶ X) [IsProper c₂.left]
    (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj K) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K :=
  (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        c₂).unit.app K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c₂).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K)) ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ c₂).hom.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint C)).map u ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ c₁).inv.app
      ((boundedConstructibleUpperShriek ℓ c₁).obj K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ
        c₁).counit.app K)

lemma globalOperator_eq_globalOperatorMk [IsProper c.c₂.left] :
    c.globalOperator = globalOperatorMk K c.C c.c₁ c.c₂ c.u := by
  rw [globalOperator_eq, globalOperatorMk]

/-- `globalOperator_eq_globalOperatorMk` for a correspondence given by its fields. -/
lemma globalOperator_mk (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (c₁ c₂ : C ⟶ X) [IsProper c₂.left]
    (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj K) :
    (⟨C, c₁, c₂, u⟩ : Correspondence ℓ K).globalOperator = globalOperatorMk K C c₁ c₂ u :=
  globalOperator_eq_globalOperatorMk _

/-- The naturality and linearity of the global operator, for an abstract family of functors. -/
lemma globalOperator_naturality_aux {DX DC S : Type*} [Category DX] [Category DC] [Category S]
    {L₂ : DX ⥤ DC} {R₂ S₂ S₁ : DC ⥤ DX} {U₁ : DX ⥤ DC} {AX : DX ⥤ S} {AC : DC ⥤ S}
    (adj₂ : L₂ ⊣ R₂) (adj₁ : S₁ ⊣ U₁) (i₂ : S₂ ≅ R₂) (c₂ : S₂ ⋙ AX ≅ AC) (c₁ : S₁ ⋙ AX ≅ AC)
    {K K' : DX} (a : K ⟶ K') (u : L₂.obj K ⟶ U₁.obj K) (u' : L₂.obj K' ⟶ U₁.obj K')
    (hu : u ≫ U₁.map a = L₂.map a ≫ u') :
    (AX.map (adj₂.unit.app K) ≫ AX.map (i₂.inv.app _) ≫ c₂.hom.app _ ≫ AC.map u ≫
        c₁.inv.app _ ≫ AX.map (adj₁.counit.app K)) ≫ AX.map a =
      AX.map a ≫ AX.map (adj₂.unit.app K') ≫ AX.map (i₂.inv.app _) ≫ c₂.hom.app _ ≫
        AC.map u' ≫ c₁.inv.app _ ≫ AX.map (adj₁.counit.app K') := by
  have e₁ : AX.map (adj₁.counit.app K) ≫ AX.map a =
      AX.map (S₁.map (U₁.map a)) ≫ AX.map (adj₁.counit.app K') := by
    rw [← AX.map_comp, ← AX.map_comp]
    exact congrArg AX.map (adj₁.counit.naturality a).symm
  have e₂ : c₁.inv.app _ ≫ AX.map (S₁.map (U₁.map a)) = AC.map (U₁.map a) ≫ c₁.inv.app _ :=
    (c₁.inv.naturality _).symm
  have e₃ : AC.map u ≫ AC.map (U₁.map a) = AC.map (L₂.map a) ≫ AC.map u' := by
    rw [← AC.map_comp, hu, AC.map_comp]
  have e₄ : c₂.hom.app _ ≫ AC.map (L₂.map a) = AX.map (S₂.map (L₂.map a)) ≫ c₂.hom.app _ :=
    (c₂.hom.naturality _).symm
  have e₅ : AX.map (i₂.inv.app _) ≫ AX.map (S₂.map (L₂.map a)) =
      AX.map (R₂.map (L₂.map a)) ≫ AX.map (i₂.inv.app _) := by
    rw [← AX.map_comp, ← AX.map_comp]
    exact congrArg AX.map (i₂.inv.naturality _).symm
  have e₆ : AX.map (adj₂.unit.app K) ≫ AX.map (R₂.map (L₂.map a)) =
      AX.map a ≫ AX.map (adj₂.unit.app K') := by
    rw [← AX.map_comp, ← AX.map_comp]
    exact congrArg AX.map (adj₂.unit.naturality a).symm
  simp only [Category.assoc]
  rw [e₁, reassoc_of% e₂, reassoc_of% e₃, reassoc_of% e₄, reassoc_of% e₅, reassoc_of% e₆]

/-- **Naturality of the global operator** (blueprint `lem-trf-global-operator-naturality`): for
correspondences `u : Lc₂^* K ⟶ Rc₁^! K` and `u' : Lc₂^* K' ⟶ Rc₁^! K'` on the same support and a
morphism `a : K ⟶ K'` compatible with them, `Rc₁^! a ∘ u = u' ∘ Lc₂^* a`, the square
```
RΓ_c(X, K) --T_c(u)--> RΓ_c(X, K)
    │RΓ_c(a)               │RΓ_c(a)
    ▼                      ▼
RΓ_c(X, K') --T_c(u')--> RΓ_c(X, K')
```
commutes (see also blueprint `rem-ptr-trf-global-operator-7`). -/
theorem globalOperator_naturality {K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : K ⟶ K')
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] (c₁ c₂ : C ⟶ X) [IsProper c₂.left]
    (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj K)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj K')
    (hu : u ≫ (boundedConstructibleUpperShriek ℓ c₁).map a =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).map a ≫ u') :
    (⟨C, c₁, c₂, u⟩ : Correspondence ℓ K).globalOperator ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map a =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map a ≫
        (⟨C, c₁, c₂, u'⟩ : Correspondence ℓ K').globalOperator := by
  rw [globalOperator_mk, globalOperator_mk, globalOperatorMk, globalOperatorMk]
  have h := globalOperator_naturality_aux
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ c₂)
    (boundedConstructibleUpperShriekAdjunction ℓ c₁)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c₂)
    (boundedConstructibleLowerShriekCompToPoint ℓ c₂)
    (boundedConstructibleLowerShriekCompToPoint ℓ c₁) a u u' hu
  simp only [Category.assoc] at h ⊢
  rw [h]

/-- **Linearity of the global operator in the correspondence** (blueprint
`rem-ptr-trf-global-operator-7`): `T_c(u + u') = T_c(u) + T_c(u')`. -/
theorem globalOperator_add (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (c₁ c₂ : C ⟶ X) [IsProper c₂.left]
    (u u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj K) :
    (⟨C, c₁, c₂, u + u'⟩ : Correspondence ℓ K).globalOperator =
      (⟨C, c₁, c₂, u⟩ : Correspondence ℓ K).globalOperator +
        (⟨C, c₁, c₂, u'⟩ : Correspondence ℓ K).globalOperator := by
  simp only [globalOperator_mk, globalOperatorMk, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- **The global operator is an endomorphism of a perfect complex** (blueprint
`lemma-perfect-complexes-geometric-point--4`, see also
`lemma-perfect-complexes-geometric-point--4`): for `k` separably closed, the source and target
`RΓ_c(X, K)` of `T_c(u)` and all the intermediate complexes `RΓ_c(X, Rc₂_* Lc₂^* K)`,
`RΓ_c(C, Lc₂^* K)`, `RΓ_c(C, Rc₁^! K)` and `RΓ_c(X, Rc₁_! Rc₁^! K)` of its definition are dualizable
objects of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`, by the perfectness of compactly supported cohomology
(`ProEtale.CondensedRing.WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology`). -/
theorem nonempty_hasRightDual_globalOperator [IsSepClosed k] :
    Nonempty (HasRightDual
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)) ∧
      Nonempty (HasRightDual
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
          ((boundedConstructibleLowerStar ℓ c.c₂).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K)))) ∧
      Nonempty (HasRightDual
        ((boundedConstructibleLowerShriek ℓ (toPoint c.C)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K))) ∧
      Nonempty (HasRightDual
        ((boundedConstructibleLowerShriek ℓ (toPoint c.C)).obj
          ((boundedConstructibleUpperShriek ℓ c.c₁).obj K))) ∧
      Nonempty (HasRightDual
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
          ((boundedConstructibleLowerShriek ℓ c.c₁).obj
            ((boundedConstructibleUpperShriek ℓ c.c₁).obj K)))) :=
  ⟨WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology _,
    WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology _,
    WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology _,
    WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology _,
    WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology _⟩

/-! ### Graph correspondences -/

/-- The counit of `R(𝟙 X)_! ⊣ R(𝟙 X)^!` is the identity, up to the identity isomorphisms. -/
lemma boundedConstructibleUpperShriekAdjunction_id_counit_app
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X)).counit.app
        M =
      (boundedConstructibleLowerShriekId ℓ X).hom.app
          ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj M) ≫
        (boundedConstructibleUpperShriekId ℓ X).hom.app M := by
  have h := conjugateEquiv_counit
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ X).inv M
  rw [boundedConstructibleUpperShriekId, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    ← cancel_epi ((boundedConstructibleLowerShriekId ℓ X).inv.app
      ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj M)),
    Iso.inv_hom_id_app_assoc]
  exact h.symm.trans (Category.comp_id _)

/-- The global operator of a correspondence whose exceptional leg is the identity,
`c = (𝟙 X, h)`: it is `RΓ_c(X, u) ∘ h^♯` after `R(𝟙 X)^! ≅ 𝟭`. -/
theorem globalOperator_mk_id (h : X ⟶ X) [IsProper h.left]
    (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶
      (boundedConstructibleUpperShriek ℓ (𝟙 X)).obj K) :
    (⟨X, 𝟙 X, h, u⟩ : Correspondence ℓ K).globalOperator =
      (compactPullback ℓ h).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (u ≫ (boundedConstructibleUpperShriekId ℓ X).hom.app K) := by
  have hl := boundedConstructibleLowerShriekComp_padicAlgCl_id_left ℓ (toPoint X)
    ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj K)
  simp only [Functor.map_comp] at hl
  rw [globalOperator_mk, globalOperatorMk, boundedConstructibleUpperShriekAdjunction_id_counit_app,
    compactPullback_app, boundedConstructibleLowerShriekCompToPoint_inv_app]
  simp only [boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hl, eqToHom_trans_assoc]
  simp only [eqToHom_refl, Category.id_comp]

variable (K) in
/-- The *graph correspondence* `(X, 𝟙 X, h, v)` of an endomorphism `h : X ⟶ X` and a map
`v : Lh^* K ⟶ K`, with coefficient map `Lh^* K --v--> K ≅ R(𝟙 X)^! K` (blueprint
`definition-frobenius-correspondences-their-operators--5`). -/
noncomputable def ofGraph (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K) :
    Correspondence ℓ K where
  C := X
  c₁ := 𝟙 X
  c₂ := h
  u := v ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app K

instance (h : X ⟶ X) [IsProper h.left]
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K) :
    IsProper (ofGraph K h v).c₂.left :=
  inferInstanceAs (IsProper h.left)

/-- **The global operator of a graph correspondence** (blueprint
`definition-frobenius-correspondences-their-operators--5`): for a proper `h`, `T_{(𝟙, h)}(v)` is the
composite
```
RΓ_c(X, K) --h^♯--> RΓ_c(X, Lh^* K) --RΓ_c(X, v)--> RΓ_c(X, K),
```
where `h^♯` is induced by the unit `K ⟶ Rh_* Lh^* K` and `Rh_* ≅ Rh_!`
(`ProEtale.CondensedRing.compactPullback`). -/
theorem globalOperator_ofGraph (h : X ⟶ X) [IsProper h.left]
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K) :
    (ofGraph K h v).globalOperator =
      (compactPullback ℓ h).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map v := by
  refine (globalOperator_mk_id h _).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]

/-- **Functoriality of the graph construction** (blueprint
`definition-frobenius-correspondences-their-operators--5`): a morphism `a : K ⟶ K'` compatible with
`v` and `v'`, `a ∘ v = v' ∘ Lh^* a`, intertwines the global operators. -/
theorem globalOperator_ofGraph_naturality {K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : K ⟶ K') (h : X ⟶ X) [IsProper h.left]
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (v' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K' ⟶ K')
    (hv : v ≫ a = (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map a ≫ v') :
    (ofGraph K h v).globalOperator ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map a =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map a ≫
        (ofGraph K' h v').globalOperator := by
  rw [globalOperator_ofGraph, globalOperator_ofGraph, Category.assoc, ← Functor.map_comp, hv,
    Functor.map_comp, compactPullback_naturality_assoc]

/-- **Compatibility of the graph construction with composition** (blueprint
`definition-frobenius-correspondences-their-operators--5`): for proper endomorphisms `h` and `h'`
with coefficient maps `v : Lh^* K ⟶ K` and `v' : Lh'^* K ⟶ K`, the graph correspondence of `h' ≫ h`
with the composite coefficient map `L(h' ≫ h)^* K ≅ Lh'^* Lh^* K --Lh'^* v--> Lh'^* K --v'--> K` has
global operator `T(v') ∘ T(v)`. -/
theorem globalOperator_ofGraph_comp (h h' : X ⟶ X) [IsProper h.left] [IsProper h'.left]
    [IsProper (h' ≫ h).left]
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (v' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h').obj K ⟶ K) :
    (ofGraph K (h' ≫ h)
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ h' h).hom.app K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h').map v ≫
            v')).globalOperator =
      (ofGraph K h v).globalOperator ≫ (ofGraph K h' v').globalOperator := by
  rw [globalOperator_ofGraph, globalOperator_ofGraph, globalOperator_ofGraph,
    compactPullback_comp_app]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  rw [Functor.map_comp, compactPullback_naturality_assoc]

variable (K) in
/-- The *graph map in degree `m`* of a Frobenius coefficient morphism `ψ : LΦ^* K ⟶ K`, an
arbitrary morphism (blueprint `definition-frobenius-correspondences-their-operators`): the graph
correspondence `c_m = (𝟙 X, Φ_m)` with coefficient map the iterate
`ψ_m : LΦ_m^* K ⟶ K ≅ R(𝟙 X)^! K` (`ProEtale.CondensedRing.frobeniusCoefficientIterate`). -/
noncomputable def frobeniusGraph (Φ : X ⟶ X)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (m : ℕ) : Correspondence ℓ K :=
  ofGraph K (frobeniusIterate Φ m) (frobeniusCoefficientIterate ψ m)

instance (Φ : X ⟶ X) [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (m : ℕ) : IsProper (frobeniusGraph K Φ ψ m).c₂.left :=
  inferInstanceAs (IsProper (frobeniusIterate Φ m).left)

/-- The global operator of the graph map in degree `m` of a Frobenius coefficient morphism `ψ` is
`F_{c,m}(ψ) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` (blueprint
`definition-frobenius-correspondences-their-operators`). -/
theorem globalOperator_frobeniusGraph (Φ : X ⟶ X) [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    (frobeniusGraph K Φ ψ m).globalOperator = frobeniusCompactOperator ℓ ψ m :=
  globalOperator_ofGraph _ _

variable (K) in
/-- The *diagonal correspondence* `(X, 𝟙, 𝟙, v)` of an endomorphism `v : K ⟶ K`, with
coefficient map `L(𝟙)^* K ≅ K --v--> K ≅ R(𝟙)^! K`. -/
noncomputable def ofEnd (v : K ⟶ K) : Correspondence ℓ K where
  C := X
  c₁ := 𝟙 X
  c₂ := 𝟙 X
  u := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K ≫ v ≫
    (boundedConstructibleUpperShriekId ℓ X).inv.app K

instance (v : K ⟶ K) : IsProper (ofEnd K v).c₂.left :=
  inferInstanceAs (IsProper (𝟙 X.left))

/-- The global operator of the diagonal correspondence of `v` is `RΓ_c(X, v)`. -/
theorem globalOperator_ofEnd (v : K ⟶ K) :
    (ofEnd K v).globalOperator =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map v := by
  have : IsProper (𝟙 X : X ⟶ X).left := inferInstanceAs (IsProper (𝟙 X.left))
  refine (globalOperator_mk_id (𝟙 X) _).trans ?_
  rw [compactPullback_id_app, ← Functor.map_comp]
  congr 1
  simp

/-! ### The fixed locus and the trace class -/

/-- The *fixed locus* `Fix(c) = C ×_{X × X} X` of an endocorrespondence: an equalizer
`ι : Fix(c) ⟶ C` of the two legs `c₁` and `c₂` in `Over (Spec (.of k))` (blueprint
`definition-correspondence`). -/
structure FixedLocus where
  /-- the fixed scheme `Fix(c)`. -/
  F : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType F.hom]
  [quasiCompact : QuasiCompact F.hom]
  [isSeparated : IsSeparated F.hom]
  /-- the inclusion `ι : Fix(c) ⟶ C`. -/
  ι : F ⟶ c.C
  w : ι ≫ c.c₁ = ι ≫ c.c₂
  /-- `ι` is an equalizer of `c₁` and `c₂`. -/
  isLimit : IsLimit (Fork.ofι ι w)

attribute [instance] FixedLocus.locallyOfFiniteType FixedLocus.quasiCompact
  FixedLocus.isSeparated

/-- The fixed locus of a diagonal correspondence is the whole scheme. -/
noncomputable def fixedLocusOfEnd (v : K ⟶ K) : (ofEnd K v).FixedLocus where
  F := X
  ι := 𝟙 X
  w := rfl
  isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι) (fun _ ↦ Category.comp_id _)
    (fun _ _ hm ↦ by simpa using hm)

end Correspondence

end

/-! ### The Frobenius graph correspondence -/

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

variable {ℓ} {Φ : X ⟶ X}

/-- The *graph correspondence* `c_m = (𝟙, Φ_m)` of a Weil object `(K, φ)` in degree `m`, with
coefficient map `LΦ_m^* K --φ_m--> K ≅ R(𝟙 X)^! K` (blueprint
`definition-frobenius-correspondences-their-operators`). -/
noncomputable def graph (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    Correspondence ℓ K.carrier where
  C := X
  c₁ := 𝟙 X
  c₂ := frobeniusIterate Φ m
  u := (K.iterateStr m).hom ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app K.carrier

instance (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) [IsFinite (frobeniusIterate Φ m).left] :
    IsProper (K.graph m).c₂.left :=
  inferInstanceAs (IsProper (frobeniusIterate Φ m).left)

/-- **The global operator of the graph correspondence** (blueprint
`lemma-scheme-frobenius-geometric-frobenius--3`): the global Frobenius `F_{c,m}` defined through the
compactly supported cohomology of Weil objects is the global operator `T_{c_m}(φ_m)` of the
graph correspondence `c_m = (𝟙, Φ_m)`. -/
theorem globalOperator_eq_correspondenceGlobalOperator (K : WeilBoundedConstructible ℓ Φ)
    (m : ℕ) [IsFinite (frobeniusIterate Φ m).left]
    [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    K.globalOperator m = (K.graph m).globalOperator :=
  (WeilBoundedConstructible.globalOperator_eq K m).trans
    (Correspondence.globalOperator_ofGraph _ _).symm

/-- The graph correspondence of a Weil object is the graph map of its structure isomorphism as a
Frobenius coefficient morphism (blueprint
`definition-frobenius-correspondences-their-operators`). -/
lemma graph_eq_frobeniusGraph (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    K.graph m = Correspondence.frobeniusGraph K.carrier Φ K.str.hom m := by
  rw [graph, Correspondence.frobeniusGraph, Correspondence.ofGraph,
    iterateStr_hom_eq_frobeniusCoefficientIterate]

/-- A rational point `x` fixed by `Φ_m` lies on the fixed locus of the graph correspondence
`c_m`: the factorization of `x` through the equalizer `Fix(c_m) ⟶ X` of `𝟙` and `Φ_m`. -/
noncomputable def fixedLocusPoint (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (F : (K.graph m).FixedLocus) (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    RationalPoint F.F :=
  F.isLimit.lift (Fork.ofι (P := point k) x (by
    change x ≫ 𝟙 X = x ≫ frobeniusIterate Φ m
    rw [Category.comp_id, hx]))

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
