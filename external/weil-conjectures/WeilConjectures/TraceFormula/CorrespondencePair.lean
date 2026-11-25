/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Product

/-!

# Correspondences between pairs and supported classes

Let `X, Y` be separated `k`-schemes of finite type with `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and
`L ∈ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`. A *correspondence from `(X, K)` to `(Y, L)`* (blueprint
`definition-correspondence`) is a scheme `C` with an exceptional leg
`c₁ : C ⟶ Y`, an ordinary leg `c₂ : C ⟶ X` and a coefficient map `u : Lc₂^* K ⟶ Rc₁^! L`
(`ProEtale.CondensedRing.CorrespondenceBetween`). Its support map is
`c = (c₁, c₂) : C ⟶ Z = Y ⨯ X`. An *opposite correspondence* is a correspondence `d` from
`(Y, L)` to `(X, K)`; its support is turned into a map `d̄ = τ d = (d₂, d₁) : D ⟶ Z` by the
exchange of factors `τ : X ⨯ Y ≅ Y ⨯ X`, and the *intersection* of `c` and `d` is a specified
fibre product `E(C, D) = C ×_{Z, c, d̄} D`
(`ProEtale.CondensedRing.CorrespondenceBetween.Intersection`).

For an endocorrespondence `c` of `(X, K)` and the identity correspondence `Δ_X` of `(X, K)`,
`d̄ = Δ_X` and the intersection `E(C, X)` is the fixed locus `Fix(c)`
(`ProEtale.CondensedRing.Correspondence.FixedLocus.toIntersection` and
`ProEtale.CondensedRing.CorrespondenceBetween.Intersection.toFixedLocus`).

A *class supported on `i : T ⟶ Z`* with values in `P ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧` is a morphism
`Ri_! ℚ̄_ℓ,T ⟶ P` (`ProEtale.CondensedRing.SupportedClass`, blueprint `def-trf-supported-class`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Supported classes -/

/-- The group `H⁰_T(Z, P) = Hom(Ri_! ℚ̄_ℓ,T, P)` of *classes supported on `i : T ⟶ Z`* with values
in `P` (blueprint `def-trf-supported-class`). The map `i` is part of the data: it need not be an
immersion. -/
abbrev SupportedClass {T Z : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (i : T ⟶ Z) (P : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : Type _ :=
  (boundedConstructibleLowerShriek ℓ i).obj (𝟙_ _) ⟶ P

/-! ### Correspondences between pairs -/

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- A *correspondence from `(X, K)` to `(Y, L)`* (blueprint
`definition-correspondence`): a separated `k`-scheme of finite type `C`
with an exceptional leg `c₁ : C ⟶ Y`, an ordinary leg `c₂ : C ⟶ X` (so that the support is
`c = (c₁, c₂) : C ⟶ Y ⨯ X`) and a coefficient map `u : Lc₂^* K ⟶ Rc₁^! L`. An *opposite
correspondence* is a correspondence from `(Y, L)` to `(X, K)`, i.e. a term of
`CorrespondenceBetween ℓ L K`. -/
structure CorrespondenceBetween (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) where
  /-- the support `C` of the correspondence. -/
  C : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType C.hom]
  [quasiCompact : QuasiCompact C.hom]
  [isSeparated : IsSeparated C.hom]
  /-- the exceptional leg `c₁ : C ⟶ Y`. -/
  c₁ : C ⟶ Y
  /-- the ordinary leg `c₂ : C ⟶ X`. -/
  c₂ : C ⟶ X
  /-- the coefficient map `u : Lc₂^* K ⟶ Rc₁^! L`. -/
  u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
    (boundedConstructibleUpperShriek ℓ c₁).obj L

namespace CorrespondenceBetween

attribute [instance] locallyOfFiniteType quasiCompact isSeparated

variable {ℓ} {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- The *support map* `c = (c₁, c₂) : C ⟶ Z = Y ⨯ X` of a correspondence from `(X, K)` to
`(Y, L)` (blueprint `definition-correspondence`): `c₁ = c ≫ p₁` and `c₂ = c ≫ p₂`. -/
noncomputable def support (c : CorrespondenceBetween ℓ K L) : c.C ⟶ Y ⨯ X :=
  prod.lift c.c₁ c.c₂

@[reassoc (attr := simp)]
lemma support_fst (c : CorrespondenceBetween ℓ K L) : c.support ≫ prod.fst = c.c₁ :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
lemma support_snd (c : CorrespondenceBetween ℓ K L) : c.support ≫ prod.snd = c.c₂ :=
  prod.lift_snd _ _

/-- The support `d̄ = τ d = (d₂, d₁) : D ⟶ Z = Y ⨯ X` of an opposite correspondence `d` from
`(Y, L)` to `(X, K)`, with `τ : X ⨯ Y ≅ Y ⨯ X` the exchange of factors (blueprint
`definition-correspondence`). -/
noncomputable def oppositeSupport (d : CorrespondenceBetween ℓ L K) : d.C ⟶ Y ⨯ X :=
  d.support ≫ (prod.braiding X Y).hom

lemma oppositeSupport_eq (d : CorrespondenceBetween ℓ L K) :
    d.oppositeSupport = prod.lift d.c₂ d.c₁ := by
  apply prod.hom_ext <;> simp [oppositeSupport]

@[reassoc (attr := simp)]
lemma oppositeSupport_fst (d : CorrespondenceBetween ℓ L K) :
    d.oppositeSupport ≫ prod.fst = d.c₂ := by
  rw [oppositeSupport_eq, prod.lift_fst]

@[reassoc (attr := simp)]
lemma oppositeSupport_snd (d : CorrespondenceBetween ℓ L K) :
    d.oppositeSupport ≫ prod.snd = d.c₁ := by
  rw [oppositeSupport_eq, prod.lift_snd]

/-- The *intersection* `E(C, D) = C ×_{Z, c, d̄} D` of a correspondence `c` from `(X, K)` to
`(Y, L)` and an opposite correspondence `d` (blueprint `definition-correspondence`):
a specified separated `k`-scheme of finite type with specified projections forming a cartesian
square over the supports `c, d̄ : C, D ⟶ Z`. -/
structure Intersection (c : CorrespondenceBetween ℓ K L) (d : CorrespondenceBetween ℓ L K) where
  /-- the intersection `E(C, D)`. -/
  E : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType E.hom]
  [quasiCompact : QuasiCompact E.hom]
  [isSeparated : IsSeparated E.hom]
  /-- the projection `E(C, D) ⟶ C`. -/
  fst : E ⟶ c.C
  /-- the projection `E(C, D) ⟶ D`. -/
  snd : E ⟶ d.C
  isPullback : IsPullback fst snd c.support d.oppositeSupport

attribute [instance] Intersection.locallyOfFiniteType Intersection.quasiCompact
  Intersection.isSeparated

/-- An endocorrespondence of `(X, K)` is a correspondence from `(X, K)` to `(X, K)` (blueprint
`definition-correspondence`). -/
@[simps]
def equivCorrespondence : CorrespondenceBetween ℓ K K ≃ Correspondence ℓ K where
  toFun c := ⟨c.C, c.c₁, c.c₂, c.u⟩
  invFun c := ⟨c.C, c.c₁, c.c₂, c.u⟩

variable (K) in
/-- The *identity correspondence* `(X, Δ_X, 1_K)` of `(X, K)`, with `d₁ = d₂ = 𝟙 X` and
coefficient map `L(𝟙)^* K ≅ K ≅ R(𝟙)^! K` (blueprint `definition-correspondence`). -/
noncomputable def id : CorrespondenceBetween ℓ K K :=
  equivCorrespondence.symm (Correspondence.ofEnd K (𝟙 K))

lemma id_c₁ : (id K).c₁ = 𝟙 X :=
  rfl

lemma id_c₂ : (id K).c₂ = 𝟙 X :=
  rfl

/-- The support of the identity correspondence is the diagonal: `d̄ = τ Δ_X = Δ_X`. -/
lemma id_oppositeSupport : (id K).oppositeSupport = diag X := by
  rw [oppositeSupport_eq, id_c₁, id_c₂]

/-- **The intersection with the identity correspondence is the fixed locus** (blueprint
`definition-correspondence`): an intersection `E(C, X)` of an endocorrespondence `c`
with the identity correspondence of `(X, K)` is a fixed locus of `c`, with inclusion the first
projection. -/
noncomputable def Intersection.toFixedLocus {c : CorrespondenceBetween ℓ K K}
    (E : c.Intersection (id K)) : (equivCorrespondence c).FixedLocus where
  F := E.E
  ι := E.fst
  w := by
    have h₁ := E.isPullback.w =≫ prod.fst
    have h₂ := E.isPullback.w =≫ prod.snd
    simp only [Category.assoc, support_fst, support_snd, oppositeSupport_fst,
      oppositeSupport_snd] at h₁ h₂
    exact h₁.trans h₂.symm
  isLimit := Fork.IsLimit.mk' _ fun s ↦ by
    have hs : s.ι ≫ c.support = (s.ι ≫ c.c₁) ≫ (id K).oppositeSupport := by
      apply prod.hom_ext
      · simp [id_c₂]
      · simp only [Category.assoc, support_snd, oppositeSupport_snd, id_c₁, Category.comp_id]
        exact (Fork.condition s).symm
    have h₁ := E.isPullback.w =≫ prod.fst
    simp only [Category.assoc, support_fst, oppositeSupport_fst, id_c₂] at h₁
    have h₁' : E.fst ≫ c.c₁ = E.snd := h₁.trans (Category.comp_id _)
    refine ⟨E.isPullback.lift s.ι (s.ι ≫ c.c₁) hs, E.isPullback.lift_fst _ _ _, fun {m} hm ↦ ?_⟩
    refine E.isPullback.hom_ext (hm.trans (E.isPullback.lift_fst _ _ _).symm) ?_
    refine Eq.trans ?_ (E.isPullback.lift_snd _ _ hs).symm
    calc m ≫ E.snd = (m ≫ E.fst) ≫ c.c₁ := by rw [Category.assoc, h₁']
      _ = s.ι ≫ c.c₁ := congrArg (· ≫ c.c₁) hm

end CorrespondenceBetween

namespace Correspondence.FixedLocus

variable {ℓ} {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}

/-- **The fixed locus is the intersection with the identity correspondence** (blueprint
`definition-correspondence`): `Fix(c) = C ×_{X ⨯ X, c, Δ_X} X = E(C, X)`, the
intersection of the endocorrespondence `c` with the identity correspondence of `(X, K)`, with
projections `ι : Fix(c) ⟶ C` and `d : Fix(c) ⟶ X`. -/
noncomputable def toIntersection (F : c.FixedLocus) :
    (CorrespondenceBetween.equivCorrespondence.symm c).Intersection
      (CorrespondenceBetween.id K) where
  E := F.F
  fst := F.ι
  snd := F.d
  isPullback := by
    rw [CorrespondenceBetween.id_oppositeSupport]
    exact F.isPullback

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
