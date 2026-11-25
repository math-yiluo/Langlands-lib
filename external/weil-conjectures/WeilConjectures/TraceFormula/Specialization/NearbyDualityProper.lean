/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyDuality

/-!

# Nearby duality: global sections and finite support

In Illusie's proof of Gabber's theorem (*Autour du théorème de monodromie locale*, Thm. 4.2;
blueprint `proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction"), the cone `C`
of the duality map `δ_{M,K}` of a proper model has no global sections (global duality and proper
exchange, blueprint `lemma-nearby-duality-proper-direct-image` (3)) and is supported on finitely
many closed points (generic slicing, blueprint `lemma-nearby-duality-slice--1`); hence it vanishes.
This file proves the last, formal step:

* a morphism `f` of bounded constructible complexes on a separated scheme of finite type over a
  separably closed field is an isomorphism as soon as `RΓ(f)` and the restriction of `f` to the
  complement of finitely many closed points are
  (`ProEtale.CondensedRing.isIso_of_isIso_upperStar_finsetComplOpens_of_isIso_lowerStar`, from
  blueprint `lemma-finite-support-global-sections--1`,
  `ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`);
* hence the duality map `δ_{M,K}` is an isomorphism as soon as `RΓ(X', δ_{M,K})` and its
  restriction away from finitely many closed points of the special fibre are
  (`NearbyCyclesModel.isIso_nearbyDualityMap_of_isIso_lowerStar`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

section Detect

variable {k : Type u} [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Global sections and restriction away from finitely many closed points detect
isomorphisms**: let `X` be a separated scheme of finite type over a separably closed field and
`S` a finite set of closed points of `X`. A morphism `f` of bounded constructible complexes on `X`
whose restriction to `X ∖ S` and whose global sections `RΓ(X, f)` are isomorphisms is an
isomorphism: its cone vanishes by
`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`
(blueprint `lemma-finite-support-global-sections--1`). -/
theorem isIso_of_isIso_upperStar_finsetComplOpens_of_isIso_lowerStar (S : Finset X.left)
    (hS : ∀ x ∈ S, IsClosed {x}) {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B)
    (hU : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (finsetComplOpens S hS))).map f))
    (hΓ : IsIso ((boundedConstructibleLowerStar ℓ
      (toPoint X)).map f)) : IsIso f := by
  have hU' : IsIso (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map f.hom) :=
    (boundedConstructible _).ι.map_isIso ((boundedConstructibleUpperStar _ ℓ
      (opensOverι (finsetComplOpens S hS))).map f)
  have hΓ' : IsIso (R((X.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map f.hom) := by
    have h := (boundedConstructible _).ι.map_isIso
      ((boundedConstructibleLowerStar ℓ (toPoint X)).map f)
    change IsIso (R(((toPoint X).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map f.hom) at h
    rwa [toPoint_left] at h
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle f.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have hC := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    X.left)).ext_of_isTriangulatedClosed₃ _ hT A.property B.property
  have h₁ := Triangle.isZero₃_of_isIso₁ _
    (R((X.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT) hΓ'
  have h₂ := Triangle.isZero₃_of_isIso₁ _
    (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT) hU'
  have : IsIso ((boundedConstructible _).ι.map f) :=
    (Triangle.isZero₃_iff_isIso₁ _ hT).1
      (isZero_of_isZero_upperStar_finsetComplOpens ℓ S hS C hC h₂ h₁)
  exact isIso_of_reflects_iso f (boundedConstructible _).ι

end Detect

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The cone of the duality map vanishes if it has no global sections and finite support**
(blueprint `proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction", last step):
the duality map `δ_{M,K}` is an isomorphism as soon as its global sections `RΓ(X', δ_{M,K})` and its
restriction to the complement of a finite set of closed points of the special fibre are. -/
theorem isIso_nearbyDualityMap_of_isIso_lowerStar (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x})
    (hU : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι (finsetComplOpens S hS))).map (nearbyDualityMap ℓ D h K)))
    (hΓ : IsIso ((boundedConstructibleLowerStar ℓ
      (toPoint X')).map (nearbyDualityMap ℓ D h K))) :
    IsIso (nearbyDualityMap ℓ D h K) :=
  isIso_of_isIso_upperStar_finsetComplOpens_of_isIso_lowerStar ℓ S hS _ hU hΓ

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
