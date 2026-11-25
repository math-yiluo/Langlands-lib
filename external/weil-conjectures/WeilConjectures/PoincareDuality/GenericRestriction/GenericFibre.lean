/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.GenericRestriction.FieldExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-!
# Restriction to a generic fibre over the affine line commutes with internal homs

Let `X` be a separated `k`-scheme of finite type with a morphism `b : X ⟶ 𝔸¹_k`, and let
`t : Spec L ⟶ 𝔸¹_k` be a point lying over the generic point of `𝔸¹_k`: a field extension
`k(x) ⟶ L` followed by the generic point `Spec k(x) ⟶ 𝔸¹_k`
(`AlgebraicGeometry.affineLineGenericPoint`); for instance the geometric generic point
`Spec \overline{k(x)} ⟶ 𝔸¹_k`. For the base change `g : X ×_{𝔸¹_k} Spec L ⟶ X` of `t` along `b`,
the derived pullback `Lg^*` commutes with internal homs of bounded constructible
`ℚ̄_ℓ`-complexes (`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isPullback`): this is
blueprint `lemma-restriction-geometric-generic-fibre` (2) for `B = 𝔸¹_k`
(`lemma-restriction-geometric-generic-fibre`).

## Proof

The base change `g` is the composite of the base change `X_L ⟶ X_{k(x)}` of the field extension
`k(x) ⟶ L`, along which internal homs commute with pullback
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_fieldExtension`), and of the base
change `X_{k(x)} ⟶ X` of the generic point, which is weakly étale
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_weaklyEtale`); the comparison maps are
compatible with composition
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_comp`).

## Main statements

- `ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isPullback`
- `ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_id_of_isIso`: the form on bounded
  constructible complexes, for the duality maps of `CategoryTheory.Verdier`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Restriction to a generic fibre over the affine line commutes with internal homs**
(blueprint `lemma-restriction-geometric-generic-fibre` (2), for `B = 𝔸¹_k`): let `X` be a separated
`k`-scheme of finite type with a morphism `b : X ⟶ 𝔸¹_k`, `φ : k(x) ⟶ L` a field extension and
`g : X' ⟶ X` the base change of `Spec L ⟶ Spec k(x) ⟶ 𝔸¹_k` along `b`. For bounded
constructible `ℚ̄_ℓ`-complexes `K` and `M` on `X`, the comparison
`Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)` is an isomorphism. -/
theorem isIso_ihomUpperStarComparison_of_isPullback (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (b : X.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) = X.hom)
    {L : Type u} [Field L] (φ : FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k) →+* L)
    {X' : Scheme.{u}} {g : X' ⟶ X.left} {b' : X' ⟶ Spec (.of L)}
    (sq : IsPullback g b' b (Spec.map (CommRingCat.ofHom φ) ≫ affineLineGenericPoint k))
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) M) :
    IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) g K M) := by
  let := φ.toAlgebra
  have hchar : ringChar (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k)) = ringChar k :=
    (Algebra.ringChar_eq k _).symm
  have : Fact (ringChar (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k))).Prime := by
    rw [hchar]
    infer_instance
  have : Fact (ringChar (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k)) ≠ ℓ) := by
    rw [hchar]
    infer_instance
  have : LocallyOfFiniteType (b ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hb]
    infer_instance
  have : QuasiCompact (b ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hb]
    infer_instance
  have : IsSeparated (b ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hb]
    infer_instance
  have : LocallyOfFiniteType b :=
    locallyOfFiniteType_of_comp b (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  have : QuasiCompact b :=
    QuasiCompact.of_comp b (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  have : IsSeparated b :=
    IsSeparated.of_comp b (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨g₁, rfl, sq₁⟩ : ∃ g₁ : X' ⟶ pullback b (affineLineGenericPoint k),
      g₁ ≫ pullback.fst _ _ = g ∧
        IsPullback g₁ b' (pullback.snd b (affineLineGenericPoint k))
          (Spec.map (CommRingCat.ofHom φ)) := by
    refine ⟨pullback.lift g (b' ≫ Spec.map (CommRingCat.ofHom φ)) (by simpa using sq.w),
      pullback.lift_fst _ _ _, IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback _ _)⟩
    rwa [pullback.lift_fst]
  have : LocallyOfFiniteType (Over.mk (pullback.snd b (affineLineGenericPoint k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd b (affineLineGenericPoint k)))
  have : QuasiCompact (Over.mk (pullback.snd b (affineLineGenericPoint k))).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd b (affineLineGenericPoint k)))
  have : IsSeparated (Over.mk (pullback.snd b (affineLineGenericPoint k))).hom :=
    inferInstanceAs (IsSeparated (pullback.snd b (affineLineGenericPoint k)))
  refine isIso_ihomUpperStarComparison_comp _ _ _ inferInstance ?_
  exact isIso_ihomUpperStarComparison_of_fieldExtension ℓ
    (Over.mk (pullback.snd b (affineLineGenericPoint k))) sq₁ _ _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hK)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hM)

section BoundedConstructible

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable {k₁ k₂ : Type u} [Field k₁] [Field k₂] [Fact (ringChar k₁).Prime]
  [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]

/-- The duality map `g^* RHom(A, N) ⟶ RHom(g^* A, g^* N)` of the pullback on bounded constructible
complexes, with the identity as dualizing map, is an isomorphism as soon as the comparison
`ProEtale.CondensedRing.ihomUpperStarComparison` of the ambient derived pullback is one at
`(A, N)` (`ProEtale.CondensedRing.ι_map_ihomComparison_upperStarOfMap_app`). -/
theorem isIso_nearbyDualityMap_upperStarOfMap_id_of_isIso {P : Over (Spec (.of k₁))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    {P' : Over (Spec (.of k₂))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
    [IsSeparated P'.hom] (g : P'.left ⟶ P.left)
    (N A : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) g A.obj N.obj)) :
    IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') g) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ g).obj N)) A) := by
  rw [Verdier.nearbyDualityMap_id_eq_ihomComparison]
  have : IsIso ((boundedConstructible _).ι.map ((Functor.LaxMonoidal.ihomComparison
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') g) A).app N)) := by
    rw [ι_map_ihomComparison_upperStarOfMap_app]
    exact h
  exact isIso_of_reflects_iso _ (boundedConstructible _).ι

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
