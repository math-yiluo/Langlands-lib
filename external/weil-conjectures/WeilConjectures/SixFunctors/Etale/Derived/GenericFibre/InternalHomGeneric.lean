/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# The internal-hom comparison over a geometric generic point

Let `S` be an integral scheme of finite type over a field `k` (in the application the affine
line, or a smooth curve `B`), let `Λ` be a finite ring whose exponent is invertible on `S`, and
let `t : T ⟶ S` be a morphism from a noetherian scheme lying over the generic point of `S`, for
instance a geometric generic point `η̄ = Spec k(S)^{alg} ⟶ S`. For `X` of finite type over `S`
with base change `g : X_T ⟶ X`, the internal-hom comparison
(`AlgebraicGeometry.Etale.derivedHomUpperStarComparison`)

`ρ_{K, M} : g^* RHom(K, M) ⟶ RHom(g^* K, g^* M)`

is an isomorphism for `K ∈ Dctf(X, Λ)` and `M ∈ Dᵇc(X, Λ)`
(`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_generic`). This is the third
assertion of blueprint `lemma-restriction-geometric-generic-fibre`; since `ρ` is the comparison map
of the monoidal functor `g^*`, it preserves evaluation
(`AlgebraicGeometry.Etale.derivedHomUpperStarComparison_ev`).

## Proof

By noetherian induction on the closed subsets of `X`, we may assume the statement on every
proper closed subscheme. Choose a dense open `j : V ⟶ X` on which `K` has a left dual
(`AlgebraicGeometry.Etale.exists_dense_open_exactPairing`), with closed complement `i : W ⟶ X`.
Unlike the blueprint, the dévissage is made in the second variable, along the supported
localization triangle `i_* Ri^! M ⟶ M ⟶ Rj_* j^* M ⟶`: the comparison maps in the
first two degrees of a morphism of triangles whose third term has no maps from the first one
determine the third (`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃_of_subsingleton`), so no
compatibility of `ρ` with connecting morphisms is needed
(`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_of_isIso_open_closed`).

* On the open piece `Rj_* N` both sides of `ρ` are direct images from `V_T` (the generic open
  base change
  `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic`,
  applied to `RHom(j^* K, N) ≅ D ⊗ᴸ N`), so it suffices to check it after `j_T^*`. There, by
  compatibility of `ρ` with composition, it is the comparison of `V_T ⟶ V` at the dualizable
  `j^* K`, an isomorphism
  (`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_rightDerivedLowerStar_of_generic`).
* On the closed piece `Ri_* X` both sides are direct images from `W_T` (proper base change), so it
  suffices to check it after `i_T^*`, where it is the comparison of `W_T ⟶ W` at `(i^* K, X)`,
  an isomorphism by induction since `X = Ri^! M` is bounded constructible (`AlgebraicGeometry.
  Etale.isIso_derivedHomUpperStarComparison_rightDerivedLowerStar_of_isClosedImmersion`).

The comparisons of the open and closed immersions themselves are isomorphisms on direct images
(`AlgebraicGeometry.Etale.isIso_derivedHomUpperStarComparison_rightDerivedLowerStar`), which
replaces the identity `RHom(Rs_! P, M) ≅ Rs_* RHom(P, Rs^! M)` of the blueprint proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- For an open immersion `j`, the counit of `Lj^* ⊣ Rj_*` is invertible: `Rj_*` is fully
faithful, since `j_! ⊣ j^* ⊣ Rj_*` and `j_!` is fully faithful. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion
    {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit := by
  have : IsIso (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit :=
    (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j)
      (mapDerivedUpperStarLowerStarAdjunction _ j)).isIso_unit_iff_isIso_counit.1 inferInstance
  have hff :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).fullyFaithfulROfIsIsoCounit
  have := hff.full
  have := hff.faithful
  exact (derivedUpperStarLowerStarAdjunction _ j).counit_isIso_of_R_fully_faithful

omit [Finite Λ] in
/-- For a closed immersion `i`, the counit of `Li^* ⊣ Ri_*` is invertible: `Ri_*` is fully
faithful. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion_generic
    {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit := by
  have : ((i)_*[ModuleCat.{u + 1} Λ]).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction _ i).preservesKInjectiveComplexes
  exact (derivedUpperStarLowerStarAdjunction _ i).counit_isIso_of_R_fully_faithful

/-- Blueprint `lemma-restriction-geometric-generic-fibre`, internal-hom comparison, open piece. Let
`j : V ⟶ Z` be an open immersion into a finite-type `S`-scheme, base changed along the generic
`Z_T ⟶ Z`, and suppose that `j^* K` has a left dual `D ∈ Dctf(V, Λ)`. Then the comparison
`g^* RHom(K, Rj_* N) ⟶ RHom(g^* K, g^* Rj_* N)` is an isomorphism for every bounded constructible
`N` on `V`. -/
lemma isIso_derivedHomUpperStarComparison_rightDerivedLowerStar_of_generic {k : Type u}
    [Field k]
    {S : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S)
    (ht : ∀ x, t.base x = genericPoint S) {Z Z' V V' : Scheme.{u}} (fZ : Z ⟶ S)
    [LocallyOfFiniteType fZ] [QuasiCompact fZ] {gZ : Z' ⟶ Z} {fZT : Z' ⟶ T}
    (hZ : IsPullback gZ fZT fZ t) {j : V ⟶ Z} [IsOpenImmersion j] {j' : V' ⟶ Z'}
    [IsOpenImmersion j'] {gV : V' ⟶ V} (sqV : IsPullback gV j' j gZ)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (D : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) V D)
    [ExactPairing D ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)]
    (N : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hN : boundedConstructible (ModuleCat.{u + 1} Λ) V N) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N)) := by
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion Λ j
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion Λ j'
  have hbcN := isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic Λ aS t ht fZ j hZ sqV hN
  obtain ⟨eflip⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) V
  have hRH : boundedConstructible (ModuleCat.{u + 1} Λ) V
      ((RHom(V)[ModuleCat.{u + 1} Λ].obj (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))).obj N) :=
    (boundedConstructible _ V).prop_of_iso
      ((derivedHomIsoDerivedTensorOfExactPairing _ D _ N ≪≫ (eflip.app D).app N).symm)
      (boundedConstructible_tensor Λ V hN hD.1 hD.2)
  have hbcR := isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic Λ aS t ht fZ j hZ
    sqV hRH
  let eA := (L((gZ)^*[ModuleCat.{u + 1} Λ])).mapIso
      (derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) j K N) ≪≫
    asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app _)
  let eB := (RHom(Z')[ModuleCat.{u + 1} Λ].obj
      (op ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app N)) ≪≫
    derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) j' _ _
  have hρj' : IsIso (derivedHomUpperStarComparison _ j' ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N))) :=
    (isIso_derivedHomUpperStarComparison_iff_of_iso_right (ModuleCat.{u + 1} Λ) j'
    ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
    (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app N))).2
    (isIso_derivedHomUpperStarComparison_rightDerivedLowerStar _ j' _ _)
  have hρh : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) (j' ≫ gZ) K
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N)) := by
    rw [isIso_derivedHomUpperStarComparison_iff_comp _ gV j (j' ≫ gZ) sqV.w.symm]
    have := isIso_derivedHomUpperStarComparison_rightDerivedLowerStar _ j K N
    have := isIso_derivedHomUpperStarComparison_of_exactPairing _ gV D
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N))
    infer_instance
  rw [isIso_derivedHomUpperStarComparison_iff_comp _ j' gZ (j' ≫ gZ) rfl] at hρh
  have : IsIso ((L((j')^*[ModuleCat.{u + 1} Λ])).map
      (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N))) :=
    IsIso.of_isIso_comp_right _ (derivedHomUpperStarComparison _ j'
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N)))
  exact (derivedUpperStarLowerStarAdjunction _ j').isIso_of_isIso_map_of_iso_rightAdjoint_obj
    eA eB _

/-- Blueprint `lemma-restriction-geometric-generic-fibre`, internal-hom comparison, closed piece.
Let `i : W ⟶ Z` be a closed immersion with base change `i_T : W_T ⟶ Z_T` along `g : Z_T ⟶ Z`. If the
comparison of `g_W : W_T ⟶ W` is an isomorphism at `(i^* K, X)`, then the comparison of `g` is
one at `(K, Ri_* X)`. -/
lemma isIso_derivedHomUpperStarComparison_rightDerivedLowerStar_of_isClosedImmersion
    {Z Z' W W' : Scheme.{u}} {gZ : Z' ⟶ Z} {i : W ⟶ Z}
    [IsClosedImmersion i] {i' : W' ⟶ Z'} [IsClosedImmersion i'] {gW : W' ⟶ W}
    (sqW : IsPullback gW i' i gZ)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (X : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hX : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gW
      ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K) X)) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj X)) := by
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion_generic Λ i
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion_generic Λ i'
  have : IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqW.toCommSq) :=
    isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sqW
  let eA := (L((gZ)^*[ModuleCat.{u + 1} Λ])).mapIso
      (derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) i K X) ≪≫
    asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqW.toCommSq).app _)
  let eB := (RHom(Z')[ModuleCat.{u + 1} Λ].obj
      (op ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqW.toCommSq).app X)) ≪≫
    derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) i' _ _
  have hρi' : IsIso (derivedHomUpperStarComparison _ i' ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj ((R((i)_*[ModuleCat.{u + 1} Λ])).obj X))) :=
    (isIso_derivedHomUpperStarComparison_iff_of_iso_right (ModuleCat.{u + 1} Λ) i'
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqW.toCommSq).app X))).2
      (isIso_derivedHomUpperStarComparison_rightDerivedLowerStar _ i' _ _)
  have hρh : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) (i' ≫ gZ) K
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj X)) := by
    rw [isIso_derivedHomUpperStarComparison_iff_comp _ gW i (i' ≫ gZ) sqW.w.symm]
    have := isIso_derivedHomUpperStarComparison_rightDerivedLowerStar _ i K X
    have : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gW
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj ((R((i)_*[ModuleCat.{u + 1} Λ])).obj X))) :=
      (isIso_derivedHomUpperStarComparison_iff_of_iso_right (ModuleCat.{u + 1} Λ) gW _
        (asIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app X))).2
        hX
    infer_instance
  rw [isIso_derivedHomUpperStarComparison_iff_comp _ i' gZ (i' ≫ gZ) rfl] at hρh
  have : IsIso ((L((i')^*[ModuleCat.{u + 1} Λ])).map
      (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
        ((R((i)_*[ModuleCat.{u + 1} Λ])).obj X))) :=
    IsIso.of_isIso_comp_right _ (derivedHomUpperStarComparison _ i'
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj ((R((i)_*[ModuleCat.{u + 1} Λ])).obj X)))
  exact (derivedUpperStarLowerStarAdjunction _ i').isIso_of_isIso_map_of_iso_rightAdjoint_obj
    eA eB _

/-- **Dévissage in the second variable.** Let `i : W ⟶ Z` be a closed immersion with open
complement `j : U ⟶ Z`, and `g : Z' ⟶ Z` a morphism with base change `j'` of `j`, along which
`Rj_*` commutes with base change at `j^* M`. If the internal-hom comparison of `g` is an
isomorphism at `(K, Ri_* Ri^! M)` and at `(K, Rj_* j^* M)`, it is one at `(K, M)`: apply
`RHom(K, -)` and `g^*` to the supported localization triangle, and use that `j'^*` kills the
first term, so that no maps go from it to the third term
(`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃_of_subsingleton`). -/
lemma isIso_derivedHomUpperStarComparison_of_isIso_open_closed {Z Z' U U' W : Scheme.{u}}
    {gZ : Z' ⟶ Z} {i : W ⟶ Z}
    [IsClosedImmersion i] {j : U ⟶ Z} [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {j' : U' ⟶ Z'} [IsOpenImmersion j'] {gU : U' ⟶ U}
    (sqU : IsPullback gU j' j gZ)
    (K M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hbc : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqU.toCommSq).app
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M)))
    (hW : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj ((R(i)^![Λ]).obj M))))
    (hU : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M)))) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K M) := by
  obtain ⟨w, hw⟩ := (existsUnique_distTriang_supportedLocalization Λ i j hij
    M).exists
  obtain ⟨w₁, hw₁⟩ := exists_distTriang_derivedHom_right (op K) _ hw
  have hT₁ := (L((gZ)^*[ModuleCat.{u + 1} Λ])).map_distinguished _ hw₁
  obtain ⟨w₂, hw₂⟩ := exists_distTriang_derivedHom_right
    (op ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)) _
    ((L((gZ)^*[ModuleCat.{u + 1} Λ])).map_distinguished _ hw)
  let eX := (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).app
    ((R(i)^![Λ]).obj M)
  have hφ₁ : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M))) :=
    (isIso_derivedHomUpperStarComparison_iff_of_iso_right _ gZ K eX).2 hW
  have : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      (supportedLocalizationTriangle Λ i j M w).obj₁) := hφ₁
  refine Pretriangulated.isIso₂_of_isIso₁₃_of_subsingleton hT₁ hw₂ _ _
    (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M)))
    (derivedHomUpperStarComparison_naturality _ gZ K _)
    (derivedHomUpperStarComparison_naturality _ gZ K _) ?_
  -- the third term is `Rj'_*` of an object, and `j'^*` kills the first one
  let eB := (RHom(Z')[ModuleCat.{u + 1} Λ].obj
      (op ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqU.toCommSq).app
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M))) ≪≫
    derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) j' _ _
  have hdisj : Disjoint (Set.range i.base) (Set.range j.base) := hij ▸ disjoint_compl_left
  have hz₀ : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj
      ((RHom(Z)[ModuleCat.{u + 1} Λ].obj (op K)).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M)))) :=
    (isZero_upperStar_rightDerivedLowerShriek _ i j hdisj _).of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
        D((j)^*[ModuleCat.{u + 1} Λ]).mapIso ((RHom(Z)[ModuleCat.{u + 1} Λ].obj (op K)).mapIso eX ≪≫
          derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) i K _ ≪≫
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).app _).symm))
  have hz : IsZero ((L((j')^*[ModuleCat.{u + 1} Λ])).obj ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj
      ((RHom(Z)[ModuleCat.{u + 1} Λ].obj (op K)).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M))))) :=
    ((L((gU)^*[ModuleCat.{u + 1} Λ])).map_isZero hz₀).of_iso
      (((leftDerivedUpperStarComp _ j' gZ (j' ≫ gZ) rfl).app _).symm ≪≫
        (leftDerivedUpperStarComp _ gU j (j' ≫ gZ) sqU.w.symm).app _)
  have : Subsingleton (((L((j')^*[ModuleCat.{u + 1} Λ])).obj (((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj
      ((RHom(Z)[ModuleCat.{u + 1} Λ].obj (op K)).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M))))⟦(1 : ℤ)⟧)) ⟶
      (RHom(U')[ModuleCat.{u + 1} Λ].obj (op ((L((j')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)))).obj
          ((L((gU)^*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj M))) :=
    ⟨fun _ _ ↦ ((((shiftFunctor _ (1 : ℤ)).map_isZero hz).of_iso
      (((L((j')^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app _))).eq_of_src _ _⟩
  exact @Equiv.subsingleton _ _ ((Iso.homCongr (Iso.refl _) eB).trans
    ((derivedUpperStarLowerStarAdjunction _ j').homEquiv _ _).symm) this

/-- Blueprint `lemma-restriction-geometric-generic-fibre`, third assertion: **the internal Hom
commutes with generic base change.** Let `S` be integral and of finite type over a field `k`, let
`Λ` be a finite ring whose exponent is invertible on `S`, and let `t : T ⟶ S` be a morphism from a
noetherian scheme lying over the generic point of `S` (e.g. a geometric generic point). Let `X`
be of finite type over `S`, with base change `g : X_T ⟶ X`. For `K ∈ Dctf(X, Λ)` and
`M ∈ Dᵇc(X, Λ)`, the canonical comparison
`g^* RHom(K, M) ⟶ RHom(g^* K, g^* M)` (`AlgebraicGeometry.Etale.derivedHomUpperStarComparison`)
is an isomorphism. It preserves evaluation
(`AlgebraicGeometry.Etale.derivedHomUpperStarComparison_ev`). -/
theorem isIso_derivedHomUpperStarComparison_of_generic {k : Type u} [Field k]
    {S : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S)
    (ht : ∀ x, t.base x = genericPoint S) {X X' : Scheme.{u}} (fX : X ⟶ S)
    [LocallyOfFiniteType fX] [QuasiCompact fX] {g : X' ⟶ X} {fT : X' ⟶ T}
    (hX : IsPullback g fT fX t)
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g K M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (fX ≫ aS)
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian (fX ≫ aS) }
  suffices key : ∀ C : TopologicalSpace.Closeds X, ∀ (Z : Scheme.{u}) (ι : Z ⟶ X)
      [IsClosedImmersion ι], Set.range ι.base ⊆ C → ∀ (Z' : Scheme.{u}) (gZ : Z' ⟶ Z)
      (fZT : Z' ⟶ T), IsPullback gZ fZT (ι ≫ fX) t →
      ∀ K M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z K →
      boundedConstructible (ModuleCat.{u + 1} Λ) Z M →
      IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K M) from
    key ⊤ X (𝟙 X) (by simp) X' g fT (by simpa using hX) K M hK hM
  intro C
  induction C using WellFoundedLT.induction with
  | _ C IH =>
  intro Z ι _ hι Z' gZ fZT hsq K M hK hM
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace ((ι ≫ fX) ≫ aS)
  have : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian ((ι ≫ fX) ≫ aS) }
  have : HasInvertibleExponent Λ Z := .of_hom (ι ≫ fX)
  rcases isEmpty_or_nonempty Z with hE | hE
  · have : IsEmpty Z' := ⟨fun z ↦ IsEmpty.false (gZ.base z)⟩
    exact IsZero.isIso
      (_root_.DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) _)
      (_root_.DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) _) _
  obtain ⟨V, hVd, hV⟩ := exists_dense_open_exactPairing Λ hK
  obtain ⟨D, hD, ⟨ep⟩⟩ := hV V le_rfl
  let i := V.closedComplement
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by simp [i]
  have sqW := (IsPullback.of_hasPullback gZ i).flip
  have sqV := (IsPullback.of_hasPullback gZ V.ι).flip
  have hbc := isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic Λ aS t ht (ι ≫ fX)
    V.ι hsq sqV (boundedConstructible_leftDerivedUpperStar _ V.ι hM)
  refine isIso_derivedHomUpperStarComparison_of_isIso_open_closed Λ hij sqV K M hbc ?_
    (isIso_derivedHomUpperStarComparison_rightDerivedLowerStar_of_generic Λ aS t ht (ι ≫ fX) hsq
      sqV K D hD _
      (boundedConstructible_leftDerivedUpperStar _ V.ι hM))
  refine isIso_derivedHomUpperStarComparison_rightDerivedLowerStar_of_isClosedImmersion Λ sqW K _ ?_
  have hsqW : IsPullback (pullback.snd gZ i) (pullback.fst gZ i ≫ fZT) ((i ≫ ι) ≫ fX) t := by
    simpa only [Category.assoc] using sqW.paste_vert hsq
  let C' : TopologicalSpace.Closeds X :=
    ⟨Set.range (i ≫ ι).base, (i ≫ ι).isClosedEmbedding.isClosed_range⟩
  have hC : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ hι ?_) fun heq ↦ ?_
    · obtain ⟨w, rfl⟩ := hx
      exact ⟨i.base w, rfl⟩
    · obtain ⟨v, hv⟩ := hVd.nonempty
      have hvC : ι.base v ∈ (C' : Set X) := heq ▸ hι ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := hvC
      have hwv : i.base w = v := ι.isClosedEmbedding.injective (by simpa using hw)
      have hvi : v ∈ Set.range i.base := ⟨w, hwv⟩
      rw [hij] at hvi
      exact hvi ⟨⟨v, hv⟩, rfl⟩
  exact IH C' hC _ (i ≫ ι) subset_rfl _ _ _ hsqW _ _
    (constructibleFiniteTor_leftDerivedUpperStar _ i hK)
    (boundedConstructible_rightDerivedUpperShriek_of_isClosedImmersion Λ ((ι ≫ fX) ≫ aS) i hM)

end Etale
end AlgebraicGeometry
