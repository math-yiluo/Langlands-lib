/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.GenericRestriction.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.FieldExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.TraceFormula.FieldDualizable

/-!
# Internal homs commute with a change of the base field

Let `k ⟶ L` be a field extension, `X` a separated `k`-scheme of finite type and
`π : X_L = X ×_k L ⟶ X` the projection. This file proves that the derived pullback `Lπ^*` commutes
with internal homs of bounded constructible `ℚ̄_ℓ`-complexes: the comparison
`Lπ^* RHom(K, M) ⟶ RHom(Lπ^* K, Lπ^* M)`
(`ProEtale.CondensedRing.ihomUpperStarComparison`) is an isomorphism
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_fieldExtension`). This is the
internal-hom assertion of blueprint `lemma-restriction-geometric-generic-fibre` (2) for a change of
the base field; the geometric generic fibre of blueprint `lemma-restriction-geometric-generic-fibre`
is such a change of base field followed by the weakly étale inclusion of a generic point
(`WeilConjectures.PoincareDuality.GenericRestriction.GenericFibre`).

## Proof

As in the blueprint, by noetherian induction on the closed subschemes `Z` of `X`, in the second
variable `M`. By topological invariance we may replace `Z` by its reduction. On a reduced `Z`,
`K` is dualizable on a nonempty open `j : U ⟶ Z`
(`ProEtale.CondensedRing.exists_isOpenImmersion_exactPairing_upperStar`, from generic
dualizability `ProEtale.CondensedRing.exists_isOpenImmersion_triangEnvelope_isDualizable`), so the
comparison of `U_L ⟶ U` at `(Lj^* K, -)` is an isomorphism. Direct images along open and closed
immersions commute with the change of the base field (Stacks 0F1C,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension`), so the formal
lemmas of `WeilConjectures.PoincareDuality.GenericRestriction.Comparison` reduce the comparison
at `(K, M)` to the comparisons on `U` and on the closed complement of `U`, which holds by
induction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Generic dualizability**, in the ambient derived category: a bounded constructible
`ℚ̄_ℓ`-complex `K` on a nonempty reduced separated `k`-scheme of finite type `Z` has a left dual
on some nonempty open subscheme `U ⟶ Z`. It is
`ProEtale.CondensedRing.exists_isOpenImmersion_triangEnvelope_isDualizable`, the dualizable objects
of the ambient derived category forming a triangulated subcategory stable under retracts. -/
theorem exists_isOpenImmersion_exactPairing_upperStar (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsReduced Z.left]
    [Nonempty Z.left]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) K) :
    ∃ (U : Over (Spec (.of k))) (_ : LocallyOfFiniteType U.hom) (_ : QuasiCompact U.hom)
      (_ : IsSeparated U.hom) (_ : Nonempty U.left) (j : U ⟶ Z) (_ : IsOpenImmersion j.left)
      (D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left))),
      Nonempty (ExactPairing D ((L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  obtain ⟨U, h₁, h₂, h₃, _, hU, j, hj, hE⟩ :=
    exists_isOpenImmersion_triangEnvelope_isDualizable ℓ Z ⟨K, hK⟩
  -- the dualizable objects of `Dᵇc(U)` lie in the ambient dualizable ones, which form a
  -- triangulated subcategory stable under retracts
  have : ((ambientDualizable ℓ U.left).inverseImage
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        U.left)).ι).IsStableUnderRetracts :=
    ⟨fun r h ↦ IsDualizable.of_retract (r.map _) h⟩
  have hle : ObjectProperty.triangEnvelope
      (C := Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) IsDualizable ≤
      (ambientDualizable ℓ U.left).inverseImage (boundedConstructible _).ι :=
    (ObjectProperty.triangEnvelope_le_iff _).2 fun K hK ↦
      (isDualizable_iff_isDualizable_obj ℓ K).1 hK
  obtain ⟨hD⟩ := IsDualizable.of_iso
    ((boundedConstructibleUpperStarCompatibility _ ℓ j).app ⟨K, hK⟩) (hle _ hE)
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left))
  let : ExactPairing ((L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K) hD.rightDual :=
    hD.exact
  exact ⟨U, h₁, h₂, h₃, hU, j, hj, hD.rightDual, ⟨BraidedCategory.exactPairing_swap _ _⟩⟩

variable {L : Type u} [Field L] [Algebra k L]

/-- The prime `ℓ` is invertible on `Spec k`, `k` being of characteristic `≠ ℓ`. -/
lemma isUnit_natCast_Γ_spec : IsUnit (ℓ : Γ(Spec (.of k), ⊤)) := by
  have hℓ : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k ≠ ℓ) ?_
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) Fact.out).1
      ((ringChar.spec k ℓ).1 h)
  simpa using hℓ.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The base change `X_L` of a quasi-compact separated `k`-scheme `X` along a field extension
`k ⟶ L` is quasi-compact and quasi-separated. -/
lemma compactSpace_and_quasiSeparatedSpace_of_isPullback_fieldExtension
    {X : Over (Spec (.of k))} [QuasiCompact X.hom] [IsSeparated X.hom] {X' : Scheme.{u}}
    {π : X' ⟶ X.left} {a' : X' ⟶ Spec (.of L)}
    (sq : IsPullback π a' X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    CompactSpace X' ∧ QuasiSeparatedSpace X' := by
  have : QuasiCompact a' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated a' :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  exact ⟨QuasiCompact.compactSpace_of_compactSpace a', quasiSeparatedSpace_of_quasiSeparated a'⟩

omit [Fact (ringChar k).Prime] in
/-- The base change along `π_Z : Z_L ⟶ Z` of a morphism `f : V ⟶ Z` of `k`-schemes is the base
change `V_L ⟶ V` of `V` along the field extension (pasting of cartesian squares). -/
lemma isPullback_fieldExtension_of_isPullback {Z V : Over (Spec (.of k))} (f : V ⟶ Z)
    {Z' V' : Scheme.{u}} {πZ : Z' ⟶ Z.left} {T : Scheme.{u}} {aZ : Z' ⟶ T}
    {ι : T ⟶ Spec (.of k)} (sqZ : IsPullback πZ aZ Z.hom ι)
    {πV : V' ⟶ V.left} {f' : V' ⟶ Z'} (sq : IsPullback πV f' f.left πZ) :
    IsPullback πV (f' ≫ aZ) V.hom ι := by
  have := sq.paste_vert sqZ
  rwa [Over.w f] at this

/-- **Direct images commute with the change of the base field**: for a morphism `f : V ⟶ Z` of
separated `k`-schemes of finite type and its base change `f' : V_L ⟶ Z_L` along the field
extension `k ⟶ L`, the base change map `Lπ_Z^* Rf_* N ⟶ Rf'_* Lπ_V^* N` is an isomorphism at
bounded constructible `N` (Stacks 0F1C,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension`). -/
lemma isIso_baseChangeMap_app_of_isPullback_fieldExtension {Z V : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] (f : V ⟶ Z)
    {Z' V' : Scheme.{u}} {πZ : Z' ⟶ Z.left} {aZ : Z' ⟶ Spec (.of L)}
    (sqZ : IsPullback πZ aZ Z.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {πV : V' ⟶ V.left} {f' : V' ⟶ Z'} (sq : IsPullback πV f' f.left πZ)
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)))
    (hN : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left) N) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq.toCommSq).app N) := by
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isPullback_fieldExtension sqZ
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isPullback_fieldExtension
    (isPullback_fieldExtension_of_isPullback f sqZ sq)
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  have : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_quasiSeparated V.hom
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsNoetherian V.left := {}
  have : QuasiSeparated f.left := by
    have : QuasiSeparated (f.left ≫ Z.hom) := by
      rw [Over.w f]
      infer_instance
    exact QuasiSeparated.of_comp f.left Z.hom
  exact isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension Z.hom aZ sqZ ℓ sq
    (isUnit_natCast_Γ_spec ℓ) N hN

/-- **The comparison on direct images, for a change of the base field**: let `f : V ⟶ Z` be a
morphism of separated `k`-schemes of finite type with fully faithful `Rf_*` (an open or a closed
immersion), and `f' : V_L ⟶ Z_L` its base change along the field extension, again with fully
faithful `Rf'_*`. If the comparison of `π_V : V_L ⟶ V` is an isomorphism at `(Lf^* K, N)`, then
the comparison of `π_Z` is an isomorphism at `(K, Rf_* N)`, for bounded constructible `K` and `N`:
`Rf_*` commutes with the change of the base field
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isPullback_fieldExtension`). -/
lemma isIso_ihomUpperStarComparison_rightDerivedLowerStar_of_fieldExtension
    {Z V : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (f : V ⟶ Z)
    [IsIso (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).counit]
    {Z' V' : Scheme.{u}} {πZ : Z' ⟶ Z.left} {aZ : Z' ⟶ Spec (.of L)}
    (sqZ : IsPullback πZ aZ Z.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {πV : V' ⟶ V.left} {f' : V' ⟶ Z'}
    [IsIso (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f').counit]
    (sq : IsPullback πV f' f.left πZ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) K)
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)))
    (hN : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left) N)
    (hρ : IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) πV
      ((L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K) N)) :
    IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) πZ K
      ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj N)) := by
  have hfK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)
      ((L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K) :=
    boundedConstructible_leftDerivedUpperStar_obj _ ℓ f ⟨K, hK⟩
  have hH : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)
      ((ihom ((L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)).obj N) :=
    ObjectProperty.prop_ihom _ hfK hN
  have h₁ := isIso_baseChangeMap_app_of_isPullback_fieldExtension ℓ f sqZ sq N hN
  have h₂ := isIso_baseChangeMap_app_of_isPullback_fieldExtension ℓ f sqZ sq _ hH
  refine isIso_ihomUpperStarComparison_rightDerivedLowerStar_of_isPullback _ sq K N ?_ ?_ hρ
  · exact_mod_proofs h₁
  · exact_mod_proofs h₂

/-- `ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isIso_open_closed`, with the base
change hypothesis at `Lj^* M` deduced from base change at all objects satisfying a property `P`
(stating the hypothesis at a variable object keeps the identification of the instances it
involves cheap). -/
private lemma isIso_ihomUpperStarComparison_of_isIso_open_closed_of_forall
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z Z' U U' W : Scheme.{u}} {gZ : Z' ⟶ Z} {i : W ⟶ Z} [IsClosedImmersion i]
    {j : U ⟶ Z} [IsOpenImmersion j] [QuasiCompact j] {j' : U' ⟶ Z'} [IsOpenImmersion j']
    {gU : U' ⟶ U}
    [(boundedConstructible (condensedRingObj Λ Z)).IsTriangulated]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (sqU : IsPullback gU j' j gZ)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hM : boundedConstructible (condensedRingObj Λ Z) M)
    (hjM : boundedConstructible (condensedRingObj Λ Z) ((R((j)_*⟦Λ⟧)).obj ((L((j)^*⟦Λ⟧)).obj M)))
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))) (hPM : P ((L((j)^*⟦Λ⟧)).obj M))
    (hbc : ∀ N, P N → IsIso ((baseChangeMap Λ sqU.toCommSq).app N))
    (hU : IsIso (ihomUpperStarComparison Λ gZ K ((R((j)_*⟦Λ⟧)).obj ((L((j)^*⟦Λ⟧)).obj M))))
    (hW : ∀ X : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj Λ W)), boundedConstructible (condensedRingObj Λ W) X →
      IsIso (ihomUpperStarComparison Λ gZ K ((R((i)_*⟦Λ⟧)).obj X))) :
    IsIso (ihomUpperStarComparison Λ gZ K M) :=
  isIso_ihomUpperStarComparison_of_isIso_open_closed Λ hij sqU K M hM hjM (hbc _ hPM) hU hW

/-- The noetherian induction behind `isIso_ihomUpperStarComparison_of_fieldExtension`: for a
closed immersion `c : Z ⟶ X` with image in the closed subset `C` of `X`, the comparison of the
base change `π_Z : Z_L ⟶ Z` is an isomorphism at bounded constructible `(K, M)`. By topological
invariance we may replace `Z` by its reduction; for reduced nonempty `Z`, `K` has a left dual on
a nonempty open subscheme `U` (`exists_isOpenImmersion_exactPairing_upperStar`), and the
dévissage in the second variable
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isIso_open_closed`) reduces to `U`
and to the closed complement of `U`, whose image in `X` is strictly smaller. -/
theorem isIso_ihomUpperStarComparison_of_fieldExtension_of_range_subset (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (C : TopologicalSpace.Closeds X.left) :
    ∀ (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      [IsSeparated Z.hom] (c : Z ⟶ X) [IsClosedImmersion c.left],
      Set.range c.left.base ⊆ C → ∀ {Z' : Scheme.{u}} {πZ : Z' ⟶ Z.left}
        {aZ : Z' ⟶ Spec (.of L)},
        IsPullback πZ aZ Z.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))) →
        ∀ K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)),
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) K →
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) M →
          IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) πZ K M) := by
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  -- by topological invariance, we may replace `Z` by its reduction
  suffices H : ∀ (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      [IsSeparated Z.hom] [IsReduced Z.left] (c : Z ⟶ X) [IsClosedImmersion c.left],
      Set.range c.left.base ⊆ C → ∀ {Z' : Scheme.{u}} {πZ : Z' ⟶ Z.left}
        {aZ : Z' ⟶ Spec (.of L)},
        IsPullback πZ aZ Z.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))) →
        ∀ K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)),
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) K →
          boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) M →
          IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) πZ K M) by
    intro Z _ _ _ c _ hc Z' πZ aZ sqZ K M hK hM
    let r := overReductionι Z
    have : IsClosedImmersion (r ≫ c).left := by
      rw [Over.comp_left]
      infer_instance
    have := isEquivalence_upperStar_of_isUniversalHomeomorphism
      (Profinite.padicAlgClRingObj ℓ) r.left
    have : (L((r.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).IsEquivalence :=
      Functor.isEquivalence_of_iso (leftDerivedUpperStarIsoMapDerivedCategory _ r.left).symm
    have := (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      r.left).unit_isIso_of_L_fully_faithful
    refine (isIso_ihomUpperStarComparison_iff_of_iso_right _ πZ K
      (asIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        r.left).unit.app M))).2 ?_
    have sq := IsPullback.of_hasPullback r.left πZ
    exact isIso_ihomUpperStarComparison_rightDerivedLowerStar_of_fieldExtension ℓ r sqZ sq K hK _
      (boundedConstructible_leftDerivedUpperStar_obj _ ℓ r ⟨M, hM⟩)
      (H _ (r ≫ c) (fun y ⟨z, hz⟩ ↦ hc ⟨r.left.base z, by simpa using hz⟩)
        (isPullback_fieldExtension_of_isPullback r sqZ sq) _ _
        (boundedConstructible_leftDerivedUpperStar_obj _ ℓ r ⟨K, hK⟩)
        (boundedConstructible_leftDerivedUpperStar_obj _ ℓ r ⟨M, hM⟩))
  intro Z _ _ _ _ c _ hc Z' πZ aZ sqZ K M hK hM
  rcases isEmpty_or_nonempty Z.left with hZ | hZ
  · have : IsEmpty Z' := ⟨fun z ↦ IsEmpty.false (πZ.base z)⟩
    exact isIso_of_source_target_iso_zero _ (isZero_derivedCategory_of_isEmpty ℓ _).isoZero
      (isZero_derivedCategory_of_isEmpty ℓ _).isoZero
  obtain ⟨U, _, _, _, ⟨u⟩, j, _, D, ⟨hD⟩⟩ :=
    exists_isOpenImmersion_exactPairing_upperStar ℓ Z K hK
  let i := overClosedComplement j
  have hcompl := isCompl_range_overClosedComplement j
  have : IsClosedImmersion (i ≫ c).left := by
    rw [Over.comp_left]
    infer_instance
  have hlt : (⟨Set.range (i ≫ c).left.base, (i ≫ c).left.isClosedEmbedding.isClosed_range⟩ :
      TopologicalSpace.Closeds X.left) < C := by
    refine lt_of_le_of_ne (fun y ⟨z, hz⟩ ↦ hc ⟨i.left.base z, by simpa using hz⟩) fun h ↦ ?_
    have hy : c.left.base (j.left.base u) ∈ (C : Set X.left) := hc ⟨_, rfl⟩
    rw [← h] at hy
    obtain ⟨z, hz⟩ := hy
    have hz' : i.left.base z = j.left.base u :=
      c.left.isClosedEmbedding.injective (by simpa using hz)
    exact Set.disjoint_left.1 hcompl.disjoint ⟨z, hz'⟩ ⟨u, rfl⟩
  have : QuasiCompact j.left := by
    have : QuasiCompact (j.left ≫ Z.hom) := by rw [Over.w j]; infer_instance
    exact QuasiCompact.of_comp j.left Z.hom
  have sqU := IsPullback.of_hasPullback j.left πZ
  have hjM := boundedConstructible_leftDerivedUpperStar_obj _ ℓ j ⟨M, hM⟩
  refine isIso_ihomUpperStarComparison_of_isIso_open_closed_of_forall _ hcompl sqU K M hM
    (boundedConstructible_rightDerivedLowerStar_obj ℓ j ⟨_, hjM⟩) _ hjM
    (fun N hN ↦ by exact_mod_proofs
      isIso_baseChangeMap_app_of_isPullback_fieldExtension ℓ j sqZ sqU N hN) ?_ fun N hN ↦ ?_
  · exact isIso_ihomUpperStarComparison_rightDerivedLowerStar_of_fieldExtension ℓ j sqZ sqU K hK
      _ hjM (isIso_ihomUpperStarComparison_of_exactPairing _ _ D _ _)
  · have sqW := IsPullback.of_hasPullback i.left πZ
    exact isIso_ihomUpperStarComparison_rightDerivedLowerStar_of_fieldExtension ℓ i sqZ sqW K hK
      N hN (ih _ hlt _ (i ≫ c) subset_rfl (isPullback_fieldExtension_of_isPullback i sqZ sqW) _ _
        (boundedConstructible_leftDerivedUpperStar_obj _ ℓ i ⟨K, hK⟩) hN)

/-- **Internal homs commute with a change of the base field** (blueprint
`lemma-restriction-geometric-generic-fibre` (2), for the change of the base field `k ⟶ L`): for a
separated `k`-scheme of finite type `X`, its base change `π : X_L ⟶ X` and bounded constructible
`ℚ̄_ℓ`-complexes `K` and `M` on `X`, the comparison
`Lπ^* RHom(K, M) ⟶ RHom(Lπ^* K, Lπ^* M)` is an isomorphism. The extension `L / k` may be
transcendental and inseparable. -/
theorem isIso_ihomUpperStarComparison_of_fieldExtension (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Scheme.{u}} {π : X' ⟶ X.left} {a' : X' ⟶ Spec (.of L)}
    (sq : IsPullback π a' X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) M) :
    IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) π K M) := by
  have : IsClosedImmersion (𝟙 X : X ⟶ X).left := inferInstanceAs (IsClosedImmersion (𝟙 X.left))
  exact isIso_ihomUpperStarComparison_of_fieldExtension_of_range_subset ℓ X ⊤ X (𝟙 X)
    (Set.subset_univ _) sq K M hK hM

end AlgebraicGeometry.ProEtale.CondensedRing
