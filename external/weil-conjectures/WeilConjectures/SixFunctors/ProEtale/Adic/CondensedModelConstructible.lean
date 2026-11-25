/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible

/-!
# Constructibility in the two models of `ℓ`-adic sheaves

Through the equivalence `E_X : AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}`
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`) between sheaves of `ℚ̄_ℓ,X`-modules and
module objects over the condensed coefficient ring `ℚ̲̄_ℓ,X`, the two notions of constructibility
agree on a noetherian scheme:

- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.isConstructibleModuleObject`: on a
  quasi-compact quasi-separated scheme, a constructible `ℓ`-adic sheaf `F` is stratified lisse,
  and on each stratum `E(F)` is locally free
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isLocallyFree`), hence locally finitely presented;
- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_of_isLocallyFinitelyPresented`: on a scheme with
  noetherian underlying space, a locally finitely presented module object over `ℚ̲̄_ℓ` is
  pro-étale locally free (`AlgebraicGeometry.ProEtale.condensedQbar_lfp_locally_free`), so the
  corresponding `ℓ`-adic sheaf is lisse;
- `AlgebraicGeometry.ProEtale.isAdicConstructibleSheaf_of_isConstructibleModuleObject`: hence a
  constructible module object over `ℚ̲̄_ℓ` on a noetherian scheme is a constructible `ℓ`-adic
  sheaf, lisse on the strata of the same stratification.
- `AlgebraicGeometry.ProEtale.bounded_homologyProperty_of_boundedConstructible`: an `ℓ`-adic
  complex whose counterpart in the derived category of module objects is bounded constructible is
  bounded with constructible cohomology sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- A finite family of immersions whose ranges are constructible and partition `X` is a
stratification of `X`. -/
noncomputable def Scheme.Stratification.ofImmersions {X : Scheme.{u}} {ι : Type} [Finite ι]
    (Z : ι → Scheme.{u}) (i : (k : ι) → Z k ⟶ X) (hi : ∀ k, IsImmersion (i k))
    (hc : ∀ k, Topology.IsConstructible (Set.range (i k).base))
    (hcover : ∀ x : X, ∃! k, x ∈ Set.range (i k).base) :
    Scheme.Stratification X :=
  letI := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  { n := Fintype.card ι
    stratum := fun a ↦ Set.range (i (e a)).base
    isLocallyClosed_stratum := fun a ↦ (i (e a)).isLocallyClosed_range
    isConstructible_stratum := fun a ↦ hc (e a)
    iUnion_stratum_eq_univ := Set.eq_univ_of_forall fun x ↦ by
      obtain ⟨k, hk, -⟩ := hcover x
      exact Set.mem_iUnion.2 ⟨e.symm k, by rw [e.apply_symm_apply]; exact hk⟩
    pairwise_disjoint_stratum := fun a b hab ↦ Set.disjoint_left.2 fun x ha hb ↦
      hab (e.injective ((hcover x).unique ha hb))
    domain := fun a ↦ Z (e a)
    immersion := fun a ↦ i (e a)
    isImmersion := fun a ↦ hi (e a)
    range_immersion := fun _ ↦ rfl }

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The module object over `ℚ̲̄_ℓ,X` of a lisse `ℓ`-adic sheaf is locally finitely presented. -/
lemma IsAdicLisseSheaf.isLocallyFinitelyPresented {X : Scheme.{u}} {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) :=
  hH.isLocallyFree.isLocallyFinitelyPresented

/-- **Constructible `ℓ`-adic sheaves give constructible module objects**: on a quasi-compact
quasi-separated scheme, the module object over `ℚ̲̄_ℓ,X` of a constructible `ℓ`-adic sheaf is
constructible. The sheaf is stratified lisse, and the module object of a lisse sheaf is locally
finitely presented, the equivalence commuting with pullbacks. -/
theorem IsAdicConstructibleSheaf.isConstructibleModuleObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj F) := by
  obtain ⟨ι, _, Z, i, hi, hc, hcover, hL⟩ := hF.isAdicStratifiedLisseSheaf
  refine ⟨Scheme.Stratification.ofImmersions Z i hi hc hcover, fun a ↦ ?_⟩
  refine (CondensedRing.isLocallyFinitelyPresented_mapMod_iff _ _ _).2 ?_
  exact IsLocallyFinitelyPresented.of_iso ((adicUpperStarCompCondensedModIso l _).app F)
    (hL _).isLocallyFinitelyPresented

/-- **Locally finitely presented module objects are lisse**: on a scheme with noetherian
underlying space, an `ℓ`-adic sheaf whose module object over `ℚ̲̄_ℓ` is pro-étale locally
finitely presented is lisse. The module object is pro-étale locally free of finite rank
(`AlgebraicGeometry.ProEtale.condensedQbar_lfp_locally_free`), and being lisse is local. -/
theorem isAdicLisseSheaf_of_isLocallyFinitelyPresented {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {G : AdicSheaf l X}
    (hG : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj G)) :
    IsAdicLisseSheaf G := by
  obtain ⟨𝒲, h𝒲⟩ := condensedQbar_lfp_locally_free l X _ hG
  refine IsAdicLisseSheaf.of_cover 𝒲.f 𝒲.mem₀ fun j ↦ ?_
  obtain ⟨r, ⟨e⟩⟩ := h𝒲 j
  exact (isAdicLisseSheaf_inverse_obj_finiteFree (l := l) (𝒲.X j) r).of_iso
    ((adicSheafEquivCondensedMod l (𝒲.X j)).inverse.mapIso
      (e.symm ≪≫ ((adicUpperStarCompCondensedModIso l (𝒲.f j)).app G).symm) ≪≫
      ((adicSheafEquivCondensedMod l (𝒲.X j)).unitIso.app _).symm)

/-- **Constructible module objects give constructible `ℓ`-adic sheaves**: on a scheme with
noetherian underlying space, an `ℓ`-adic sheaf whose module object over `ℚ̲̄_ℓ` is constructible is
constructible, lisse on the strata of the same stratification
(`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_of_isLocallyFinitelyPresented`). -/
theorem isAdicConstructibleSheaf_of_isConstructibleModuleObject {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {G : AdicSheaf l X}
    (hG : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj G)) :
    IsAdicConstructibleSheaf G := by
  obtain ⟨S, hS⟩ := hG
  refine IsAdicStratifiedLisseSheaf.isAdicConstructibleSheaf
    ⟨Fin S.n, inferInstance, S.domain, S.immersion, S.isImmersion, fun a ↦ ?_, fun x ↦ ?_,
      fun a ↦ ?_⟩
  · rw [S.range_immersion]
    exact S.isConstructible_stratum a
  · have hx : x ∈ ⋃ a, S.stratum a := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
    refine ⟨a, show x ∈ Set.range (S.immersion a) by rwa [S.range_immersion], fun b hb ↦ ?_⟩
    change x ∈ Set.range (S.immersion b) at hb
    rw [S.range_immersion] at hb
    by_contra hba
    exact Set.disjoint_left.1 (S.pairwise_disjoint_stratum hba) hb ha
  · have : TopologicalSpace.NoetherianSpace (S.domain a) :=
      (S.immersion a).isEmbedding.isInducing.noetherianSpace
    exact isAdicLisseSheaf_of_isLocallyFinitelyPresented
      (IsLocallyFinitelyPresented.of_iso ((adicUpperStarCompCondensedModIso l _).app G).symm
        ((CondensedRing.isLocallyFinitelyPresented_mapMod_iff _ _ _).1 (hS a)))

/-- An `ℓ`-adic complex on a scheme with noetherian underlying space whose module-object
counterpart over `ℚ̲̄_ℓ` (`AlgebraicGeometry.ProEtale.adicSheafDerivedEquivCondensedMod`) is
bounded constructible is bounded with constructible cohomology sheaves. -/
theorem bounded_homologyProperty_of_boundedConstructible {Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Y] {K : DerivedCategory (AdicSheaf l Y)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) Y)
      ((adicSheafDerivedEquivCondensedMod l Y).functor.obj K)) :
    DerivedCategory.TStructure.t.bounded K ∧
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y) K := by
  let E := adicSheafEquivCondensedMod l Y
  have e (n : ℤ) := (homologyFunctorCompAdicSheafEquivCondensedModIso (l := l) (X := Y) n).app K
  have hz (n : ℤ) (h : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((adicSheafDerivedEquivCondensedMod l Y).functor.obj K))) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj K) :=
    (E.inverse.map_isZero (h.of_iso (e n))).of_iso (E.unitIso.app _)
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun n ↦ ?_⟩
  · exact (DerivedCategory.isGE_iff K a).2 fun n hn ↦
      hz n ((DerivedCategory.isGE_iff _ a).1 ha n hn)
  · exact (DerivedCategory.isLE_iff K b).2 fun n hn ↦
      hz n ((DerivedCategory.isLE_iff _ b).1 hb n hn)
  · exact isAdicConstructibleSheaf_of_isConstructibleModuleObject
      (IsConstructibleModuleObject.of_iso (e n).symm (hc n))

end ProEtale

end AlgebraicGeometry
