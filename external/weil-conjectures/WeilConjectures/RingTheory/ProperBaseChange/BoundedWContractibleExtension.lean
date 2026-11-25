/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.SetTheory.Cardinal.Arithmetic
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.StrictWCover.ThmPeIndetaleRefinementPart3Supplement2
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.StrictWCover.StrictWCoverSize
import WeilConjectures.RingTheory.ProperBaseChange.ProfiniteComponentRingPullback
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BoundedExtremallyDisconnectedCover
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.RingTheory.Localization.Cardinality

/-! # Bounded w-contractible extensions

Source: Stacks Project, Tags 0981, 0983, 0984 and 0989
(blueprint: lem-weil-pbc-wcontractible-ring-extension).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace RingHom

/-- Every ring has a bounded faithfully flat ind-etale extension splitting all faithfully
flat weakly etale extensions, and its spectrum is a singleton pro-etale cover.
Source: Stacks Project, Tags 0981, 0983, 0984 and 0989
(blueprint: lem-weil-pbc-wcontractible-ring-extension).

Proof plan:
1. Form the strict w-local cover C_A. The strict-w-cover theorem gives faithful flatness,
ind-etaleness, w-locality and strictly henselian maximal local rings. Its size theorem gives
|C_A| ≤ κ.
2. The profinite component-ring-pullback theorem identifies its component space with its
closed points, hence bounds that space by 2^κ. The bounded-extremally-disconnected-cover
lemma gives a profinite extremally disconnected surjection T onto it, of size ≤ 2^(2^(2^κ)).
3. Apply profinite-component-ring-pullback to construct C_A → D, ind-Zariski and ind-etale,
identifying local rings and preserving w-locality. Surjectivity on spectra and flatness,
using ind-etale-stability and flat-surjective-spectrum-faithfully-flat, make A → D faithfully
flat and ind-etale. The maximal local rings of D remain strictly henselian.
4. The wcontractible-geometric-criterion supplies the retraction of every faithfully flat
weakly etale D → B from these conditions and the extremal disconnectedness of T.
5. Each maximal local ring of D has size ≤ κ, since fractions in the corresponding local
ring of C_A are represented by pairs of elements of C_A. The diagonal map into the product
of maximal local rings is injective: a nonzero element has its annihilator contained in a
maximal ideal and cannot vanish in that localization. There are ≤ |T| such ideals, giving
|D| ≤ κ^(2^(2^(2^κ))). For the zero ring the product is empty and the bound still holds.
6. For every affine open U of Spec A, its inverse image V is affine by
morphism-affine-schemes-affine. The fibre-product-affine-spectra lemma identifies it with
the spectrum of the base-changed algebra. Faithfully-flat-base-change and
faithfully-flat-surjective-spectrum show V maps onto U. The sole affine open V verifies
the finite-affine-open covering condition of Tag 0989. Weak etaleness follows from
ind-etale-stability, so this singleton is a pro-etale covering. -/
theorem exists_bounded_wContractible_extension (A : Type u) [CommRing A]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧
      Cardinal.mk D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) ∧
      (∀ (B : Type (max u v)) [CommRing B] (g : D →+* B),
        g.FaithfullyFlat → g.WeaklyEtale →
          ∃ r : B →+* D, r.comp g = RingHom.id D) ∧
      Presieve.singleton (Spec.map (CommRingCat.ofHom f)) ∈
        Scheme.proetalePrecoverage (Spec (CommRingCat.of A)) := by
  classical
  let C := PrincipalWLocalization.StrictWCover.algebra A
  obtain ⟨hCfaith, hCind, hCw, hCstrict, _⟩ :=
    PrincipalWLocalization.StrictWCover.properties A
  have : Module.FaithfullyFlat A C := hCfaith
  have : Algebra.IndEtale A C := hCind
  have : IsWLocalRing C := hCw
  have hCsize : Cardinal.mk C ≤ κ := by
    simpa using PrincipalWLocalization.StrictWCover.cardinalMk_le A κ hκ (by simpa using hA)
  obtain ⟨hcompact, ht2, htd, _, hpull⟩ :=
    Algebra.exists_profinite_component_ring_pullback C
  have : CompactSpace (ConnectedComponents (PrimeSpectrum C)) := hcompact
  have : T2Space (ConnectedComponents (PrimeSpectrum C)) := ht2
  have : TotallyDisconnectedSpace (ConnectedComponents (PrimeSpectrum C)) := htd
  let P := Profinite.of (ConnectedComponents (PrimeSpectrum C))
  have hPsize : Cardinal.mk P ≤ (2 : Cardinal.{u}) ^ κ := by
    calc
      Cardinal.mk P ≤ Cardinal.mk (PrimeSpectrum C) :=
        Cardinal.mk_le_of_surjective ConnectedComponents.surjective_coe
      _ ≤ Cardinal.mk (Set C) := Cardinal.mk_le_of_injective
        (f := fun p : PrimeSpectrum C ↦ (p.asIdeal : Set C)) (by
          intro p q h
          exact PrimeSpectrum.ext (SetLike.coe_injective h))
      _ = (2 : Cardinal.{u}) ^ Cardinal.mk C := Cardinal.mk_set
      _ ≤ (2 : Cardinal.{u}) ^ κ := Cardinal.power_le_power_left (by norm_num) hCsize
  have hpow : Cardinal.aleph0 ≤ (2 : Cardinal.{u}) ^ κ :=
    hκ.trans (Cardinal.cantor κ).le
  obtain ⟨T, t, ht, hT, hTsize⟩ :=
    Profinite.exists_bounded_extremallyDisconnected_cover P _ hpow hPsize
  have : ExtremallyDisconnected T := hT
  obtain ⟨D, _, _, e, eπ, _, _, _, _, hind, hlocal, hw,
    hclosedD, hclosedT, hsurj⟩ := hpull T t
  have : IsWLocalRing D := hw
  have : Algebra.IndEtale C D := hind
  have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) :=
    extremallyDisconnected_of_homeo eπ.symm
  have hDstrict : ∀ (m : Ideal D) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    intro m hm
    let q : PrimeSpectrum D := ⟨m, inferInstance⟩
    have hq : q ∈ closedPoints (PrimeSpectrum D) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hm
    rw [hclosedD] at hq
    have hmC : (m.comap (algebraMap C D)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hq
    have := hCstrict (m.comap (algebraMap C D))
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (RingEquiv.ofBijective _ (hlocal q))
  have hCDfaith : (algebraMap C D).FaithfullyFlat := by
    apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    refine ⟨?_, hsurj ht⟩
    have : Algebra.WeaklyEtale C D := inferInstance
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  let : Algebra A D := Algebra.compHom D (algebraMap A C)
  have : IsScalarTower A C D := .of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat C D :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hCDfaith
  have : Module.FaithfullyFlat A D := Module.FaithfullyFlat.trans A C D
  have : Algebra.IndEtale A D := Algebra.IndEtale.trans A C D
  have hcard : Cardinal.mk D ≤
      κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) := by
    let M := closedPoints (PrimeSpectrum D)
    let L := fun m : M ↦ Localization.AtPrime m.val.asIdeal
    let δ : D → ((m : M) → L m) := fun d m ↦ algebraMap D (L m) d
    have hδ : Function.Injective δ := by
      intro x y hxy
      apply sub_eq_zero.mp
      apply eq_zero_of_localization (x - y)
      intro m hm
      let q : PrimeSpectrum D := ⟨m, hm.isPrime⟩
      have hq : q ∈ closedPoints (PrimeSpectrum D) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hm
      have h := congrFun hxy (⟨q, hq⟩ : M)
      simpa only [map_sub, sub_eq_zero] using h
    have hL : ∀ m : M, Cardinal.mk (L m) ≤ κ := by
      intro m
      let q := m.val
      let p := q.asIdeal.comap (algebraMap C D)
      let E := RingEquiv.ofBijective _ (hlocal q)
      calc
        Cardinal.mk (L m) = Cardinal.mk (Localization.AtPrime p) :=
          (Cardinal.mk_congr E.toEquiv).symm
        _ ≤ Cardinal.mk C := IsLocalization.cardinalMk_le p.primeCompl
        _ ≤ κ := hCsize
    have hM : Cardinal.mk M ≤
        (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)) := by
      rw [Cardinal.mk_congr hclosedT.homeomorph.toEquiv]
      exact hTsize
    calc
      Cardinal.mk D ≤ Cardinal.mk ((m : M) → L m) := Cardinal.mk_le_of_injective hδ
      _ = Cardinal.prod (fun m : M ↦ Cardinal.mk (L m)) := Cardinal.mk_pi L
      _ ≤ Cardinal.prod (fun _ : M ↦ κ) := Cardinal.prod_le_prod _ _ hL
      _ = κ ^ Cardinal.mk M := Cardinal.prod_const' M κ
      _ ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) :=
        Cardinal.power_le_power_left (ne_of_gt (Cardinal.aleph0_pos.trans_le hκ)) hM
  refine ⟨D, inferInstance, algebraMap A D,
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance,
    (RingHom.IndEtale.algebraMap_iff (R := A) (S := D)).mpr inferInstance, hcard, ?_, ?_⟩
  · intro B _ g hg hwg
    exact exists_retraction_of_wlocal_geometric_criterion hDstrict g hg hwg
  · have hweak : AlgebraicGeometry.WeaklyEtale
        (Spec.map (CommRingCat.ofHom (algebraMap A D))) := inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A D))) := by
      rw [surjective_iff]
      exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    change Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap A D))) ∈
      Scheme.propQCPrecoverage @AlgebraicGeometry.WeaklyEtale (Spec (CommRingCat.of A))
    exact Scheme.Hom.singleton_mem_propQCPrecoverage hweak

end RingHom
