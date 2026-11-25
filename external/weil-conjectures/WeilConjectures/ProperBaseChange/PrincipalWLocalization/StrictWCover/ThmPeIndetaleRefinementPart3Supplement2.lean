/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.StrictWCover.ThmPeIndetaleRefinementPart3Supplement
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart2Supplement
import WeilConjectures.RingTheory.ProperBaseChange.ThmPeIndetaleRefinementPart1Supplement
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart3
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale

/-! # Properties of the strict w-local cover

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1229;
Stacks Project, Tag 097X, first paragraph of proof, properties (1), (3), (7), (9)
(blueprint: theorem-existence-contractible-covers--1).
-/

@[expose] public section

universe u

namespace PrincipalWLocalization.StrictWCover

/-- A principal ind-Zariski presentation is an ind-etale presentation: principal
localizations and their finite products are etale, and etaleness respects algebra equivalences.
Source: the definitions in `IndPrincipalZariski` and Mathlib's etale-localization API. -/
private theorem indEtale_of_principal (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (h : Algebra.IsIndPrincipalZariski R S) : Algebra.IndEtale R S := by
  obtain ⟨I, hI, hF, P, hP⟩ := h
  let := hI
  let := hF
  refine ⟨I, hI, hF, P, ?_⟩
  intro i
  obtain ⟨n, f, ⟨e⟩⟩ := hP i
  have (j : Fin n) : Algebra.Etale R (Localization.Away (f j)) :=
    Algebra.Etale.of_isLocalizationAway (f j)
  exact Algebra.Etale.of_equiv e.symm

/-- A prime over a maximal ideal under an ind-etale map is maximal. Map its quotient
into its fraction field. The ind-etale local-field image lemma makes every image separable,
hence integral over the base quotient field. Injectivity reflects integrality, so the domain
quotient is integral over a field and is itself a field.
Source: Stacks 097X, first proof paragraph; the source library's
`Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing`. -/
private theorem maximal_of_indEtale (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IndEtale R S] (q : Ideal S) [q.IsPrime]
    (hm : (q.comap (algebraMap R S)).IsMaximal) : q.IsMaximal := by
  let m := q.comap (algebraMap R S)
  have : m.IsMaximal := hm
  let k := R ⧸ m
  let : Field k := Ideal.Quotient.field m
  let B := S ⧸ q
  let : Algebra k B := Ideal.Quotient.algebraQuotientOfLEComap le_rfl
  let : Algebra k q.ResidueField :=
    ((algebraMap B q.ResidueField).comp (algebraMap k B)).toAlgebra
  have : IsScalarTower k B q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R k B := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  have : IsScalarTower R k q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R k B, ← IsScalarTower.algebraMap_eq R B q.ResidueField]
  let φ : B →ₐ[k] q.ResidueField := IsScalarTower.toAlgHom k B q.ResidueField
  have hφ : Function.Injective φ := q.injective_algebraMap_quotient_residueField
  have : Algebra.IsIntegral k B := ⟨fun b ↦ by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply (isIntegral_algHom_iff φ hφ).mp
    exact (Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing k q.ResidueField
      (IsScalarTower.toAlgHom R S q.ResidueField) s).isIntegral⟩
  apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient q).mpr
  exact isField_of_isIntegral_of_isField' (Field.toIsField k)

/-- The specified strict w-local cover is faithfully flat and ind-etale over its base,
its spectrum is w-local, its maximal local rings are strictly henselian, and its closed
points map onto the whole base spectrum.
Source: blueprint order 1229; Stacks Project, Tag 097X, first proof paragraph
(blueprint: theorem-existence-contractible-covers--1).

Proof: Put W = A^w, E = W^e, I the closed-point ideal of W, and T = V(IE).
The point description of `PrincipalWLocalization.points` shows that V(I) consists of
closed points and maps onto Spec A, since the diagonal pair (x,x) maps to x.
The etale-contraction properties make W -> E faithfully flat and ind-etale, with strictly
henselian maximal local rings. A prime q in T contracts to a maximal ideal m of W.
Map E/q into its fraction field, with scalars W/m. The source-library lemma
`Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing` makes each image of E separable
over W/m, hence integral. Integrality reflects along the injective fraction-field map.
Thus the domain E/q is integral over the field W/m, so is itself a field and q is maximal.
Apply retained-localization properties to this closed set of closed points:
C_A is w-local, with closed points T and unchanged local rings E_q there. Transfer
henselianity along these local-ring isomorphisms by unique lifting of residue idempotents
in finite algebras, and transfer separable closedness by the residue-field isomorphism.
For every x in Spec A choose a closed point m of W above it. Faithful flatness of E/W
gives a prime q above m; it contains IE and belongs to T. The retained closed point (q,q)
therefore maps to x. Finally A -> W and E -> C_A are ind-Zariski, hence ind-etale.
The source library's ind-etale composition lemma makes the composite ind-etale;
its weak-etaleness instance gives flatness.
The closed-point surjectivity just proved implies spectrum surjectivity, so the flat
surjective-spectrum criterion gives faithful flatness. -/
theorem properties (A : Type u) [CommRing A] :
    Module.FaithfullyFlat A (algebra A) ∧
    Algebra.IndEtale A (algebra A) ∧
    IsWLocalRing (algebra A) ∧
    (∀ (m : Ideal (algebra A)) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m)) ∧
    Function.Surjective
      (fun q : closedPoints (PrimeSpectrum (algebra A)) ↦
        PrimeSpectrum.comap (algebraMap A (algebra A)) q.val) := by
  classical
  let W := PrincipalWLocalization.algebra A
  let E := contraction A
  let f : W →+* E := contractionMap A
  let : Algebra W E := f.toAlgebra
  have hf := CommRingCat.etaleContraction_properties (CommRingCat.of W)
  have hfe : f.IndEtale := hf.2.1
  have : Algebra.IndEtale W E := hfe
  obtain ⟨ew, hew, _, _, _, _, _, hwclosed, ⟨hw, hhw⟩, _, _⟩ :=
    PrincipalWLocalization.points A
  have hclosedIdeal : PrimeSpectrum.zeroLocus (closedIdeal A : Set W) =
      closedPoints (PrimeSpectrum W) := by
    rw [closedIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hwclosed.closure_eq]
  let T := PrimeSpectrum.zeroLocus (extendedIdeal A : Set E)
  have hT (q : PrimeSpectrum E) (hq : q ∈ T) : IsClosed ({q} : Set (PrimeSpectrum E)) := by
    have hq' : extendedIdeal A ≤ q.asIdeal := hq
    have hm : PrimeSpectrum.comap f q ∈ closedPoints (PrimeSpectrum W) := by
      rw [← hclosedIdeal]
      exact (Ideal.map_le_iff_le_comap).mp hq'
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr
    apply maximal_of_indEtale W E q.asIdeal
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (mem_closedPoints_iff.mp hm)
  let : TopologicalSpace T :=
    TopologicalSpace.induced Subtype.val (constructibleTopology (PrimeSpectrum E))
  obtain ⟨hiz, ⟨ec, hlocal, hret⟩, _⟩ :=
    Retained.properties T (PrimeSpectrum.isClosed_zeroLocus _)
  obtain ⟨hwlocal, ⟨hc, hhc⟩⟩ := hret hT
  have hstrict (m : Ideal (algebra A)) [m.IsMaximal] :
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    let z : closedPoints (PrimeSpectrum (algebra A)) :=
      ⟨⟨m, inferInstance⟩, mem_closedPoints_iff.mpr
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr inferInstance)⟩
    let x := hc.toEquiv.symm z
    have hpair : (ec z.val).val = (x.val, x.val) := by
      simpa [x] using hhc x
    obtain ⟨hm, hbij⟩ := hlocal z.val
    have : (ec z.val).val.2.asIdeal.IsMaximal := by
      rw [hpair]
      exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp (hT x.val x.property)
    have : IsStrictlyHenselianLocalRing
        (Localization.AtPrime (ec z.val).val.2.asIdeal) := hf.2.2.2 _
    exact IsStrictlyHenselianLocalRing.of_ringEquiv (RingEquiv.ofBijective _ hbij)
  have hsurj : Function.Surjective
      (fun q : closedPoints (PrimeSpectrum (algebra A)) ↦
        PrimeSpectrum.comap (algebraMap A (algebra A)) q.val) := by
    intro x
    let m := (hw x).val
    have hm : PrimeSpectrum.comap (algebraMap A W) m = x := by
      rw [hew]
      exact congrArg Prod.snd (hhw x)
    obtain ⟨q, hqm⟩ : ∃ q : PrimeSpectrum E, PrimeSpectrum.comap f q = m :=
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hf.1).2 m
    have hqT : q ∈ T := by
      change extendedIdeal A ≤ q.asIdeal
      apply Ideal.map_le_iff_le_comap.mpr
      change closedIdeal A ≤ (PrimeSpectrum.comap f q).asIdeal
      rw [hqm]
      have hmclosed : m ∈ closedPoints (PrimeSpectrum W) := (hw x).property
      change m ∈ PrimeSpectrum.zeroLocus (closedIdeal A : Set W)
      rw [hclosedIdeal]
      exact hmclosed
    let y : T := ⟨q, hqT⟩
    refine ⟨hc y, ?_⟩
    obtain ⟨hy, _⟩ := hlocal (hc y).val
    have hcomp : PrimeSpectrum.comap (Retained.structuralMap T
        (PrimeSpectrum.isClosed_zeroLocus _)) (hc y).val = q := by
      apply PrimeSpectrum.ext
      change (hc y).val.asIdeal.comap _ = q.asIdeal
      rw [← hy]
      exact congrArg (fun p : PrimeSpectrum E × PrimeSpectrum E ↦ p.2.asIdeal) (hhc y)
    change PrimeSpectrum.comap (structuralMap A) (hc y).val = x
    change PrimeSpectrum.comap ((Retained.structuralMap T
      (PrimeSpectrum.isClosed_zeroLocus _)).comp
        (f.comp (algebraMap A W))) (hc y).val = x
    rw [PrimeSpectrum.comap_comp_apply, hcomp, PrimeSpectrum.comap_comp_apply, hqm, hm]
  have hwe : (algebraMap A W).IndEtale :=
    (RingHom.IndEtale.algebraMap_iff A W).mpr
      (indEtale_of_principal A W (PrincipalWLocalization.isIndPrincipalZariski (A := A)))
  have hec : (Retained.structuralMap T (PrimeSpectrum.isClosed_zeroLocus _)).IndEtale :=
    @indEtale_of_principal E _ _ _
      (Retained.structuralMap T (PrimeSpectrum.isClosed_zeroLocus _)).toAlgebra hiz
  have hie : Algebra.IndEtale A (algebra A) := by
    apply (RingHom.IndEtale.algebraMap_iff A (algebra A)).mp
    change ((Retained.structuralMap T (PrimeSpectrum.isClosed_zeroLocus _)).comp
      (f.comp (algebraMap A W))).IndEtale
    exact hec.comp (hfe.comp hwe)
  have : Algebra.IndEtale A (algebra A) := hie
  have hff : Module.FaithfullyFlat A (algebra A) :=
    Module.FaithfullyFlat.of_comap_surjective fun x ↦ by
      obtain ⟨q, hq⟩ := hsurj x
      exact ⟨q.val, hq⟩
  exact ⟨hff, hie, hwlocal, hstrict, hsurj⟩

end PrincipalWLocalization.StrictWCover
