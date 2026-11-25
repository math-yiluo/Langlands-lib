/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.HopkinsLevitzki
import WeilConjectures.RingTheory.FlatPermanence

/-!
# The étale map into an adapted Artinian subalgebra

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FH, after property (1).
(blueprint: lem-weil-pbc-popescu-etale-quotient-map).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

private theorem flat_quotient_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (I : Ideal R) (J : Ideal S)
    (hJ : I.map f = J) :
    (Ideal.quotientMap J f (hJ ▸ Ideal.le_comap_map)).Flat := by
  subst J
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  change (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv


/-- A fixed flat polynomial localization with adapted residue differentials induces an
étale map from its prime-power quotient into the admissible subalgebra. Unlike the original
existence theorem, this makes no choice of polynomial coordinates and assumes their flatness.
Source: Stacks Tag 07FH, construction of the factorization and its étaleness.
(blueprint: lem-weil-pbc-popescu-etale-quotient-map).

Proof: The polynomial evaluation into the ambient quotient has all variable images in A;
its coefficient images lie there because A is a k-subalgebra. Hence it factors through A.
Every polynomial outside p maps outside the ambient maximal ideal and thus outside m_A by
the contraction hypothesis. Such images are units in A, so extend evaluation to P by the
localization universal property. Its composite with the inclusion A → B agrees with the
quotient of ψ by uniqueness of localization maps. Since pΛ_q = qΛ_q, this composite kills
p^nP. The inclusion is injective, so the map into A also kills p^nP, giving f : P/p^nP → A
and the displayed compatibility. This map is local, since all elements of p map
into m_A. The quotient map P/p^nP → B is the base change of the flat ψ and therefore flat.
The inclusion A → B is flat local, hence faithfully flat. Flatness descends to f by 0584.
The extension of pA to B equals qB, which also equals the extension of m_A; faithful flat
ideal contraction gives pA = m_A. The induced field extension F/κ(p) is finitely generated,
since A is essentially of finite type over k. The surjection Ω(F/k) → Ω(F/κ(p)) kills the
differentials of all the coordinate residues, which span by hypothesis, so the latter is
zero. By the finitely generated field criterion (Algebra 090W) the
field extension is finite separable. Since A is Artinian, finite residue
extension and pA = m_A imply that A is finite over P/p^nP by the Artinian
finite-over-residue-finite lemma. The base is Noetherian,
so A is finitely presented. Finally the flat local criterion 00U6, with pA = m_A and finite
separable residue extension, gives étaleness at the maximal ideal. Since A is Artinian local,
this is its only prime, so the map is étale. This proves the statement without any geometric
regularity or characteristic hypothesis. -/
theorem exists_etale_popescu_quotient_map
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (A : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) [IsLocalRing A]
    (hA : A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (hAm : IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom
      ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q)
    (hψ : ψ.comp (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom)
    (hideal : q.map (algebraMap Λ (Localization.AtPrime q)) =
      (q.comap φ.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom))
    (hflat : ψ.Flat) (a : Fin m → A)
    (ha : ∀ j, (a j : Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
      Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) (φ (MvPolynomial.X j))))
    (hspan : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun j ↦ KaehlerDifferential.D k (IsLocalRing.ResidueField A)
        (IsLocalRing.residue A (a j)))) = ⊤) :
    ∃ f : (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) →+* A,
      IsLocalHom f ∧
      (letI := f.toAlgebra
       Etale (Localization.AtPrime (q.comap φ.toRingHom) ⧸
         ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
           (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) A) ∧
      (A.val.toRingHom.comp f).comp
        (Ideal.Quotient.mk ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom))) ^ n)) =
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)).comp ψ := by
  classical
  let R := MvPolynomial (Fin m) k
  let p : Ideal R := q.comap φ.toRingHom
  let P := Localization.AtPrime p
  let L := Localization.AtPrime q
  let J : Ideal L := q.map (algebraMap Λ L)
  let I : Ideal P := p.map (algebraMap R P)
  let B := L ⧸ J ^ n
  let π : L →+* B := Ideal.Quotient.mk (J ^ n)
  let g : R →ₐ[k] A := MvPolynomial.aeval a
  have heval : A.val.comp g =
      (Ideal.Quotient.mkₐ k (J ^ n)).comp ((IsScalarTower.toAlgHom k Λ L).comp φ) := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa [g, π, J, L] using ha j
  have heval' : A.val.toRingHom.comp g.toRingHom =
      π.comp ((algebraMap Λ L).comp φ.toRingHom) :=
    congrArg AlgHom.toRingHom heval
  have hJ : J = IsLocalRing.maximalIdeal L := Localization.AtPrime.map_eq_maximalIdeal
  have hpow : J ^ n ≤ J := Ideal.pow_le_self (by omega)
  have hunit : ∀ s : p.primeCompl, IsUnit (g s) := by
    intro s
    by_contra hs
    have hsA : g s ∈ IsLocalRing.maximalIdeal A := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hs
    rw [hAm] at hsA
    change A.val (g s) ∈ J.map π at hsA
    have hgs : A.val (g s) = π (algebraMap Λ L (φ s)) :=
      RingHom.congr_fun heval' s
    rw [hgs] at hsA
    have hsL : algebraMap Λ L (φ s) ∈ J := by
      change algebraMap Λ L (φ s) ∈ (J.map π).comap π at hsA
      simpa only [π, Ideal.comap_map_mk hpow] using hsA
    have hsq : φ s ∈ q := by
      rw [hJ] at hsL
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q _).mp hsL
    exact s.property hsq
  let e : P →+* A := IsLocalization.lift hunit
  have he : A.val.toRingHom.comp e = π.comp ψ := by
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [RingHom.comp_assoc, IsLocalization.lift_comp, RingHom.comp_assoc, hψ]
    exact heval'
  have hmap : I.map ψ = J := by
    rw [Ideal.map_map, hψ]
    exact hideal.symm
  have hkill : I ^ n ≤ RingHom.ker e := by
    intro x hx
    apply RingHom.mem_ker.mpr
    apply Subtype.val_injective
    change (A.val.toRingHom.comp e) x = 0
    rw [he]
    change π (ψ x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem ψ hx
  let f : (P ⧸ I ^ n) →+* A := Ideal.Quotient.lift (I ^ n) e hkill
  have hf : (A.val.toRingHom.comp f).comp (Ideal.Quotient.mk (I ^ n)) = π.comp ψ := by
    calc
      _ = A.val.toRingHom.comp e := by ext x; rfl
      _ = π.comp ψ := he
  have heLocal : IsLocalHom e := by
    apply ((IsLocalRing.local_hom_TFAE e).out 3 1).mp
    change (IsLocalRing.maximalIdeal P).map e ≤ IsLocalRing.maximalIdeal A
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change e (algebraMap R P x) ∈ IsLocalRing.maximalIdeal A
    rw [IsLocalization.lift_eq, hAm]
    change A.val (g x) ∈ J.map π
    have hgx : A.val (g x) = π (algebraMap Λ L (φ x)) := RingHom.congr_fun heval' x
    rw [hgx]
    apply Ideal.mem_map_of_mem
    exact Ideal.mem_map_of_mem _ hx
  have hfLocal : IsLocalHom f := by
    constructor
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (isUnit_of_map_unit e r hx).map (Ideal.Quotient.mk (I ^ n))
  let Q := P ⧸ I ^ n
  have hI : I = IsLocalRing.maximalIdeal P := Localization.AtPrime.map_eq_maximalIdeal
  have hIpow : I ^ n ≤ I := Ideal.pow_le_self (by omega)
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (hI ▸ IsLocalRing.maximalIdeal.isMaximal P).ne_top hIpow)
  have : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (hJ ▸ IsLocalRing.maximalIdeal.isMaximal L).ne_top hpow)
  have : IsLocalRing B := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  have hQm : IsLocalRing.maximalIdeal Q = I.map (Ideal.Quotient.mk (I ^ n)) := by
    calc
      _ = (IsLocalRing.maximalIdeal P).map (Ideal.Quotient.mk (I ^ n)) :=
        (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
      _ = _ := congrArg (Ideal.map (Ideal.Quotient.mk (I ^ n))) hI.symm
  have hBm : IsLocalRing.maximalIdeal B = J.map π := by
    calc
      _ = (IsLocalRing.maximalIdeal L).map π :=
        (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
      _ = _ := congrArg (Ideal.map π) hJ.symm
  have : IsLocalHom A.val.toRingHom := by
    apply ((IsLocalRing.local_hom_TFAE A.val.toRingHom).out 5 1).mp
    rw [hBm]
    exact hAm.symm
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom A.val.toRingHom›
  have hAB : Module.Flat A B := hA.2.2.choose_spec.1
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hmax : (IsLocalRing.maximalIdeal Q).map f = IsLocalRing.maximalIdeal A := by
    have heq : ((IsLocalRing.maximalIdeal Q).map f).map A.val.toRingHom =
        (IsLocalRing.maximalIdeal A).map A.val.toRingHom := by
      calc
        _ = (I.map ψ).map π := by
          rw [hQm, Ideal.map_map, Ideal.map_map, hf]
          simp only [Ideal.map_map, RingHom.comp_assoc, I]
        _ = J.map π := congrArg (Ideal.map π) hmap
        _ = _ := hA.2.2.choose_spec.2.symm
    have hc := congrArg (Ideal.comap A.val.toRingHom) heq
    exact (Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) _).symm.trans
      (hc.trans (Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) _))
  have hbase : (I ^ n).map ψ = J ^ n := by rw [Ideal.map_pow, hmap]
  let β : Q →+* B := Ideal.quotientMap (J ^ n) ψ (hbase ▸ Ideal.le_comap_map)
  have hβ : A.val.toRingHom.comp f = β := by
    apply Ideal.Quotient.ringHom_ext
    exact hf
  have hβflat : (A.val.toRingHom.comp f).Flat := by
    rw [hβ]
    exact flat_quotient_map ψ hflat (I ^ n) (J ^ n) hbase
  have hfflat : f.Flat :=
    RingHom.flat_of_flat_module_of_faithfullyFlat_module (M := B) f hβflat
  refine ⟨f, hfLocal, ?_, hf⟩
  let : Algebra Q A := f.toAlgebra
  have : Module.Flat Q A := hfflat
  have : IsLocalHom (algebraMap Q A) := hfLocal
  have : IsScalarTower k Q A := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap k A r =
      f (Ideal.Quotient.mk (I ^ n) (algebraMap R P (MvPolynomial.C r)))
    change algebraMap k A r = (Ideal.Quotient.lift (I ^ n) e hkill)
      (Ideal.Quotient.mk (I ^ n) (algebraMap R P (MvPolynomial.C r)))
    rw [Ideal.Quotient.lift_mk]
    change algebraMap k A r = IsLocalization.lift hunit
      (algebraMap R P (MvPolynomial.C r))
    rw [IsLocalization.lift_eq]
    exact (g.commutes r).symm
  have hcoord (j : Fin m) : f (algebraMap R Q (MvPolynomial.X j)) = a j := by
    change f (Ideal.Quotient.mk (I ^ n) (algebraMap R P (MvPolynomial.X j))) = a j
    change (Ideal.Quotient.lift (I ^ n) e hkill)
      (Ideal.Quotient.mk (I ^ n) (algebraMap R P (MvPolynomial.X j))) = a j
    rw [Ideal.Quotient.lift_mk]
    change IsLocalization.lift hunit (algebraMap R P (MvPolynomial.X j)) = a j
    rw [IsLocalization.lift_eq]
    exact MvPolynomial.aeval_X a j
  let F := IsLocalRing.ResidueField A
  have : EssFiniteType k A := hA.2.1
  have : EssFiniteType Q A := EssFiniteType.of_comp k Q A
  have : EssFiniteType k F := EssFiniteType.comp k A F
  have : EssFiniteType Q F := EssFiniteType.of_comp k Q F
  have hker : Submodule.span F (Set.range (fun j ↦ KaehlerDifferential.D k F
      (IsLocalRing.residue A (a j)))) ≤
      LinearMap.ker (KaehlerDifferential.map k Q F F) := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    change KaehlerDifferential.map k Q F F (KaehlerDifferential.D k F
      (IsLocalRing.residue A (a j))) = 0
    rw [KaehlerDifferential.map_D]
    change KaehlerDifferential.D Q F (IsLocalRing.residue A (a j)) = 0
    rw [← hcoord j]
    change KaehlerDifferential.D Q F
      (algebraMap A F (algebraMap Q A (algebraMap R Q (MvPolynomial.X j)))) = 0
    rw [← IsScalarTower.algebraMap_apply]
    exact Derivation.map_algebraMap _ _
  have : FormallyUnramified Q F := by
    constructor
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective k Q F x
    exact hker (hspan.symm ▸ Submodule.mem_top)
  have : FormallyUnramified (IsLocalRing.ResidueField Q) F :=
    FormallyUnramified.of_restrictScalars Q (IsLocalRing.ResidueField Q) F
  have : EssFiniteType (IsLocalRing.ResidueField Q) F :=
    EssFiniteType.of_comp Q (IsLocalRing.ResidueField Q) F
  have : Algebra.IsSeparable (IsLocalRing.ResidueField Q) F :=
    FormallyUnramified.isSeparable _ _
  have : FormallyUnramified Q A := FormallyUnramified.of_map_maximalIdeal hmax
  have : Module.Finite (IsLocalRing.ResidueField Q) F :=
    FormallyUnramified.finite_of_free _ _
  have : Module.Finite Q F := Module.Finite.trans (IsLocalRing.ResidueField Q) F
  have hjac : Ring.jacobson A = IsLocalRing.maximalIdeal A := by
    rw [← Ideal.jacobson_bot]
    exact IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top
  have : Module.Finite Q (A ⧸ Ring.jacobson A) := by
    rw [hjac]
    exact ‹Module.Finite Q F›
  have : IsArtinianRing A := hA.1
  have : Module.Finite Q A := IsSemiprimaryRing.finite_of_isArtinian Q A A
  have : FiniteType Q A := inferInstance
  have : IsNoetherianRing R := inferInstance
  have : IsNoetherianRing P := inferInstance
  have : IsNoetherianRing Q := inferInstance
  have : FinitePresentation Q A := FinitePresentation.of_finiteType.mp inferInstance
  exact Etale.of_formallyUnramified_of_flat

end Algebra
