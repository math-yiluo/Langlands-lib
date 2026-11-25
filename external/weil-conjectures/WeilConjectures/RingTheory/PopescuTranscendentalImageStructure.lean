/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLocalizedPolynomialImage
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

public import Mathlib.RingTheory.Algebraic.Defs

import WeilConjectures.RingTheory.FlatAndFlatOfFlatFibreNoetherian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Artinian and flat structure of the localized transcendental image

Source: Stacks Project, Tags 07FH and 07FI, transcendental case.
(blueprint: lem-weil-pbc-popescu-transcendental-image-structure).
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra

private theorem polynomialPrime_eq
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B] [IsLocalRing B]
    (A₀ : Subalgebra k B) [IsLocalRing A₀] (x : B)
    [Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    (hmap : ∀ c : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) (IsLocalRing.residue A₀ c) =
        IsLocalRing.residue B (c : B))
    (hα : Transcendental (IsLocalRing.ResidueField A₀) (IsLocalRing.residue B x)) :
    popescuPolynomialPrime A₀ x =
      (IsLocalRing.maximalIdeal A₀).map Polynomial.C := by
  have heval : (IsLocalRing.residue B).comp (popescuPolynomialEval A₀ x).toRingHom =
      (Polynomial.aeval (IsLocalRing.residue B x)).toRingHom.comp
        (Polynomial.mapRingHom (IsLocalRing.residue A₀)) := by
    ext c <;> simp [popescuPolynomialEval, hmap]
  change (IsLocalRing.maximalIdeal B).comap (popescuPolynomialEval A₀ x).toRingHom = _
  rw [← IsLocalRing.ker_residue, RingHom.comap_ker, heval,
    RingHom.ker_comp_of_injective _ (_root_.transcendental_iff_injective.mp hα),
    Polynomial.ker_mapRingHom, IsLocalRing.ker_residue]

private theorem image_artinian_and_maximalIdeal
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B] [IsLocalRing B]
    (A₀ : Subalgebra k B) [IsLocalRing A₀] [IsArtinianRing A₀] (x : B)
    (hmax : (IsLocalRing.maximalIdeal A₀).map A₀.val.toRingHom =
      IsLocalRing.maximalIdeal B)
    (hprime : popescuPolynomialPrime A₀ x =
      (IsLocalRing.maximalIdeal A₀).map Polynomial.C) :
    IsArtinianRing (popescuLocalizedPolynomialImage A₀ x) ∧
      (IsLocalRing.maximalIdeal (popescuLocalizedPolynomialImage A₀ x)).map
        (popescuLocalizedPolynomialImage A₀ x).val.toRingHom =
          IsLocalRing.maximalIdeal B := by
  let A := popescuLocalizedPolynomialImage A₀ x
  let D := Localization.AtPrime (popescuPolynomialPrime A₀ x)
  let g : D →ₐ[k] A := (popescuLocalizedPolynomialMap A₀ x).rangeRestrict
  let c : A₀ →+* D := (algebraMap (Polynomial A₀) D).comp Polynomial.C
  have hDmax : IsLocalRing.maximalIdeal D = (IsLocalRing.maximalIdeal A₀).map c := by
    calc
      IsLocalRing.maximalIdeal D = (popescuPolynomialPrime A₀ x).map
          (algebraMap (Polynomial A₀) D) := Localization.AtPrime.map_eq_maximalIdeal.symm
      _ = ((IsLocalRing.maximalIdeal A₀).map Polynomial.C).map
          (algebraMap (Polynomial A₀) D) :=
        congrArg (Ideal.map (algebraMap (Polynomial A₀) D)) hprime
      _ = _ := Ideal.map_map Polynomial.C (algebraMap (Polynomial A₀) D)
  have : IsArtinianRing D := by
    apply (isArtinianRing_iff_isNilpotent_maximalIdeal D).mpr
    rw [hDmax]
    exact ((isArtinianRing_iff_isNilpotent_maximalIdeal A₀).mp inferInstance).map
      (Ideal.mapHom c)
  have hAart : IsArtinianRing A := by
    let := g.toRingHom.toAlgebra
    have : IsArtinian D A := isArtinian_of_surjective D (Algebra.linearMap D A)
      (popescuLocalizedPolynomialMap A₀ x).rangeRestrict_surjective
    exact isArtinian_of_tower D (M := A) inferInstance
  refine ⟨hAart, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective g.toRingHom
    (popescuLocalizedPolynomialMap A₀ x).rangeRestrict_surjective, hDmax,
    Ideal.map_map, Ideal.map_map]
  convert hmax using 1
  congr 1
  ext a
  exact (popescuLocalizedPolynomialMap_algebraMap A₀ x _).trans
    (Polynomial.aevalTower_C A₀.val x a)

private theorem localHom_of_artinian
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S] [IsArtinianRing R] [IsLocalRing R]
    (f : R →+* S) : IsLocalHom f :=
  ⟨fun b hb ↦ by
    by_contra hn
    have hnil : IsNilpotent b :=
      Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hn
    exact (hnil.map f).not_isUnit hb⟩

/-- The explicit localized polynomial image has the Artinian and flat parts of admissibility.
Source: Stacks Project, Tag 07FI, transcendental case, and Tag 07FH.

Proof: Put θ = evaluation at x and n = θ⁻¹(m_B). On residues θ is evaluation
F₀[T] → K at the transcendental residue of x; it is injective. Thus n = m₀[T].
The localization D = A₀[T]_n is Noetherian, its maximal ideal is m₀D, and this
ideal is nilpotent since A₀ is Artinian. Therefore D is Artinian local.
The map D → B is local. Apply the Noetherian fibre flatness criterion to
A₀ → D → B and M = B. The module B is flat over A₀ by admissibility, and
B/m₀B is a vector space over D/m₀D = F₀(T), hence flat. Thus D → B is flat.
It is faithfully flat because it is local, hence injective. Its image is
isomorphic to D, so is Artinian and flatly included in B. The maximal ideal
of that image is the image of m₀D; extending it to B gives m₀B = m_B.
(blueprint: lem-weil-pbc-popescu-transcendental-image-structure). -/
theorem popescu_transcendental_image_structure
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [IsArtinianRing B] [IsLocalRing B]
    (A₀ : Subalgebra k B) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible (IsLocalRing.maximalIdeal B))
    (x : B) [IsLocalHom A₀.val]
    [Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    [IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    (hmap : ∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) (IsLocalRing.residue A₀ a₀) =
        IsLocalRing.residue B (a₀ : B))
    (hα : Transcendental (IsLocalRing.ResidueField A₀) (IsLocalRing.residue B x)) :
    IsArtinianRing (popescuLocalizedPolynomialImage A₀ x) ∧
      (popescuLocalizedPolynomialImage A₀ x).val.toRingHom.Flat ∧
      (IsLocalRing.maximalIdeal (popescuLocalizedPolynomialImage A₀ x)).map
        (popescuLocalizedPolynomialImage A₀ x).val.toRingHom =
          IsLocalRing.maximalIdeal B := by
  classical
  have : IsArtinianRing A₀ := hA₀.1
  obtain ⟨_, hflat₀, hmax₀⟩ := hA₀.2.2
  let A := popescuLocalizedPolynomialImage A₀ x
  let D := Localization.AtPrime (popescuPolynomialPrime A₀ x)
  let g : D →ₐ[k] A := (popescuLocalizedPolynomialMap A₀ x).rangeRestrict
  let φ : D →ₐ[k] B := popescuLocalizedPolynomialMap A₀ x
  have hprime := polynomialPrime_eq A₀ x hmap hα
  have hstructure := image_artinian_and_maximalIdeal A₀ x hmax₀ hprime
  let c : A₀ →+* D := (algebraMap (Polynomial A₀) D).comp Polynomial.C
  have hDmax : IsLocalRing.maximalIdeal D = (IsLocalRing.maximalIdeal A₀).map c := by
    calc
      IsLocalRing.maximalIdeal D = (popescuPolynomialPrime A₀ x).map
          (algebraMap (Polynomial A₀) D) := Localization.AtPrime.map_eq_maximalIdeal.symm
      _ = ((IsLocalRing.maximalIdeal A₀).map Polynomial.C).map
          (algebraMap (Polynomial A₀) D) :=
        congrArg (Ideal.map (algebraMap (Polynomial A₀) D)) hprime
      _ = _ := Ideal.map_map Polynomial.C (algebraMap (Polynomial A₀) D)
  have : IsArtinianRing D := by
    apply (isArtinianRing_iff_isNilpotent_maximalIdeal D).mpr
    rw [hDmax]
    exact ((isArtinianRing_iff_isNilpotent_maximalIdeal A₀).mp inferInstance).map
      (Ideal.mapHom c)
  let : Algebra D B := φ.toRingHom.toAlgebra
  have : IsScalarTower A₀ D B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact ((popescuLocalizedPolynomialMap_algebraMap A₀ x _).trans
      (Polynomial.aevalTower_C A₀.val x a)).symm)
  have : IsLocalHom (algebraMap A₀ D) := localHom_of_artinian _
  have : IsLocalHom (algebraMap D B) := localHom_of_artinian _
  change (algebraMap A₀ B).Flat at hflat₀
  have : Module.Flat A₀ B := RingHom.flat_algebraMap_iff.mp hflat₀
  have hI : (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ D) =
      IsLocalRing.maximalIdeal D := hDmax.symm
  have : ((IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ D)).IsMaximal := by
    rw [hI]
    infer_instance
  let := Ideal.Quotient.field ((IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ D))
  have hfibre : Module.Flat
      (D ⧸ (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ D))
      (_root_.TensorProduct D
        (D ⧸ (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ D)) B) := by
    have : Module.Free (D ⧸ (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ D))
        (_root_.TensorProduct D
          (D ⧸ (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ D)) B) :=
      Module.Free.of_divisionRing _ _
    exact Module.Flat.of_free
  have : Module.Flat D B :=
    (Module.flat_and_flat_of_flat_fibre_noetherian A₀ D B B hfibre).2
  have : Module.FaithfullyFlat D B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hφinj : Function.Injective φ := FaithfulSMul.algebraMap_injective D B
  have hginj : Function.Injective g := by
    intro a b hab
    apply hφinj
    exact congrArg Subtype.val hab
  let e : D ≃+* A := RingEquiv.ofBijective g.toRingHom
    ⟨hginj, (popescuLocalizedPolynomialMap A₀ x).rangeRestrict_surjective⟩
  have hcomp : φ.toRingHom.comp e.symm.toRingHom = A.val.toRingHom := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply a)
  have hφflat : φ.toRingHom.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflat := (RingHom.Flat.of_bijective (f := e.symm.toRingHom) e.symm.bijective).comp hφflat
  rw [hcomp] at hflat
  exact ⟨hstructure.1, hflat, hstructure.2⟩

end Algebra
