/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Local rings as directed colimits of essentially finite type rings

Source: Stacks Project, Tag 00QU, proof (construction of the base-ring system).
(blueprint: lemma-quasi-finite-coordinates--1)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

-- Index by the finitely generated subalgebras rather than their finite generating sets.
private abbrev LocalIndex (R : Type u) [CommRing R] :=
  {A : Subalgebra ℤ R // A.FG}

private abbrev localPrime {R : Type u} [CommRing R] [IsLocalRing R]
    (A : LocalIndex R) : Ideal A.1 :=
  (IsLocalRing.maximalIdeal R).comap A.1.val.toRingHom

private abbrev LocalStage {R : Type u} [CommRing R] [IsLocalRing R]
    (A : LocalIndex R) := Localization.AtPrime (localPrime A)

private noncomputable def localTransition {R : Type u} [CommRing R] [IsLocalRing R]
    {A B : LocalIndex R} (h : A ≤ B) : LocalStage A →+* LocalStage B :=
  Localization.localRingHom (localPrime A) (localPrime B)
    (Subalgebra.inclusion h).toRingHom (by ext x; rfl)

private lemma localTransition_algebraMap {R : Type u} [CommRing R] [IsLocalRing R]
    {A B : LocalIndex R} (h : A ≤ B) (x : A.1) :
    localTransition h (algebraMap A.1 (LocalStage A) x) =
      algebraMap B.1 (LocalStage B) (Subalgebra.inclusion h x) :=
  Localization.localRingHom_to_map _ _ _ _ x

private noncomputable abbrev localDiagram (R : Type u) [CommRing R] [IsLocalRing R] :
    LocalIndex R ⥤ CommRingCat.{u} where
  obj A := .of (LocalStage A)
  map f := ofHom (localTransition (leOfHom f))
  map_id A := by
    ext1
    apply IsLocalization.ringHom_ext (localPrime A).primeCompl
    ext x
    change localTransition le_rfl (algebraMap A.1 (LocalStage A) x) =
      algebraMap A.1 (LocalStage A) x
    exact localTransition_algebraMap le_rfl x
  map_comp {A B C} f g := by
    ext1
    apply IsLocalization.ringHom_ext (localPrime A).primeCompl
    ext x
    change localTransition (leOfHom (f ≫ g)) (algebraMap A.1 (LocalStage A) x) =
      localTransition (leOfHom g)
        (localTransition (leOfHom f) (algebraMap A.1 (LocalStage A) x))
    simp only [localTransition_algebraMap]
    rfl

private lemma localDenominator_unit {R : Type u} [CommRing R] [IsLocalRing R]
    (A : LocalIndex R) (s : (localPrime A).primeCompl) : IsUnit (A.1.val s) :=
  (IsLocalRing.notMem_maximalIdeal).mp s.2

private noncomputable def localToRing {R : Type u} [CommRing R] [IsLocalRing R]
    (A : LocalIndex R) : LocalStage A →+* R :=
  IsLocalization.lift (localDenominator_unit A)

private lemma localToRing_algebraMap {R : Type u} [CommRing R] [IsLocalRing R]
    (A : LocalIndex R) (x : A.1) :
    localToRing A (algebraMap A.1 (LocalStage A) x) = A.1.val x :=
  IsLocalization.lift_eq _ x

private lemma localToRing_local {R : Type u} [CommRing R] [IsLocalRing R]
    (A : LocalIndex R) : IsLocalHom (localToRing A) := by
  constructor
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (localPrime A).primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff _ (localPrime A) a s).mpr
  apply (IsLocalRing.notMem_maximalIdeal).mpr
  have he := congrArg (localToRing A) (IsLocalization.mk'_spec (LocalStage A) a s)
  rw [map_mul, localToRing_algebraMap, localToRing_algebraMap] at he
  change IsUnit (A.1.val a)
  rw [← he]
  exact hx.mul (localDenominator_unit A s)

private noncomputable def localCocone (R : Type u) [CommRing R] [IsLocalRing R] :
    Cocone (localDiagram R) where
  pt := .of R
  ι :=
    { app A := ofHom (localToRing A)
      naturality {A B} f := by
        ext1
        change (localToRing B).comp (localTransition (leOfHom f)) = localToRing A
        apply IsLocalization.ringHom_ext (localPrime A).primeCompl
        ext x
        simp only [RingHom.comp_apply, localTransition_algebraMap, localToRing_algebraMap]
        rfl }

-- Restrict any cocone on the localized system to the original subalgebras.
private noncomputable def unlocalizedCocone {R : Type u} [CommRing R] [IsLocalRing R]
    (s : Cocone (localDiagram R)) : Cocone (fgSubalgebraDiagram R) where
  pt := s.pt
  ι :=
    { app A := ofHom (algebraMap A.1 (LocalStage A)) ≫ s.ι.app A
      naturality {A B} f := by
        have hw := s.w f
        ext x
        have he := ConcreteCategory.congr_hom hw (algebraMap A.1 (LocalStage A) x)
        change (s.ι.app B).hom
          (algebraMap B.1 (LocalStage B) (Subalgebra.inclusion (leOfHom f) x)) =
            (s.ι.app A).hom (algebraMap A.1 (LocalStage A) x)
        change (s.ι.app B).hom
          (localTransition (leOfHom f) (algebraMap A.1 (LocalStage A) x)) =
            (s.ι.app A).hom (algebraMap A.1 (LocalStage A) x) at he
        rwa [localTransition_algebraMap] at he }

-- The original subalgebra colimit supplies the descent map; localization extensionality
-- extends its factorization from each subalgebra to its localization.
private noncomputable def localCoconeIsColimit (R : Type u) [CommRing R] [IsLocalRing R] :
    IsColimit (localCocone R) where
  desc s := (isColimitFgSubalgebraCocone R).desc (unlocalizedCocone s)
  fac s A := by
    ext1
    change ((isColimitFgSubalgebraCocone R).desc (unlocalizedCocone s)).hom.comp
      (localToRing A) = (s.ι.app A).hom
    apply IsLocalization.ringHom_ext (localPrime A).primeCompl
    ext x
    have he := ConcreteCategory.congr_hom
      ((isColimitFgSubalgebraCocone R).fac (unlocalizedCocone s) A) x
    change ((isColimitFgSubalgebraCocone R).desc (unlocalizedCocone s)).hom
      (localToRing A (algebraMap A.1 (LocalStage A) x)) =
        (s.ι.app A).hom (algebraMap A.1 (LocalStage A) x)
    rw [localToRing_algebraMap]
    exact he
  uniq s m hm := by
    apply (isColimitFgSubalgebraCocone R).uniq (unlocalizedCocone s) m
    intro A
    ext x
    have he := ConcreteCategory.congr_hom (hm A) (algebraMap A.1 (LocalStage A) x)
    change m.hom (A.1.val x) = (s.ι.app A).hom (algebraMap A.1 (LocalStage A) x)
    change m.hom (localToRing A (algebraMap A.1 (LocalStage A) x)) =
      (s.ι.app A).hom (algebraMap A.1 (LocalStage A) x) at he
    rwa [localToRing_algebraMap] at he

/-- Every local ring is a directed colimit in commutative rings of local rings essentially
of finite type over `ℤ`, with local transition maps and local cocone maps.
Source: Stacks Project, Tag 00QU, proof, base-ring construction; also Tag 00QT.
(blueprint: lemma-quasi-finite-coordinates--1)

Proof: Index by finite subsets `A` of `R`, including the empty subset; union supplies common
upper bounds. Let `C_A = ℤ[A]` and contract the maximal ideal of `R` to a prime `q_A` of `C_A`.
Localize `C_A` at `q_A` (def-weil-pbc-localization-at-prime). The resulting local ring `R_A`
is essentially of finite type over `ℤ`, since `A` generates `C_A`
(def-weil-pbc-finite-type-algebra, def-weil-pbc-essentially-finite-type-algebra).
For `A ⊆ B`, the fraction map `a/s ↦ a/s` is well defined: any denominator and any witness
of equality outside `q_A` remain outside `q_B`. This map preserves ring operations and
sends the maximal ideal into the maximal ideal. Its formula gives identity and composition.
Every denominator outside `q_A` is a unit in `R`
(lem-weil-pbc-local-ring-unit-criterion), so `a/s ↦ a * s⁻¹` defines a local ring map to `R`.
The fraction equality criterion proves well-definedness and compatibility. These maps are
injective: equality of images implies `at - bs = 0` already in the subring `C_A`.
Every `x : R` occurs at the singleton subset `{x}`. For any compatible cocone into any
commutative ring `T`, send an element of `R` to its image from any stage representing it.
Two representations agree in the union stage by injectivity into `R`, so this rule is
independent of the representation. Using a common stage proves it preserves sums and
products; the empty stage supplies zero and one. It factors the cocone maps and is unique
by the singleton representations, proving the universal property
(def-weil-pbc-category-colimit). -/
theorem exists_local_essFiniteType_colimit (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ CommRingCat.{u}) (π : F ⟶ (Functor.const I).obj (CommRingCat.of R)),
      (∀ i : I, IsLocalRing (F.obj i)) ∧
      (∀ (i j : I) (f : i ⟶ j), IsLocalHom (F.map f).hom) ∧
      (∀ i : I, IsLocalHom (π.app i).hom) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      (∀ i : I, Algebra.EssFiniteType ℤ (F.obj i)) := by
  refine ⟨LocalIndex R, inferInstance, inferInstance, inferInstance,
    localDiagram R, (localCocone R).ι, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact inferInstance
  · intro A B f
    change IsLocalHom (localTransition (leOfHom f))
    exact Localization.isLocalHom_localRingHom _ _ _ _
  · intro A
    exact localToRing_local A
  · exact ⟨localCoconeIsColimit R⟩
  · intro A
    -- Match the canonical integer algebra on the categorical ring object.
    let : Algebra ℤ (LocalStage A) := Ring.toIntAlgebra _
    change Algebra.EssFiniteType ℤ (LocalStage A)
    have : Algebra.FiniteType ℤ A.1 := (Subalgebra.fg_iff_finiteType A.1).mp A.2
    have : Algebra.EssFiniteType A.1 (LocalStage A) :=
      Algebra.EssFiniteType.of_isLocalization _ (localPrime A).primeCompl
    exact Algebra.EssFiniteType.comp ℤ A.1 (LocalStage A)

end CommRingCat
