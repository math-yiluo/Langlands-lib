/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RingHom.EssFiniteType
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime

/-! # Localizing a filtered ring system at a local target

Source: Stacks Project, Algebra, Tags 037D and 00QV.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace RingHom

/-- A localization of a filtered ring colimit which is local is the colimit of
stage localizations at the inverse images of its maximal ideal.

Source: Stacks Project, Algebra, proof of Tag 037D and Tag 00QV.
(blueprint: lem-weil-pbc-localize-filtered-ring-system)

Proof: Contract the maximal ideal of T to q in colimit D. Since T is a
localization and local, it is also the localization at q: enlarge the original
denominators to all elements mapping to units. Apply the prime-localization
colimit theorem at q. Its stage rings are localizations at contracted primes,
so their localization maps are essentially of finite type. Identify the
localization of colimit D at q with T by the unique algebra equivalence.
Postcompose the cocone with this equivalence. The induced stage maps to T
are local, because a fraction maps to a unit precisely when its numerator
avoids the contracted prime. The cocone remains a colimit under the equivalence.
The transformation λ consists of the canonical stage localization maps. -/
theorem exists_localized_filtered_ring_system
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{u}) (T : CommRingCat.{u}) [IsLocalRing T]
    (g : (colimit D : CommRingCat.{u}) →+* T) (W : Submonoid (colimit D : CommRingCat.{u}))
    (hT : letI := g.toAlgebra; IsLocalization W T) :
    ∃ (B : J ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T) (ιB : D ⟶ B),
      Nonempty (IsColimit (Cocone.mk T β)) ∧
      (∀ i, (ιB.app i).hom.EssFiniteType) ∧
      (∀ i, IsLocalHom (β.app i).hom) ∧
      (∀ i, (β.app i).hom.comp (ιB.app i).hom = g.comp (colimit.ι D i).hom) := by
  classical
  let := g.toAlgebra
  have : IsLocalization W T := hT
  let q : Ideal (colimit D : CommRingCat.{u}) := Ideal.comap g (IsLocalRing.maximalIdeal T)
  have : q.IsPrime := Ideal.IsPrime.comap _
  have hqT : IsLocalization q.primeCompl T := by
    apply IsLocalization.of_le W q.primeCompl
    · intro x hx
      change ¬ g x ∈ IsLocalRing.maximalIdeal T
      exact fun hn ↦ hn (IsLocalization.map_units T ⟨x, hx⟩)
    · intro x hx
      change ¬ ¬ IsUnit (g x) at hx
      exact not_not.mp hx
  let e : Localization.AtPrime q ≃ₐ[(colimit D : CommRingCat.{u})] T :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) T
  obtain ⟨_, _, B, hB, hnat, s, hs, hcompat, ⟨hcol⟩⟩ :=
    AlgebraicGeometry.filteredColimitLocalizationAtPrime D q
  let qi (i : J) : Ideal (D.obj i) := Ideal.comap (colimit.ι D i).hom q
  let ei (i : J) : B.obj i ≅ CommRingCat.of (Localization.AtPrime (qi i)) :=
    eqToIso (hB i)
  let j : s.pt ≅ T := eqToIso hs ≪≫ e.toRingEquiv.toCommRingCatIso
  let β : B ⟶ (Functor.const J).obj T := (s.extend j.hom).ι
  let ιB : D ⟶ B :=
    { app := fun i ↦ CommRingCat.ofHom (algebraMap (D.obj i)
          (Localization.AtPrime (qi i))) ≫ (ei i).inv
      naturality := by
        intro i k a
        simpa only [ei, eqToIso.inv, Category.assoc] using (hnat i k a).symm }
  have hcomp (i : J) :
      (β.app i).hom.comp (ιB.app i).hom = g.comp (colimit.ι D i).hom := by
    ext x
    have h := ConcreteCategory.congr_hom (hcompat i) x
    change e ((eqToHom hs).hom ((s.ι.app i).hom
      ((ei i).inv.hom (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x)))) = _
    change (eqToHom hs).hom ((s.ι.app i).hom
      ((ei i).inv.hom (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x))) =
        algebraMap (colimit D : CommRingCat.{u}) (Localization.AtPrime q)
          ((colimit.ι D i).hom x) at h
    rw [h, e.commutes]
    rfl
  refine ⟨B, β, ιB, ⟨hcol.extendIso j.hom⟩, ?_, ?_, hcomp⟩
  · intro i
    have hloc : (algebraMap (D.obj i) (Localization.AtPrime (qi i))).EssFiniteType :=
      essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization _ (qi i).primeCompl)
    exact hloc.comp (FiniteType.of_surjective (ei i).inv.hom
      (ei i).symm.commRingCatIsoToRingEquiv.surjective).essFiniteType
  · intro i
    let li : Localization.AtPrime (qi i) →+* Localization.AtPrime q :=
      Localization.localRingHom (qi i) q (colimit.ι D i).hom rfl
    have hli : IsLocalHom li :=
      Localization.isLocalHom_localRingHom (qi i) q (colimit.ι D i).hom rfl
    have he : IsLocalHom e.toRingHom :=
      isLocalHom_of_leftInverse e.symm.toRingHom e.left_inv
    have hei : IsLocalHom (ei i).hom.hom :=
      isLocalHom_of_leftInverse (ei i).inv.hom
        (ei i).commRingCatIsoToRingEquiv.left_inv
    have hb : (β.app i).hom = e.toRingHom.comp (li.comp (ei i).hom.hom) := by
      have hb' : (β.app i).hom.comp (ei i).inv.hom = e.toRingHom.comp li := by
        apply IsLocalization.ringHom_ext (qi i).primeCompl
        ext x
        have hx := DFunLike.congr_fun (hcomp i) x
        change (β.app i).hom ((ei i).inv.hom
          (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x)) = _ at hx
        change _ = e (li (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x))
        rw [Localization.localRingHom_to_map, e.commutes]
        exact hx
      ext x
      have hx := DFunLike.congr_fun hb' ((ei i).hom.hom x)
      change (β.app i).hom ((ei i).inv.hom ((ei i).hom.hom x)) =
        e (li ((ei i).hom.hom x)) at hx
      have hi : (ei i).inv.hom ((ei i).hom.hom x) = x :=
        (ei i).commRingCatIsoToRingEquiv.left_inv x
      rw [hi] at hx
      exact hx
    rw [hb]
    infer_instance

end RingHom
