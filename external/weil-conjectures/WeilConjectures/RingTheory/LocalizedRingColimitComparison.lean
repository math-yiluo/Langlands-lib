/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.Algebra.Category.Ring.FilteredColimits
/-! # Localized ring comparison
Source: Stacks Project, Algebra, Tag 037D, proof first paragraph.
(blueprint: lem-pc-localized-ring-colimit-comparison) -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra
/-- Canonical localized ring colimit comparison.
Source: Stacks Project, Algebra, Tag 037D, proof first paragraph.
(blueprint: lem-pc-localized-ring-colimit-comparison)
Proof: The stage local maps form a cocone, since their restrictions to the original
rings agree. Lift each numerator and denominator through the supplied ring colimit and
pass to a common stage; the lifted denominator avoids the contracted prime. This proves
surjectivity of the induced map. For injectivity, lift a multiplier outside the prime
witnessing equality of fractions. The zero cross difference holds at a later stage by
the filtered colimit equality criterion. The multiplier remains outside the prime,
so the fractions agree there. Hence the induced map is a bijective ring map. Its inverse
is a ring map and the coprojection formula is its defining factorization equation.
The numerator transition equation determines each entire localized transition map. -/
theorem localizedRingColimitComparison
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {T : Type u} [CommRing T] (F L : Λ ⥤ CommRingCat.{u})
    (κ : F ⟶ (Functor.const Λ).obj (CommRingCat.of T))
    (hF : Nonempty (IsColimit (Cocone.mk (CommRingCat.of T) κ)))
    (p : Ideal T) [p.IsPrime] (pᵢ : ∀ i, Ideal (F.obj i)) [∀ i, (pᵢ i).IsPrime]
    (hp : ∀ i, pᵢ i = p.comap (κ.app i).hom)
    (eᵢ : ∀ i, L.obj i ≃+* Localization.AtPrime (pᵢ i))
    (hm : ∀ (i j : Λ) (f : i ⟶ j) (x : F.obj i),
      eᵢ j ((L.map f).hom ((eᵢ i).symm (algebraMap _ _ x))) =
        algebraMap _ _ ((F.map f).hom x)) :
    ∃ e : (colimit L : CommRingCat.{u}) ≃+* Localization.AtPrime p,
      ∀ i (z : L.obj i), e ((colimit.ι L i).hom z) =
        Localization.localRingHom (pᵢ i) p (κ.app i).hom (hp i) (eᵢ i z) := by
  let g : ∀ i, L.obj i →+* Localization.AtPrime p := fun i ↦
    (Localization.localRingHom (pᵢ i) p (κ.app i).hom (hp i)).comp (eᵢ i).toRingHom
  have hg : ∀ (i j : Λ) (a : i ⟶ j), (g j).comp (L.map a).hom = g i := by
    intro i j a
    have hloc : ((g j).comp (L.map a).hom).comp (eᵢ i).symm.toRingHom =
        (g i).comp (eᵢ i).symm.toRingHom := by
      apply IsLocalization.ringHom_ext (pᵢ i).primeCompl
      ext x
      change Localization.localRingHom (pᵢ j) p (κ.app j).hom (hp j)
        (eᵢ j ((L.map a).hom ((eᵢ i).symm (algebraMap _ _ x)))) =
        Localization.localRingHom (pᵢ i) p (κ.app i).hom (hp i)
          (eᵢ i ((eᵢ i).symm (algebraMap _ _ x)))
      rw [hm, (eᵢ i).apply_symm_apply]
      simp only [Localization.localRingHom_to_map]
      have hκ := κ.naturality a
      exact congrArg (algebraMap T (Localization.AtPrime p))
        (ConcreteCategory.congr_hom hκ x)
    ext z
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom,
      RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply] using RingHom.congr_fun hloc (eᵢ i z)
  let c : Cocone L := Cocone.mk (CommRingCat.of (Localization.AtPrime p))
    { app := fun i ↦ CommRingCat.ofHom (g i)
      naturality := fun i j a ↦ by
        apply CommRingCat.hom_ext
        exact hg i j a }
  classical
  let hcF := hF.some
  let U : Cocone L → Cocone F := fun s ↦
    { pt := s.pt
      ι :=
        { app := fun i ↦ CommRingCat.ofHom
            ((eᵢ i).symm.toRingHom.comp
              (algebraMap (F.obj i) (Localization.AtPrime (pᵢ i)))) ≫ s.ι.app i
          naturality := by
            intro i j a
            ext x
            have ht : (L.map a).hom ((eᵢ i).symm (algebraMap _ _ x)) =
                (eᵢ j).symm (algebraMap _ _ ((F.map a).hom x)) := by
              apply (eᵢ j).injective
              rw [hm, (eᵢ j).apply_symm_apply]
            change (s.ι.app j).hom ((eᵢ j).symm
                (algebraMap _ _ ((F.map a).hom x))) =
              (s.ι.app i).hom ((eᵢ i).symm (algebraMap _ _ x))
            rw [← ht]
            exact ConcreteCategory.congr_hom (s.w a)
              ((eᵢ i).symm (algebraMap _ _ x)) } }
  let f : ∀ s : Cocone L, CommRingCat.of T ⟶ s.pt := fun s ↦ hcF.desc (U s)
  have hf (s : Cocone L) (i : Λ) (x : F.obj i) :
      (f s).hom ((κ.app i).hom x) =
        (s.ι.app i).hom ((eᵢ i).symm (algebraMap _ _ x)) := by
    exact ConcreteCategory.congr_hom (hcF.fac (U s) i) x
  have hu (s : Cocone L) (y : p.primeCompl) : IsUnit ((f s).hom y) := by
    obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) hcF) (y : T)
    change (κ.app i).hom x = (y : T) at hx
    have hxq : x ∈ (pᵢ i).primeCompl := by
      change x ∉ pᵢ i
      rw [hp i]
      change (κ.app i).hom x ∉ p
      rw [hx]
      exact y.property
    rw [← hx, hf]
    exact ((IsLocalization.map_units (R := F.obj i)
      (Localization.AtPrime (pᵢ i)) ⟨x, hxq⟩).map (eᵢ i).symm.toRingHom).map
        (s.ι.app i).hom
  have hc : IsColimit c :=
    { desc := fun s ↦ CommRingCat.ofHom
        (IsLocalization.lift (S := Localization.AtPrime p) (hu s))
      fac := by
        intro s i
        apply CommRingCat.hom_ext
        have heq : ((IsLocalization.lift (hu s)).comp (g i)).comp
            (eᵢ i).symm.toRingHom = (s.ι.app i).hom.comp (eᵢ i).symm.toRingHom := by
          apply IsLocalization.ringHom_ext (pᵢ i).primeCompl
          ext x
          change IsLocalization.lift (hu s)
            (Localization.localRingHom (pᵢ i) p (κ.app i).hom (hp i)
              (eᵢ i ((eᵢ i).symm (algebraMap _ _ x)))) =
                (s.ι.app i).hom ((eᵢ i).symm (algebraMap _ _ x))
          rw [(eᵢ i).apply_symm_apply, Localization.localRingHom_to_map,
            IsLocalization.lift_eq]
          exact hf s i x
        ext z
        have hh := RingHom.congr_fun heq (eᵢ i z)
        change IsLocalization.lift (hu s) (g i ((eᵢ i).symm (eᵢ i z))) =
          (s.ι.app i).hom ((eᵢ i).symm (eᵢ i z)) at hh
        change IsLocalization.lift (hu s) (g i z) = (s.ι.app i).hom z
        simpa only [RingEquiv.symm_apply_apply] using hh
      uniq := by
        intro s m hm'
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext p.primeCompl
        have heq : CommRingCat.ofHom
            (m.hom.comp (algebraMap T (Localization.AtPrime p))) = f s := by
          apply hcF.hom_ext
          intro i
          ext x
          change m.hom (algebraMap T (Localization.AtPrime p) ((κ.app i).hom x)) =
            (f s).hom ((κ.app i).hom x)
          rw [hf]
          have hh := ConcreteCategory.congr_hom (hm' i)
            ((eᵢ i).symm (algebraMap _ _ x))
          change m.hom (Localization.localRingHom (pᵢ i) p (κ.app i).hom (hp i)
            (eᵢ i ((eᵢ i).symm (algebraMap _ _ x)))) =
              (s.ι.app i).hom ((eᵢ i).symm (algebraMap _ _ x)) at hh
          simp only [RingEquiv.apply_symm_apply, Localization.localRingHom_to_map] at hh
          convert hh using 1
        ext x
        change m.hom (algebraMap _ _ x) = IsLocalization.lift (hu s) (algebraMap _ _ x)
        rw [IsLocalization.lift_eq]
        exact ConcreteCategory.congr_hom heq x }
  let e := CategoryTheory.Iso.commRingCatIsoToRingEquiv
    ((colimit.isColimit L).coconePointUniqueUpToIso hc)
  refine ⟨e, ?_⟩
  intro i z
  exact ConcreteCategory.congr_hom
    ((colimit.isColimit L).comp_coconePointUniqueUpToIso_hom hc i) z
end Algebra
