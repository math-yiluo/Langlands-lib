/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRingMaximalIdealCriterion
public import WeilConjectures.RingTheory.PairHenselizationNoetherianCompletion
import WeilConjectures.RingTheory.PairHenselizationRegularFibers
import WeilConjectures.RingTheory.FlatLocalCompletionIso
import WeilConjectures.RingTheory.RegularThroughLocalization
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularRingEquiv
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FibreRingNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Maximal local completion maps of a henselization of a G-ring

Source: Stacks Project, More on Algebra, Tag 0AH3.
(blueprint: lem-weil-pbc-henselization-pair-g-ring-core).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

private theorem localization_maximal_residue_comparison
    (A B : Type u) [CommRing A] [CommRing B] (I : Ideal A) (f : A →+* B)
    (m : Ideal B) [m.IsMaximal] (hJm : I.map f ≤ m)
    (hq : Function.Surjective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) :
    let p := m.comap f
    let φ := Localization.localRingHom p m f rfl
    Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime m) ∧
      Function.Bijective (Ideal.quotientMap
        (IsLocalRing.maximalIdeal (Localization.AtPrime m)) φ
        (IsLocalRing.maximalIdeal_comap φ).ge) := by
  let J := I.map f
  have happrox : ∀ b : B, ∃ a : A, b - f a ∈ J := by
    intro b
    obtain ⟨x, hx⟩ := hq (Ideal.Quotient.mk J b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_⟩
    rw [Ideal.quotientMap_mk] at hx
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hx.symm
  let p := m.comap f
  have hmap : Ideal.map f p = m := by
    apply le_antisymm Ideal.map_comap_le
    intro b hb
    obtain ⟨a, ha⟩ := happrox b
    have hap : a ∈ p := by
      change f a ∈ m
      simpa only [sub_sub_cancel] using m.sub_mem hb (hJm ha)
    have hIp : I ≤ p := Ideal.map_le_iff_le_comap.mp hJm
    simpa only [sub_add_cancel] using
      (Ideal.map f p).add_mem (Ideal.map_mono hIp ha) (Ideal.mem_map_of_mem f hap)
  let R := Localization.AtPrime p
  let S := Localization.AtPrime m
  let φ : R →+* S := Localization.localRingHom p m f rfl
  have hmax : Ideal.map φ (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      show φ.comp (algebraMap A R) = (algebraMap B S).comp f by
        apply RingHom.ext
        intro x
        exact Localization.localRingHom_to_map p m f rfl x,
      ← Ideal.map_map, hmap, Localization.AtPrime.map_eq_maximalIdeal]
  have hres : Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal S) φ
      (IsLocalRing.maximalIdeal_comap φ).ge) := by
    refine ⟨Ideal.quotientMap_injective' (IsLocalRing.maximalIdeal_comap φ).le, ?_⟩
    intro y
    obtain ⟨b, hb⟩ := m.algebraMap_residueField_surjective y
    obtain ⟨a, ha⟩ := happrox b
    refine ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (algebraMap A R a), ?_⟩
    rw [Ideal.quotientMap_mk, Localization.localRingHom_to_map, ← hb]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    change algebraMap B S (f a) - algebraMap B S b ∈ _
    rw [← map_sub, ← Localization.AtPrime.map_eq_maximalIdeal]
    apply Ideal.mem_map_of_mem
    simpa only [neg_sub] using m.neg_mem (hJm ha)
  exact ⟨hmax, hres⟩

/-- The Noetherian and maximal-local regularity part of the G-ring theorem for a
henselization of a pair.  It packages the completion comparison, finite separable
fibres, and geometric-regularity argument of Stacks Project Tag 0AH3; the final
application of the maximal-ideal criterion is kept in the parent theorem.
Source: Stacks Project, More on Algebra, Tag 0AH3, proof paragraphs 1--4
(blueprint: lem-weil-pbc-henselization-pair-g-ring-core).
-/
theorem henselization_pair_noetherian_and_maximal_regular
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : Nonempty (IsColimit c) ∧
      HenselianRing c.pt.right (I.map c.pt.hom.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map c.pt.hom.hom) c.pt.hom.hom
        (Ideal.le_comap_map)))
    (hA : IsGRing A) :
    IsNoetherianRing c.pt.right ∧
      ∀ (m : Ideal c.pt.right) [m.IsMaximal],
        RingHom.IsRegular
          (algebraMap (Localization.AtPrime m)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
              (Localization.AtPrime m))) := by
  classical
  have : IsNoetherianRing A := hA.1
  obtain ⟨hB, hflat, _⟩ := pair_henselization_noetherian_completion A I c hc.1.some
  have : IsNoetherianRing c.pt.right := hB
  refine ⟨hB, ?_⟩
  intro m hm
  let B : Type u := c.pt.right
  let f : A →+* B := c.pt.hom.hom
  let J := I.map f
  have : HenselianRing B J := hc.2.1
  -- Henselianness and quotient surjectivity give representatives modulo every maximal ideal.
  have hJm : J ≤ m := HenselianRing.jac.trans (sInf_le ⟨bot_le, hm⟩)
  let p := m.comap f
  let R := Localization.AtPrime p
  let S := Localization.AtPrime m
  let φ : R →+* S := Localization.localRingHom p m f rfl
  have hφflat : φ.Flat := RingHom.Flat.localRingHom hflat m p rfl
  have hcomparison := localization_maximal_residue_comparison A B I f m hJm hc.2.2.2
  let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let Shat := AdicCompletion (IsLocalRing.maximalIdeal S) S
  obtain ⟨φhat, _, hbij, hcomm⟩ := RingHom.flat_local_completion_iso φ hφflat
    hcomparison.1 hcomparison.2
  let e : Rhat ≃+* Shat := RingEquiv.ofBijective φhat hbij
  let g : B →+* Shat := (algebraMap S Shat).comp (algebraMap B S)
  have htriangle : e.toRingHom.comp ((algebraMap R Rhat).comp (algebraMap A R)) =
      g.comp f := by
    apply RingHom.ext
    intro x
    change φhat (algebraMap R Rhat (algebraMap A R x)) =
      algebraMap S Shat (algebraMap B S (f x))
    have hx := DFunLike.congr_fun hcomm (algebraMap A R x)
    change φhat (algebraMap R Rhat (algebraMap A R x)) =
      algebraMap S Shat (φ (algebraMap A R x)) at hx
    exact hx.trans (congrArg (algebraMap S Shat)
      (Localization.localRingHom_to_map p m f rfl x))
  have : IsNoetherianRing Rhat := AdicCompletion.isNoetherianRing _
  -- Transport the regular base completion map, then cancel the ind-etale extension.
  have hbase : ((algebraMap R Rhat).comp (algebraMap A R)).IsRegular := by
    exact (IsLocalization.isRegular_and_fiber p.primeCompl).1.comp_of_fiber_noetherian
      (hA.2 p) (fun q _ ↦ Ideal.isNoetherianRing_fiber q)
  have hcomposite : (g.comp f).IsRegular :=
    RingHom.IsRegular.of_ringEquiv _ _ (RingEquiv.refl A) e
      (by simpa using htriangle) hbase
  have hfib := pair_henselization_regular_fibers A I c hc.1.some Shat g hcomposite
  have hgreg : g.IsRegular := ⟨RingHom.Flat.comp
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat B S))
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat S Shat)), hfib⟩
  exact RingHom.isRegular_of_comp_algebraMap_localization m.primeCompl hgreg

end RingTheory
