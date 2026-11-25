/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularThroughLocalization
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.GeometricallyRegularFibersOfMaximal
public import Mathlib.RingTheory.Flat.Localization

/-!
# Regular ring maps are local on the target

Source: Stacks Project, More on Algebra, Lemma 07C0
(blueprint: lem-weil-pbc-regular-local-maximal).
-/

@[expose] public section

universe u v

namespace RingHom

/-- For a ring map with Noetherian target, regularity is equivalent to regularity of all
induced maps on prime localizations, and also to regularity at all maximal target ideals.
Source: Stacks Project, More on Algebra, Lemma 07C0
(blueprint: lem-weil-pbc-regular-local-maximal).

Proof:
1. Flatness is equivalent to flatness of all induced local maps, by
   `lem-weil-pbc-flat-map-local-criterion` (Stacks 00HT).
2. At a prime `q` above `p`, the closed fibre of the local map is a localization of the
   global fibre at `p`. This identification commutes with finite purely inseparable residue
   field extensions (`theorem-finite-etale-covers-proper-henselian--2`,
   `def-weil-pbc-localization-at-prime`). A Noetherian fibre ring is regular exactly when its prime
   localizations are regular local rings, by `lem-weil-pbc-regular-ring-local-criterion`. The same
   argument for each prime of the source local ring gives the equivalence of global regularity and
   the prime-local condition.
3. The prime-local condition includes the maximal-local condition. Conversely, put each
   target prime inside a maximal ideal. The map at that prime is obtained by further
   localization of the map at the maximal ideal. Apply the fibre-localization description
   and `lem-weil-pbc-regular-ring-local-criterion` again to obtain regularity there. Together
   with step 1, this gives the maximal-local equivalence. -/
theorem isRegular_iff_localRingHom_prime_and_maximal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S) :
    (f.IsRegular ↔ ∀ (q : Ideal S) [q.IsPrime],
      (Localization.localRingHom (q.comap f) q f rfl).IsRegular) ∧
    (f.IsRegular ↔ ∀ (m : Ideal S) [m.IsMaximal],
      (Localization.localRingHom (m.comap f) m f rfl).IsRegular) := by
  have hlocal (hf : f.IsRegular) (q : Ideal S) [q.IsPrime] :
      (Localization.localRingHom (q.comap f) q f rfl).IsRegular := by
    let : Algebra R S := f.toAlgebra
    have hf' : (algebraMap R S).IsRegular := hf
    have hcomp : (algebraMap R (Localization.AtPrime q)).IsRegular :=
      hf'.comp_of_fiber_noetherian
        (IsLocalization.isRegular_and_fiber q.primeCompl).1
        (fun p _ ↦ Ideal.isNoetherianRing_fiber p)
    let := (Localization.localRingHom (q.comap f) q f rfl).toAlgebra
    have : IsScalarTower R (Localization.AtPrime (q.comap f))
        (Localization.AtPrime q) :=
      .of_algebraMap_eq fun x ↦
        (Localization.localRingHom_to_map _ _ _ rfl x).symm
    exact isRegular_of_comp_algebraMap_localization (q.comap f).primeCompl hcomp
  have hmax (h : ∀ (m : Ideal S) [m.IsMaximal],
      (Localization.localRingHom (m.comap f) m f rfl).IsRegular) : f.IsRegular := by
    let : Algebra R S := f.toAlgebra
    refine ⟨?_, ?_⟩
    · change Module.Flat R S
      apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
        (fun P ↦ Algebra.linearMap S _)
      intro P _
      let := (Localization.localRingHom (P.comap f) P f rfl).toAlgebra
      have : IsScalarTower R (Localization.AtPrime (P.comap f))
          (Localization.AtPrime P) :=
        .of_algebraMap_eq fun x ↦
          (Localization.localRingHom_to_map _ _ _ rfl x).symm
      have : Module.Flat (Localization.AtPrime (P.comap f)) (Localization.AtPrime P) :=
        (h P).1
      exact Module.Flat.trans R (Localization.AtPrime (P.comap f)) (Localization.AtPrime P)
    · intro p _
      apply Algebra.isGeometricallyRegular_fiber_of_localizations_maximal p
      intro m _
      let := (Localization.localRingHom (m.comap f) m f rfl).toAlgebra
      have : IsScalarTower R (Localization.AtPrime (m.comap f))
          (Localization.AtPrime m) :=
        .of_algebraMap_eq fun x ↦
          (Localization.localRingHom_to_map _ _ _ rfl x).symm
      have hm : (algebraMap (Localization.AtPrime (m.comap f))
          (Localization.AtPrime m)).IsRegular := h m
      have hcomp : (algebraMap R (Localization.AtPrime m)).IsRegular :=
        (IsLocalization.isRegular_and_fiber (m.comap f).primeCompl).1
          |>.comp_of_fiber_noetherian hm (fun p _ ↦ Ideal.isNoetherianRing_fiber p)
      rw [RingHom.IsRegular, toAlgebra_algebraMap] at hcomp
      exact hcomp.2 p
  exact ⟨⟨hlocal, fun h ↦ hmax (fun m _ ↦ h m)⟩, ⟨fun hf m _ ↦ hlocal hf m, hmax⟩⟩

end RingHom
