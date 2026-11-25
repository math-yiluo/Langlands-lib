/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.FibreRingNoetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Geometric regularity of a fibre from maximal target localizations

Source: Stacks Project, More on Algebra, Lemma 07C0, fibre argument.
(blueprint: lem-weil-pbc-geometrically-regular-fiber-of-maximal).
-/

@[expose] public section

universe u v

namespace Algebra

private theorem regular_tensor_of_maximal
    {R : Type u} {S : Type v} {K : Type (max u v)}
    [CommRing R] [CommRing S] [CommRing K] [Algebra R S] [Algebra R K]
    [IsNoetherianRing (TensorProduct R K S)]
    (h : ∀ (m : Ideal S) [m.IsMaximal],
      IsRegularRing (TensorProduct R K (Localization.AtPrime m))) :
    IsRegularRing (TensorProduct R K S) := by
  apply isRegularRing_iff.mpr
  intro n hn
  let f := (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R K S)
  let q := n.comap f.toRingHom
  have : q.IsPrime := Ideal.comap_isPrime _ n
  obtain ⟨m, hm, hqm⟩ := q.exists_le_maximal (show q.IsPrime from inferInstance).ne_top
  let _ := hm
  let M := m.primeCompl.map f
  have hd : Disjoint (M : Set (TensorProduct R K S)) (n : Set _) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ hx
    exact hs (hqm hx)
  let C := Localization M
  have hp : (n.map (algebraMap (TensorProduct R K S) C)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M C n hn hd
  let _ := hp
  have he : (n.map (algebraMap (TensorProduct R K S) C)).under
      (TensorProduct R K S) = n :=
    IsLocalization.under_map_of_isPrime_disjoint M C hn hd
  have : IsRegularRing C := by
    have := h m
    exact IsRegularRing.of_ringEquiv
      (IsLocalization.tensorProductEquivOfMapIncludeRight R K m.primeCompl
        (Localization.AtPrime m) C).toRingEquiv
  have e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
    (n.map (algebraMap (TensorProduct R K S) C))
  have : IsRegularLocalRing
      (Localization.AtPrime ((n.map (algebraMap (TensorProduct R K S) C)).under
        (TensorProduct R K S))) :=
    IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv
    (Localization.localRingEquiv
      ((n.map (algebraMap (TensorProduct R K S) C)).under (TensorProduct R K S))
      n (RingEquiv.refl _) (by
        change _ = n.comap (RingHom.id _)
        rw [Ideal.comap_id]
        exact he))

/-- For a fixed source prime, geometric regularity of the fibre can be checked after
localizing the target at each maximal ideal. Flatness is not required.
Source: Stacks Project, More on Algebra, Lemma 07C0, the fibre part of (3) implies (1).
(blueprint: lem-weil-pbc-geometrically-regular-fiber-of-maximal).

Proof: Write F = kappa(p) tensor_R S. It is a localization of S/pS, hence Noetherian.
Fix a finite purely inseparable extension K of kappa(p). The extended fibre F_K is
finite over F, hence Noetherian. Fix a prime n of F_K. Its contraction q to S is a
prime ideal. Choose a maximal ideal m containing q. By hypothesis, the fibre
kappa(p) tensor_R S_m is geometrically regular. Its scalar extension to K is
therefore regular. Tensor product commutes with localization, so this extended
local fibre is the localization of F_K at the images of S minus m. The prime n
avoids these images because its contraction q is contained in m. Thus (F_K)_n is
a localization of the regular extended local fibre and is regular local. The
regular-ring local criterion proves F_K regular. Since K was arbitrary, F is
geometrically regular. For S = 0, all these fibres are zero and regular, so the
vacuous maximal-ideal hypothesis also gives the conclusion. -/
theorem isGeometricallyRegular_fiber_of_localizations_maximal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (p : Ideal R) [p.IsPrime]
    (h : ∀ (m : Ideal S) [m.IsMaximal],
      IsGeometricallyRegular p.ResidueField (p.Fiber (Localization.AtPrime m))) :
    IsGeometricallyRegular p.ResidueField (p.Fiber S) := by
  have := p.isNoetherianRing_fiber (B := S)
  refine ⟨inferInstance, ?_⟩
  intro K _ _ _ _
  let : Algebra R K := Algebra.compHom K (algebraMap R p.ResidueField)
  let : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  let F := p.Fiber S
  let : Algebra F (TensorProduct p.ResidueField K F) :=
    Algebra.TensorProduct.rightAlgebra
  have : Module.Finite F (TensorProduct p.ResidueField K F) := by
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight p.ResidueField F K).toLinearEquiv
  have : IsNoetherianRing (TensorProduct p.ResidueField K F) :=
    IsNoetherianRing.of_finite F _
  let e := Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K S
  have : IsNoetherianRing (TensorProduct R K S) :=
    isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  have : IsRegularRing (TensorProduct R K S) := by
    apply regular_tensor_of_maximal
    intro m hm
    have := (h m).2 K
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K
        (Localization.AtPrime m)).toRingEquiv
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

end Algebra
