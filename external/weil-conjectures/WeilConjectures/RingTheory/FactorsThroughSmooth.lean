/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
import WeilConjectures.RingTheory.FactorsThroughLocalization

/-!
# Maps from finitely presented algebras factor through smooth algebras

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07FJ, item-eighth-resolve,
lines 3062-3074 (blueprint: lem-weil-pbc-essentially-smooth-factors-through-smooth).
-/

@[expose] public section

universe u₁ v₁ w

namespace Algebra

/-- A map from a finitely presented `R`-algebra to an essentially smooth `R`-algebra factors
through a smooth `R`-algebra. Source: Stacks Project, Smoothing Ring Maps,
proof of Lemma Tag 07FJ,
item-eighth-resolve, lines 3062-3074
(blueprint: lem-weil-pbc-essentially-smooth-factors-through-smooth).

Proof:
1. By def-weil-pbc-essentially-smooth-ring-map, write `D` as `Localization S` for a
   smooth `R`-algebra `P`. For each `s ∈ S`, `Localization.Away s` is smooth by
   lem-weil-pbc-smooth-ring-map-principal-localization.
2. By theorem-finite-etale-covers-proper-henselian--2, these principal
   localizations form a filtered diagram with colimit `Localization S`, in the sense of
   def-weil-pbc-category-colimit. The transition maps and coprojections commute with
   `P`'s structure map, hence are `R`-algebra maps.
3. Compose `g` with the presentation isomorphism of `D`. Finite presentation of `C`
   and lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit give a stage
   and a map from `C` to that stage whose composite with its coprojection is this map.
4. Take `T` to be that smooth principal localization. Compose its coprojection with
   the inverse presentation isomorphism of `D`; the two maps have composite `g`.
-/
theorem essentiallySmooth_factors_through_smooth
    (R : Type u₁) (C : Type v₁) (D : Type w)
    [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra.FinitePresentation R C]
    (hD : EssentiallySmooth R D) (g : C →ₐ[R] D) :
    ∃ (T : Type (max u₁ v₁ w)) (_ : CommRing T) (_ : Algebra R T),
      Smooth R T ∧ ∃ (f : C →ₐ[R] T) (k : T →ₐ[R] D), k.comp f = g := by
  rcases hD with ⟨P, hP, hRP, hPsmooth, S, ⟨e⟩⟩
  let : CommRing P := hP
  let : Algebra R P := hRP
  obtain ⟨s, f, k, hk⟩ :=
    factors_through_principal_localization R C P S (e.toAlgHom.comp g)
  let : Smooth R P := hPsmooth
  let : Smooth P (Localization.Away (s : P)) := Smooth.of_isLocalization_Away (s : P)
  let : Smooth R (Localization.Away (s : P)) := Smooth.comp R P _
  let T := ULift.{max u₁ v₁ w} (Localization.Away (s : P))
  let a : T ≃ₐ[R] Localization.Away (s : P) := ULift.algEquiv
  refine ⟨T, inferInstance, inferInstance, Smooth.of_equiv a.symm,
    a.symm.toAlgHom.comp f, e.symm.toAlgHom.comp (k.comp a.toAlgHom), ?_⟩
  ext x
  change e.symm (k (f x)) = g x
  have hx : k (f x) = (e : D → Localization S) (g x) := by
    exact DFunLike.congr_fun hk x
  rw [hx]
  exact e.symm_apply_apply (g x)

end Algebra
