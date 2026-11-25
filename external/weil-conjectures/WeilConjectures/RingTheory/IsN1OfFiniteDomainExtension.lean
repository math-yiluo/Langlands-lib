/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Noetherian.Basic

/-!
# Descent of N-1 along finite extensions of domains

Source: Stacks Project, Algebra, Lemma 10.161.7 (Tag 032K), N-1 clause
(blueprint: lem-weil-pbc-n1-descends-finite-domain-extension).
-/

@[expose] public section

universe uA uB uK uL

set_option autoImplicit false

/-- N-1 descends along a finite injective extension of domains when the smaller domain
is Noetherian. Source: Stacks Project, Algebra, Lemma 10.161.7 (Tag 032K), N-1 clause
(blueprint: lem-weil-pbc-n1-descends-finite-domain-extension).

Proof (the source omits the proof and gives the integral-closure containment as a hint):
1. The inclusion `A → B` extends to an injective `A`-linear map `K → L` of fraction
   fields: send `a / s` to `a / s` in `L`. Equality of fractions gives well-definedness;
   nonzero elements of `A` stay nonzero, and a field homomorphism is injective
   (def-weil-pbc-localization-at-prime).
2. This map sends the integral closure of `A` in `K` into that of `B` in `L`:
   apply the map to a monic equation over `A` and regard its coefficients as elements
   of `B` (def-weil-pbc-integral-closure).
3. The latter closure is finite over `B` by N-1, and `B` is finite over `A`, so it is
   finite over `A` by transitivity (def-weil-pbc-japanese-domain,
   def-weil-finitely-generated-module, lem-weil-pbc-finite-module-over-finite-algebra).
4. The image of the first closure is an `A`-submodule of the latter closure. Since
   `A` is Noetherian it is finite (def-weil-pbc-noetherian-ring,
   lem-weil-pbc-noetherian-submodule-finite). Injectivity identifies the first closure
   with this image, so it too is finite over `A`, precisely N-1
   (def-weil-pbc-integral-closure, def-weil-pbc-japanese-domain). -/
theorem isN1_of_finite_domain_extension
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (hAB : Function.Injective (algebraMap A B)) (hB : IsN1 B L) : IsN1 A K := by
  let : Algebra A L := Algebra.compHom L (algebraMap A B)
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  let g : A →ₐ[A] L := Algebra.ofId A L
  have hg : Function.Injective g :=
    (IsFractionRing.injective B L).comp hAB
  let f : K →ₐ[A] L := IsFractionRing.liftAlgHom hg
  let : Algebra A (integralClosure B L) :=
    Algebra.compHom (integralClosure B L) (algebraMap A B)
  have : IsScalarTower A B (integralClosure B L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite B (integralClosure B L) := hB
  have : Module.Finite A (integralClosure B L) :=
    Module.Finite.trans B (integralClosure B L)
  let i : integralClosure A K →ₗ[A] integralClosure B L :=
    { toFun := fun x => ⟨f x, (x.property.map f).tower_top⟩
      map_add' := by intro x y; apply Subtype.ext; exact f.map_add x y
      map_smul' := by intro a x; apply Subtype.ext; exact f.toLinearMap.map_smul a x }
  exact Module.Finite.of_injective i fun x y h =>
    Subtype.ext (f.injective (congrArg Subtype.val h))
