/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import WeilConjectures.Mathlib.RingTheory.Flat.Localization

/-!
# Base change of flatness at a module point

Source: Stacks Project, Algebra, Theorem Tag 00RC, reduction paragraph;
Tags 00HI and 00HT. (blueprint: lem-weil-pbc-flat-localized-module-base-change)
-/

@[expose] public section

universe u v w x y z

open scoped TensorProduct
open TensorProduct

namespace Module.Flat

private theorem flat_at_prime_of_flat_localization
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
    (T : Submonoid S) (f : X →ₗ[S] Y) [IsLocalizedModule T f] [Flat R Y]
    (q : PrimeSpectrum S) (hT : T ≤ q.asIdeal.primeCompl) :
    Flat R (LocalizedModule q.asIdeal.primeCompl X) := by
  rw [Module.flat_localizedModule_iff]
  intro J y hy
  let g := AlgebraTensorModule.rTensor R J f
  have : IsLocalizedModule T g := inferInstance
  have hcomm (z : X ⊗[R] J) :
      J.subtype.lTensor Y (g z) = AlgebraTensorModule.rTensor R R f (J.subtype.lTensor X z) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul x j => rfl
  have hzero : g y = 0 := by
    apply (Flat.lTensor_preserves_injective_linearMap (M := Y) J.subtype
      Subtype.val_injective)
    rw [hcomm, hy, map_zero, map_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (f := g)).mp hzero
  exact ⟨t, hT t.2, ht⟩

/-- Flatness at the contracted prime persists under a scalar pushout and module base change.

Source: Stacks Project, Algebra, Theorem Tag 00RC, reduction paragraph, and
Tags 00HI (flat base change) and 00HT (localization and flatness).
(blueprint: lem-weil-pbc-flat-localized-module-base-change)

Proof:
1. Put p = q intersect B. Base change the flat A-module N_p along A -> R. It is flat
   over R by `Module.Flat.baseChange`. The pushout cancellation equivalence identifies
   S tensor_B N_p with R tensor_A N_p, so the former is R-flat as well.
2. Tensor the localization map N -> N_p with S. Tensor symmetry and
   `IsLocalizedModule.rTensor` show that this S-linear map is a localization at
   the image of B minus p. Precompose it with the inverse of the given equivalence.
   This gives a localization map from M to the flat R-module S tensor_B N_p.
3. For an ideal J of R, take an element of the kernel of M tensor_R J -> M tensor_R R.
   Its image in (S tensor_B N_p) tensor_R J vanishes, since the latter module is flat
   over R and tensor maps commute with the localization map. The zero criterion for
   localized modules, applied to this map tensored with J, supplies a denominator
   in the image of B minus p which annihilates the element.
4. Such a denominator is outside q by the definition of p. The criterion
   `Module.flat_localizedModule_iff` therefore proves that M_q is flat over R.

No finiteness or Noetherian assumption is needed, and q is allowed to be any prime. -/
theorem localizedModule_of_isPushout
    {A : Type u} {B : Type v} {R : Type w} {S : Type x}
    {N : Type y} {M : Type z}
    [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [Algebra A B] [Algebra A R] [Algebra R S] [Algebra B S] [Algebra A S]
    [IsScalarTower A B S] [IsScalarTower A R S] [Algebra.IsPushout A R B S]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (e : S ⊗[B] N ≃ₗ[S] M) (q : PrimeSpectrum S)
    (h : Module.Flat A
      (LocalizedModule (q.asIdeal.comap (algebraMap B S)).primeCompl N)) :
    Module.Flat R (LocalizedModule q.asIdeal.primeCompl M) := by
  let p := q.asIdeal.comap (algebraMap B S)
  let Np := LocalizedModule p.primeCompl N
  have : Flat A Np := h
  have : Flat R (R ⊗[A] Np) := inferInstance
  have : Flat R (S ⊗[B] Np) :=
    Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A R B S Np)
  let f : S ⊗[B] N →ₗ[S] S ⊗[B] Np :=
    AlgebraTensorModule.lTensor S S (LocalizedModule.mkLinearMap p.primeCompl N)
  let c := (TensorProduct.comm B S N).restrictScalars B
  let c' := (TensorProduct.comm B Np S).restrictScalars B
  let g := AlgebraTensorModule.rTensor B S (LocalizedModule.mkLinearMap p.primeCompl N)
  have : IsLocalizedModule p.primeCompl g := inferInstance
  have hc : f.restrictScalars B = c'.toLinearMap ∘ₗ g ∘ₗ c.toLinearMap := by
    ext s n
    rfl
  have hf : IsLocalizedModule p.primeCompl (f.restrictScalars B) := by
    rw [hc]
    infer_instance
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid S p.primeCompl) f :=
    IsLocalizedModule.of_restrictScalars p.primeCompl f
  let f' := f ∘ₗ e.symm.toLinearMap
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid S p.primeCompl) f' :=
    inferInstance
  apply flat_at_prime_of_flat_localization
    (Algebra.algebraMapSubmonoid S p.primeCompl) f' q
  rintro _ ⟨b, hb, rfl⟩
  exact hb


end Module.Flat
