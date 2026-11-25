/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.GlobalCompleteIntersectionPrincipalLocalization
import Mathlib.RingTheory.Localization.BaseChange
import all WeilConjectures.RingTheory.SmoothLocalCompleteIntersection

@[expose] public section

universe u v
namespace Algebra

private theorem globalCI_away_away {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (a h : A) (hci : IsGlobalCompleteIntersection k (Localization.Away h)) :
    IsGlobalCompleteIntersection k
      (Localization.Away (algebraMap A (Localization.Away a) h)) := by
  let Ah := Localization.Away h
  let Aa := Localization.Away a
  let Aha := Localization.Away (algebraMap A Ah a)
  let Aah := Localization.Away (algebraMap A Aa h)
  have : IsLocalization.Away (a * h) Aha := inferInstance
  have : IsLocalization.Away (a * h) Aah := inferInstance
  exact globalCI_equiv
    ((IsLocalization.algEquiv (.powers (a * h)) Aha Aah).restrictScalars k)
    (isGlobalCompleteIntersection_localizationAway k Ah hci (algebraMap A Ah a))

private theorem fibre_neighborhood_rebase
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {p p' : PrimeSpectrum R} (e : p = p') (q : PrimeSpectrum S)
    (hp : q.comap (algebraMap R S) = p)
    (hci : ∃ h : p.asIdeal.Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S p ⟨q, hp⟩).asIdeal ∧
      IsGlobalCompleteIntersection p.asIdeal.ResidueField (Localization.Away h)) :
    ∃ h : p'.asIdeal.Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S p' ⟨q, hp.trans e⟩).asIdeal ∧
      IsGlobalCompleteIntersection p'.asIdeal.ResidueField (Localization.Away h) := by
  subst p'
  exact hci

private theorem fibre_transport_same_base
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hp : q.comap (algebraMap R S) = p)
    (g : S) (q₁ : PrimeSpectrum (Localization.Away g))
    (hp₁ : q₁.comap (algebraMap R (Localization.Away g)) = p)
    (hq : q₁.comap (algebraMap S (Localization.Away g)) = q)
    (hci : ∃ h : p.asIdeal.Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S p ⟨q, hp⟩).asIdeal ∧
      IsGlobalCompleteIntersection p.asIdeal.ResidueField (Localization.Away h)) :
    ∃ h : p.asIdeal.Fiber (Localization.Away g),
      h ∉ (PrimeSpectrum.preimageEquivFiber R (Localization.Away g) p ⟨q₁, hp₁⟩).asIdeal ∧
      IsGlobalCompleteIntersection p.asIdeal.ResidueField (Localization.Away h) := by
  let k := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber S
  let F₁ := p.asIdeal.Fiber (Localization.Away g)
  let a : F := _root_.TensorProduct.tmul R (1 : k) g
  let e : F₁ ≃ₐ[k] Localization.Away a :=
    IsLocalization.Away.tensorProductEquivTMulRight R k g (Localization.Away g)
  let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, hp⟩
  let Q₁ := PrimeSpectrum.preimageEquivFiber R (Localization.Away g) p ⟨q₁, hp₁⟩
  let Qg := PrimeSpectrum.comap e.symm.toRingHom Q₁
  have hQ₁ : PrimeSpectrum.comap
      (TensorProduct.includeRight : Localization.Away g →ₐ[R] F₁).toRingHom Q₁ = q₁ :=
    congrArg Subtype.val
      ((PrimeSpectrum.preimageEquivFiber R (Localization.Away g) p).symm_apply_apply
        ⟨q₁, hp₁⟩)
  have hQg : PrimeSpectrum.comap (algebraMap F (Localization.Away a)) Qg = Q := by
    apply (PrimeSpectrum.preimageEquivFiber R S p).symm.injective
    dsimp only [Q]
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    change PrimeSpectrum.comap (TensorProduct.includeRight : S →ₐ[R] F).toRingHom
      (PrimeSpectrum.comap (algebraMap F (Localization.Away a)) Qg) = q
    rw [← hq, ← hQ₁]
    ext s
    change e.symm (algebraMap F (Localization.Away a)
      (_root_.TensorProduct.tmul R (1 : k) s)) ∈ Q₁.asIdeal ↔
      _root_.TensorProduct.tmul R (1 : k) (algebraMap S (Localization.Away g) s) ∈ Q₁.asIdeal
    have he := IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (S := k) S g
      (Localization.Away g) (1 : k) s
    rw [← he, e.symm_apply_apply]
  obtain ⟨h, hh, hci⟩ := hci
  let b := algebraMap F (Localization.Away a) h
  have hb : b ∉ Qg.asIdeal := by
    change h ∉ (PrimeSpectrum.comap (algebraMap F (Localization.Away a)) Qg).asIdeal
    rwa [hQg]
  refine ⟨e.symm b, hb, ?_⟩
  exact globalCI_equiv
    (IsLocalization.algEquivOfAlgEquiv (M := .powers b) (T := .powers (e.symm b))
      (Localization.Away b) (Localization.Away (e.symm b)) e.symm
      (Submonoid.map_powers e.symm b))
    (globalCI_away_away a h hci)

/-- Transport of a complete-intersection fibre witness across principal localization,
for a fixed prime `q₁` contracting to `q`.

Source: Stacks Project, Algebra, Tag 00SY, first sentence of (3) ⇒ (2), and Tag 00SA (1).
(blueprint: lem-weil-pbc-syntomic-principal-localization-fibre-transport).

Proof: put `p = q ∩ R`, `k = κ(p)`, `F = k ⊗[R] S`, and `a = 1 ⊗ g`.
The scalar tower and the contraction equality give `q₁ ∩ R = p`, identifying the two
base residue fields as `k`. Base change of principal localization identifies the new
fibre `F₁ = k ⊗[R] S_g` with `F_a`: denominators are powers of `a` and the map
`φ : F → F₁` sends `x ⊗ s` to `x ⊗ (s/1)`.

The inverse of `PrimeSpectrum.preimageEquivFiber` contracts a fibre prime along
the right tensor inclusion. The pure-tensor formula for the base-change equivalence
and `q₁ ∩ S = q` therefore show that `φ⁻¹(Q₁)` contracts to `q` in `S`.
Injectivity of this inverse equivalence gives `φ⁻¹(Q₁) = Q`.
Choose the witness `h` from `hci` and set `h₁ = φ(h)`.
It is outside `Q₁` because `h` is outside `Q`.

The localization `(F₁)_{h₁}` is a `k`-algebra isomorphic to `(F_h)_{a/1}`:
both have the universal property of inverting `a` and `h` in `F`. The given `F_h`
is a global complete intersection, so its principal localization at `a/1` is one
by Tag 00SA (1). Transport this conclusion along the `k`-algebra isomorphism:
the zero-ring clause is preserved; otherwise compose the polynomial-quotient
presentation with the isomorphism and use its homeomorphism on prime spectra to
preserve Krull dimension. This supplies the required witness `h₁`. -/
theorem exists_completeIntersection_fibre_transport
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (g : S) (hg : g ∉ q.asIdeal)
    (q₁ : PrimeSpectrum (Localization.Away g))
    (hq : q₁.comap (algebraMap S (Localization.Away g)) = q)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ h : (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).Fiber
          (Localization.Away g),
        h ∉ (PrimeSpectrum.preimageEquivFiber R (Localization.Away g)
          (q₁.comap (algebraMap R (Localization.Away g))) ⟨q₁, rfl⟩).asIdeal ∧
        IsGlobalCompleteIntersection
          (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).ResidueField
          (Localization.Away h) := by
  have _ := hg
  have hp : q₁.comap (algebraMap R (Localization.Away g)) =
      q.comap (algebraMap R S) := by
    rw [← hq, ← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]
  exact fibre_transport_same_base (q₁.comap (algebraMap R (Localization.Away g)))
    q hp.symm g q₁ rfl hq (fibre_neighborhood_rebase hp.symm q rfl hci)

end Algebra
