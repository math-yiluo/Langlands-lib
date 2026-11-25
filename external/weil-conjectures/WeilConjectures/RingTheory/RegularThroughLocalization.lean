/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.GeometricRegularityFieldIso

/-!
# Regularity through localization

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07PT, line 12392
(blueprint: lem-weil-pbc-regular-through-localization).
-/

@[expose] public section

universe u v w

namespace RingHom

/-- If a ring map out of a localization is regular after precomposition with the
localization map, then the map out of the localization is regular. Here ψ is
`algebraMap A' C` and the composite ψ ∘ λ is `algebraMap A C` through
`IsScalarTower A A' C`. Source: Stacks
Project, More on Algebra, proof of Lemma Tag 07PT, line 12392
(blueprint: lem-weil-pbc-regular-through-localization).

Proof:
1. Flatness of the composite implies flatness of C over A' by
`lem-weil-pbc-flat-over-localization` with M = C, using the localization axioms;
thus ψ is flat (`def-weil-pbc-flat-ring-map`, Algebra 00HT (2)).
2. For a prime q' of A', its inverse image q in A is prime and misses W.
The localization induces an A-algebra isomorphism σ from κ(q) to κ(q') = k
(identification of residue fields under localization, Algebra 00E3, 00C9).
3. The identity maps on C and k are module localizations at W: denominators
act invertibly and the fraction and kernel conditions hold with denominator 1.
By `lem-weil-pbc-localization-tensor-product` (Algebra 00DL), the canonical map
C ⊗[A] k → C ⊗[A'] k is a localization. W already acts invertibly on its source,
so that map is bijective and respects multiplication, the unit, and k-scalars.
4. Tensoring σ with the identity on C and composing with the map of step 3
gives a ring isomorphism Θ from the composite's fibre to ψ's fibre, compatible
with σ on residue-field scalars (`def-weil-pbc-localization-at-prime`).
5. The composite's fibre is Noetherian and geometrically regular. Transport
Noetherianity across Θ. A finite purely inseparable extension k'/k is also
such an extension of κ(q) via σ. The scalar-compatible Θ induces mutually
inverse maps between the two base-changed fibre rings. Their regularity is
therefore identical (`def-weil-pbc-noetherian-ring`,
`def-weil-pbc-finite-purely-inseparable-extension`, `def-weil-regular-scheme`;
Algebra 0382). Hence ψ's fibre is geometrically regular over k.
6. Flatness from step 1 and the fibre conditions from steps 2–5 give regularity
of ψ by `theorem-finite-etale-covers-proper-henselian--2` (More on Algebra 07BZ).
-/
theorem isRegular_of_comp_algebraMap_localization
    {A : Type u} {A' : Type v} {C : Type w}
    [CommRing A] [CommRing A'] [CommRing C]
    [Algebra A A'] [Algebra A' C] [Algebra A C] [IsScalarTower A A' C]
    (W : Submonoid A) [IsLocalization W A']
    (hψ : (algebraMap A C).IsRegular) :
    (algebraMap A' C).IsRegular := by
  rw [RingHom.IsRegular, toAlgebra_algebraMap] at hψ ⊢
  refine ⟨?_, ?_⟩
  · rw [RingHom.flat_algebraMap_iff]
    have hflat : Module.Flat A C := (RingHom.flat_algebraMap_iff).mp hψ.1
    exact (Module.flat_iff_of_isLocalization A' W C).mpr hflat
  · intro q' hq'
    let q := q'.comap (algebraMap A A')
    have : q.IsPrime := Ideal.IsPrime.comap (algebraMap A A')
    let σ : q.ResidueField ≃ₐ[A] q'.ResidueField :=
      AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ q q' (Algebra.ofId A A') rfl)
        ((RingHom.surjectiveOnStalks_of_isLocalization W A').residueFieldMap_bijective
          q q' rfl)
    let e₁ := Algebra.TensorProduct.congr σ (AlgEquiv.refl : C ≃ₐ[A] C)
    have : TensorProduct.CompatibleSMul A A' q'.ResidueField C :=
      IsLocalization.tensorProduct_compatibleSMul W A' q'.ResidueField C
    let e₂ := Algebra.TensorProduct.equivOfCompatibleSMul A A' q'.ResidueField
      q'.ResidueField C
    exact Algebra.isGeometricallyRegular_of_fieldIso σ.toRingEquiv
      (e₁.toRingEquiv.trans e₂.symm.toRingEquiv) (by
        intro x y
        induction y using TensorProduct.inductionOn with
        | tmul a c =>
          change e₂.symm (σ (x * a) ⊗ₜ[A] c) =
            σ x • e₂.symm (σ a ⊗ₜ[A] c)
          simp [e₂, Algebra.TensorProduct.equivOfCompatibleSMul,
            Algebra.TensorProduct.mapOfCompatibleSMul,
            Algebra.smul_def]
        | add a b ha hb => simp_all) (hψ.2 q)

end RingHom
