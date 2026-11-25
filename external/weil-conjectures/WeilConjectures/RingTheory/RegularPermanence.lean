/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.GeometricallyRegularDescent

/-!
# Permanence of regular ring maps

Source: Stacks Project, More on Algebra, Lemma Tag 07NT
(blueprint: lem-weil-pbc-regular-permanence).
-/

@[expose] public section

universe u v w

namespace RingHom

/-- Regularity descends along a flat map inducing a surjection on spectra.
Source: Stacks Project, More on Algebra, Lemma Tag 07NT; proof via Algebra Lemmas 039V and 07NH
(blueprint: lem-weil-pbc-regular-permanence).

Proof: Since `B → C` is flat and its prime-spectrum map is surjective, it is faithfully flat.
The already proved `Module.Flat.of_flat_of_faithfullyFlat` descends flatness of `A → B`.
For each prime `p` of `A`, tensor cancellation identifies `p.Fiber C` with
`(p.Fiber B) ⊗[B] C`, compatibly with the fibre map `1 ⊗ (B → C)`.
Mathlib's faithfully flat base-change instance makes this a faithfully flat extension
of `p.Fiber B`. Geometric regularity, including Noetherianity, descends along this map
by `Algebra.isGeometricallyRegular_of_faithfullyFlat`. Together with flatness, this
is exactly regularity of `A → B`.
-/
theorem isRegular_of_isRegular_comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hcomp : (algebraMap A C).IsRegular)
    (hflat : (algebraMap B C).Flat)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B C))) :
    (algebraMap A B).IsRegular := by
  have hBC : Module.FaithfullyFlat B C :=
    (faithfullyFlat_algebraMap_iff).mp
      (FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hflat, hsurj⟩)
  rw [IsRegular, toAlgebra_algebraMap] at hcomp ⊢
  refine ⟨?_, ?_⟩
  · have : Module.Flat A C := flat_algebraMap_iff.mp hcomp.1
    exact flat_algebraMap_iff.mpr (Module.Flat.of_flat_of_faithfullyFlat (C := C))
  · intro p hp
    let f : p.Fiber B →ₐ[p.ResidueField] p.Fiber C :=
      Algebra.TensorProduct.lTensor p.ResidueField (IsScalarTower.toAlgHom A B C)
    let : Algebra (p.Fiber B) (p.Fiber C) := f.toRingHom.toAlgebra
    have : IsScalarTower p.ResidueField (p.Fiber B) (p.Fiber C) :=
      IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    have : Module.FaithfullyFlat (p.Fiber B) (p.Fiber C) := by
      let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
      let e : p.Fiber C ≃ₐ[p.Fiber B] TensorProduct B (p.Fiber B) C :=
        { __ := (Algebra.IsPushout.cancelBaseChangeAlg A p.ResidueField B (p.Fiber B) C).symm,
          commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor
            A B C p.ResidueField) x) }
      exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv
    exact Algebra.isGeometricallyRegular_of_faithfullyFlat
      p.ResidueField (p.Fiber B) (p.Fiber C) (hcomp.2 p)

end RingHom
