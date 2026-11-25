/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.PairHenselizationFiberLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.RingTheory.GeometricRegularitySeparableExtension
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Regular fibres after an ind-etale extension

Source: Stacks Project, More on Algebra, Tag 0AH3, final fibre calculation,
using Tag 0AH1 and Algebra Tag 07QH.
(blueprint: lem-weil-pbc-pair-henselization-regular-fibers).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

private theorem regular_localization (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] [IsRegularRing R] :
    IsRegularRing S := by
  apply isRegularRing_of_localization R S M (algebraMap R S)
  · exact IsLocalization.map_units S
  · intro y
    obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj M y
    obtain ⟨z, hz⟩ := (IsLocalization.map_units S s).exists_right_inv
    refine ⟨r, s, z, IsUnit.of_mul_eq_one_right _ hz, hz, ?_⟩
    calc
      y = y * (algebraMap R S s * z) := by rw [hz, mul_one]
      _ = algebraMap R S r * z := by rw [← mul_assoc, hy]
  · intro r hr
    obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists M S).mp
      (show algebraMap R S r = algebraMap R S 0 by simpa only [map_zero] using hr)
    exact ⟨s, by simpa only [mul_zero] using hs⟩

private theorem geometricallyRegular_localization (k R S : Type u)
    [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra R S] [IsScalarTower k R S] (M : Submonoid R) [IsLocalization M S]
    (hR : Algebra.IsGeometricallyRegular k R) :
    Algebra.IsGeometricallyRegular k S := by
  have : IsNoetherianRing R := hR.1
  refine ⟨IsLocalization.isNoetherianRing M S hR.1, ?_⟩
  intro K _ _ _ _
  have : IsRegularRing (TensorProduct k K R) := hR.2 K
  let f : TensorProduct k K R →ₐ[K] TensorProduct k K S :=
    Algebra.TensorProduct.lTensor K (IsScalarTower.toAlgHom k R S)
  let : Algebra (TensorProduct k K R) (TensorProduct k K S) := f.toRingHom.toAlgebra
  have : IsScalarTower K (TensorProduct k K R) (TensorProduct k K S) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K)))
      (TensorProduct k K S) := by
    apply IsLocalization.tensorProduct_tensorProduct_right k K M S
    ext r
    change f (TensorProduct.tmul k 1 r) = TensorProduct.tmul k 1 (algebraMap R S r)
    simp [f]
  exact regular_localization (TensorProduct k K R) (TensorProduct k K S)
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K)))

/-- A map out of a Noetherian henselization colimit has geometrically regular fibres
if its composite with the base structure map is regular. No completion, henselian
pair, or G-ring hypothesis is involved in this fibre calculation.

Source: Stacks Project, More on Algebra, Tag 0AH3, displayed product-of-fibres
calculation and its following paragraph; Tag 0AH1; Algebra Tag 07QH.
(blueprint: lem-weil-pbc-pair-henselization-regular-fibers).

Proof: The indexing category is filtered by Tag 0A02. Regard its diagram and colimit
as A-algebras, and apply Tag 0AH1. For a prime q of B = c.pt.right, with contraction
p in A, this gives B tensor_A kappa(p) as a finite product of residue fields at all
primes above p, and kappa(q)/kappa(p) is separable algebraic. Tensor this product
with C over B. The resulting algebra kappa(p) tensor_A C is the finite product
of kappa(q_i) tensor_B C. The projection onto the q component is localization at
an idempotent. Regularity of the composite makes the product geometrically regular
over kappa(p); localization commutes with every finite purely inseparable base
extension, so its q component is geometrically regular over kappa(p) too. Its
Noetherianity follows as a quotient of the Noetherian product. Apply Tag 07QH to
replace kappa(p) by its separable algebraic extension kappa(q). This proves the
required geometric regularity. If the product has no factors, there is no prime q
to check; a zero component has vacuous regularity and causes no exception. -/
theorem pair_henselization_regular_fibers
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun D : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) [IsNoetherianRing c.pt.right]
    (C : Type u) [CommRing C] (g : c.pt.right →+* C)
    (hregular : (g.comp c.pt.hom.hom).IsRegular) :
    letI := g.toAlgebra
    ∀ (q : Ideal c.pt.right) [q.IsPrime],
      Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := by
  let : Algebra A c.pt.right := c.pt.hom.hom.toAlgebra
  let : Algebra c.pt.right C := g.toAlgebra
  let : Algebra A C := (g.comp c.pt.hom.hom).toAlgebra
  have : IsScalarTower A c.pt.right C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro q hq
  let p := q.comap c.pt.hom.hom
  let ρ : p.ResidueField →ₐ[A] q.ResidueField :=
    Ideal.ResidueField.mapₐ p q (Algebra.ofId A c.pt.right) rfl
  let : Algebra p.ResidueField q.ResidueField := ρ.toRingHom.toAlgebra
  have : IsScalarTower p.ResidueField q.ResidueField (q.Fiber C) := inferInstance
  have : IsScalarTower A p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' ρ.comp_algebraMap.symm
  have : IsScalarTower A p.ResidueField (q.Fiber C) :=
    IsScalarTower.to₁₂₄ A p.ResidueField q.ResidueField (q.Fiber C)
  let φ : p.Fiber C →ₐ[p.ResidueField] q.Fiber C :=
    Algebra.TensorProduct.lift (Algebra.ofId p.ResidueField (q.Fiber C))
      (AlgHom.restrictScalars A
        (Algebra.TensorProduct.includeRight : C →ₐ[c.pt.right] q.Fiber C))
      (fun _ _ ↦ Commute.all _ _)
  let : Algebra (p.Fiber C) (q.Fiber C) := φ.toRingHom.toAlgebra
  have : IsScalarTower p.ResidueField (p.Fiber C) (q.Fiber C) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  obtain ⟨hsep, M, hloc⟩ := pair_henselization_fiber_localization A I c hc C g q
    ρ rfl φ.toRingHom (by
      intro x y
      change (Algebra.TensorProduct.lift _ _ _) (TensorProduct.tmul A x y) = _
      rw [Algebra.TensorProduct.lift_tmul]
      change (TensorProduct.tmul c.pt.right
        (algebraMap p.ResidueField q.ResidueField x) 1) *
        (TensorProduct.tmul c.pt.right 1 y) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl)
  have : Algebra.IsSeparable p.ResidueField q.ResidueField := hsep
  have : IsLocalization M (q.Fiber C) := hloc
  have hP : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber C) := hregular.2 p
  have hQ := geometricallyRegular_localization p.ResidueField (p.Fiber C) (q.Fiber C) M hP
  have : IsNoetherianRing (q.Fiber C) := hQ.1
  exact Algebra.isGeometricallyRegular_of_isSeparable
    p.ResidueField q.ResidueField (q.Fiber C) hQ

end RingTheory
