/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.SingularIdealsRelativeBound
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth

@[expose] public section

universe u v w
namespace Algebra

/-- Absolute singular-ideal containment from an annihilator bound.

This is the smooth-composition paragraph in Stacks Project, Tag 07CT. The relative
containment makes every prime outside the extended singular ideal smooth for `D → B`; smooth
base change and composition then make it smooth for `R → B`, and the radical zero-locus
criterion gives the absolute inclusion. The proof is postponed while the requisite
smooth-composition lemmas are formalized.
(blueprint: lem-weil-pbc-singular-ideals-absolute-bound)
-/
theorem singularIdeal_map_le_absolute_of_annihilator_bound
    (R : Type u) (D : Type v) (B : Type w)
    [CommRing R] [CommRing D] [CommRing B]
    [Algebra R D] [Algebra R B] [IsNoetherianRing R] [FinitePresentation R D]
    (dB : D →ₐ[R] B)
    (hfp : @FinitePresentation D B _ _ dB.toRingHom.toAlgebra)
    (π : R) (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hbound : Ideal.span (dB ''
      {r : D | ∀ x : D, (algebraMap R D π) ^ 2 * x = 0 →
        r * algebraMap R D π * x = 0}) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra) :
    Ideal.map dB.toRingHom (singularIdeal R D) ≤ singularIdeal R B := by
  let : Algebra D B := dB.toRingHom.toAlgebra
  have : IsScalarTower R D B := IsScalarTower.of_algebraMap_eq' dB.comp_algebraMap.symm
  have hrel := singularIdeal_map_le_relative_of_annihilator_bound R D B dB hfp π hR hbound
  unfold singularIdeal
  refine (Ideal.map_radical_le dB.toRingHom).trans (Ideal.radical_mono ?_)
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro f hf
  apply Ideal.subset_span
  change Smooth R (Localization.Away (dB f))
  let Df := Localization.Away f
  let Bf := Localization.Away (dB f)
  let : Algebra Df Bf := (Localization.awayMap dB.toRingHom f).toAlgebra
  have : IsScalarTower D Df Bf := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap D Bf x =
      IsLocalization.Away.map Df Bf dB.toRingHom f (algebraMap D Df x)
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have : IsScalarTower R Df Bf := IsScalarTower.to₁₃₄ R D Df Bf
  have : Smooth R Df := hf
  have : Smooth D Bf := smooth_localization_of_mem_singularIdeal D B (dB f)
    (hrel (Ideal.mem_map_of_mem dB.toRingHom (Ideal.le_radical (Ideal.subset_span hf))))
  have : FinitePresentation Df Bf :=
    FinitePresentation.of_restrict_scalars_finitePresentation D Df Bf
  have : IsLocalization ((Submonoid.powers f).map (algebraMap D B)) Bf := by
    change IsLocalization ((Submonoid.powers f).map dB.toRingHom) Bf
    infer_instance
  have : FormallySmooth Df Bf := FormallySmooth.localization_base (Submonoid.powers f)
  have : Smooth Df Bf := ⟨inferInstance, inferInstance⟩
  exact Smooth.comp R Df Bf

end Algebra
