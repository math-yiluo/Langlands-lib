/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The open–closed sequence of pro-étale sheaves of modules

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. For
pro-étale sheaves of modules over a ring `R`:

* the unit `N ⟶ j^* j_! N` of `j_! ⊣ j^*` is an isomorphism
  (`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekUpperStarAdjunction_unit`,
  blueprint `proposition-extension-zero-restriction-closed-subscheme--7`);
* every sheaf `M` sits in the short exact sequence `0 ⟶ j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ 0`
  formed by the counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`
  (`AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex`, blueprint
  `proposition-extension-zero-restriction-closed-subscheme`).

The exactness is checked after applying `j^*` and `i^*`, which are exact and jointly detect
zero objects (`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}}

section OpenUnit

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--7` (subsection
`proposition-extension-zero-restriction-closed-subscheme`): for an open immersion `j`, the unit
`N ⟶ j^* j_! N` of the extension-by-zero adjunction `j_! ⊣ j^*` is an isomorphism on pro-étale
sheaves. Indeed `j_!` is fully faithful
(`AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek`): on objects over `U` the
presheaf extension by zero is the identity. -/
instance isIso_openImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (openImmersionLowerShriekUpperStarAdjunction A j).unit :=
  (openImmersionLowerShriekUpperStarAdjunction A j).unit_isIso_of_L_fully_faithful

/-- `j^*` of the counit `j_! j^* M ⟶ M` is an isomorphism, by a triangle identity. -/
instance isIso_upperStar_map_openImmersionLowerShriekUpperStarAdjunction_counit
    (M : Sheaf (ProEt.topology X) A) :
    IsIso ((j)^*[A].map ((openImmersionLowerShriekUpperStarAdjunction A j).counit.app M)) := by
  have h := (openImmersionLowerShriekUpperStarAdjunction A j).right_triangle_components (Y := M)
  rw [← IsIso.inv_eq_of_hom_inv_id h]
  infer_instance

end OpenUnit

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

omit [IsOpenImmersion j] in
/-- A short complex of pro-étale sheaves of modules is short exact as soon as its restrictions
to a closed immersion and to its quasi-compact open complement are. -/
theorem shortExact_of_shortExact_map_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (S : ShortComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)))
    (hi : (S.map (i)^*[ModuleCat.{u + 1} R]).ShortExact)
    (hj : (S.map (j)^*[ModuleCat.{u + 1} R]).ShortExact) : S.ShortExact := by
  have hker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X), (S.map (g)^*[ModuleCat.{u + 1} R]).ShortExact →
      IsZero ((g)^*[ModuleCat.{u + 1} R].obj (kernel S.f)) := fun g hg ↦
    have : Mono ((g)^*[ModuleCat.{u + 1} R].map S.f) := hg.mono_f
    (isZero_kernel_of_mono ((g)^*[ModuleCat.{u + 1} R].map S.f)).of_iso
      (PreservesKernel.iso _ S.f)
  have hcoker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X), (S.map (g)^*[ModuleCat.{u + 1} R]).ShortExact →
      IsZero ((g)^*[ModuleCat.{u + 1} R].obj (cokernel S.g)) := fun g hg ↦
    have : Epi ((g)^*[ModuleCat.{u + 1} R].map S.g) := hg.epi_g
    (isZero_cokernel_of_epi ((g)^*[ModuleCat.{u + 1} R].map S.g)).of_iso
      (PreservesCokernel.iso _ S.g)
  have hhom : ∀ {Y : Scheme.{u}} (g : Y ⟶ X), (S.map (g)^*[ModuleCat.{u + 1} R]).ShortExact →
      IsZero ((g)^*[ModuleCat.{u + 1} R].obj S.homology) := fun g hg ↦
    ((S.map _).exact_iff_isZero_homology.1 hg.exact).of_iso (S.mapHomologyIso _).symm
  have : Mono S.f := Preadditive.mono_of_isZero_kernel _
    (isZero_of_isZero_upperStar_of_isCompl i j hij _ (hker i hi) (hker j hj))
  have : Epi S.g := Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar_of_isCompl i j hij _ (hcoker i hi) (hcoker j hj))
  exact ⟨S.exact_iff_isZero_homology.2
    (isZero_of_isZero_upperStar_of_isCompl i j hij _ (hhom i hi) (hhom j hj))⟩

variable (R) in
/-- The open–closed short complex `j_! j^* M ⟶ M ⟶ i_* i^* M` of a pro-étale sheaf of modules,
formed by the counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`; the composite vanishes since
`j^* i_* = 0`. -/
noncomputable def openClosedShortComplex
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    ShortComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) where
  f := (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app M
  g := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M
  zero := by
    apply ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).homEquiv
      _ _).injective
    exact (isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint _).eq_of_tgt _ _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`lemma-local-cohomology-right-adjoint--1`), for the constant sheaf of rings `R`: let `i : Z ⟶ X` be
a closed immersion with quasi-compact open complement `j : U ⟶ X`. For every pro-étale sheaf of
`R`-modules `M` the sequence `0 ⟶ j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ 0`, formed by the counit of
`j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`, is exact.

The other assertions of the node are: `j^*` and `j_!` are exact with `j_! ⊣ j^*`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`), with invertible
unit (`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekUpperStarAdjunction_unit`);
`i_*` is exact (`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`), with
invertible counit (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`), and
`j^* i_* = 0` (`AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint`).

The sequence is checked to be exact after `j^*`, where it becomes
`j^* M ≅ j^* M ⟶ 0`, and after `i^*`, where it becomes `0 ⟶ i^* M ≅ i^* i_* i^* M`
(`AlgebraicGeometry.ProEtale.shortExact_of_shortExact_map_upperStar_of_isCompl`). -/
theorem shortExact_openClosedShortComplex
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (openClosedShortComplex R i j hij M).ShortExact := by
  refine shortExact_of_shortExact_map_upperStar_of_isCompl i j hij _ ?_ ?_
  · -- after `i^*`: `0 ⟶ i^* M ≅ i^* i_* i^* M`
    have hz : IsZero ((i)^*[ModuleCat.{u + 1} R].obj ((j)_!open[ModuleCat.{u + 1} R].obj
        ((j)^*[ModuleCat.{u + 1} R].obj M))) :=
      isZero_upperStar_openImmersionLowerShriek _ j i
        (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) _
    have : IsIso ((i)^*[ModuleCat.{u + 1} R].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M)) := by
      have h := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).left_triangle_components M
      have : IsIso ((i)^*[ModuleCat.{u + 1} R].map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M) ≫
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit.app _) := by
        rw [h]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit.app _)
    have hf : ((openClosedShortComplex R i j hij M).map (i)^*[ModuleCat.{u + 1} R]).f = 0 :=
      hz.eq_of_src _ _
    have : Mono ((openClosedShortComplex R i j hij M).map (i)^*[ModuleCat.{u + 1} R]).f :=
      ⟨fun a b _ ↦ hz.eq_of_tgt a b⟩
    have : Epi ((openClosedShortComplex R i j hij M).map (i)^*[ModuleCat.{u + 1} R]).g :=
      inferInstanceAs (Epi ((i)^*[ModuleCat.{u + 1} R].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M)))
    have hgm : Mono ((openClosedShortComplex R i j hij M).map (i)^*[ModuleCat.{u + 1} R]).g :=
      inferInstanceAs (Mono ((i)^*[ModuleCat.{u + 1} R].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M)))
    exact ⟨(ShortComplex.exact_iff_mono _ hf).2 hgm⟩
  · -- after `j^*`: `j^* M ≅ j^* M ⟶ 0`
    have hz : IsZero ((j)^*[ModuleCat.{u + 1} R].obj ((i)_*[ModuleCat.{u + 1} R].obj
        ((i)^*[ModuleCat.{u + 1} R].obj M))) :=
      isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint _
    have hg : ((openClosedShortComplex R i j hij M).map (j)^*[ModuleCat.{u + 1} R]).g = 0 :=
      hz.eq_of_tgt _ _
    have : Epi ((openClosedShortComplex R i j hij M).map (j)^*[ModuleCat.{u + 1} R]).g :=
      ⟨fun a b _ ↦ hz.eq_of_src a b⟩
    have : Mono ((openClosedShortComplex R i j hij M).map (j)^*[ModuleCat.{u + 1} R]).f :=
      inferInstanceAs (Mono ((j)^*[ModuleCat.{u + 1} R].map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app M)))
    have hfe : Epi ((openClosedShortComplex R i j hij M).map (j)^*[ModuleCat.{u + 1} R]).f :=
      inferInstanceAs (Epi ((j)^*[ModuleCat.{u + 1} R].map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app M)))
    exact ⟨(ShortComplex.exact_iff_epi _ hg).2 hfe⟩

section BaseChange

variable {Z' U' X' : Scheme.{u}} (g : X' ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i']
  (j' : U' ⟶ X') [IsOpenImmersion j'] [QuasiCompact j'] (gZ : Z' ⟶ Z) (gU : U' ⟶ U)

omit [IsClosedImmersion i] [QuasiCompact j] [IsClosedImmersion i'] [IsOpenImmersion j']
  [QuasiCompact j'] in
/-- The pullback along `g` of a sheaf supported on `Z` vanishes on the preimage `U'` of the
complement of `Z`. -/
lemma isZero_upperStar_upperStar_lowerStar (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (hj : j' ≫ g = gU ≫ j) (G : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R)) :
    IsZero ((j')^*[ModuleCat.{u + 1} R].obj
      ((g)^*[ModuleCat.{u + 1} R].obj ((i)_*[ModuleCat.{u + 1} R].obj G))) := by
  have := isZero_upperStar_lowerStar_of_disjoint (ModuleCat.{u + 1} R) i j hij.disjoint G
  refine ((gU)^*[ModuleCat.{u + 1} R].map_isZero this).of_iso ?_
  exact ((upperStarComp _ j' g).app _).symm ≪≫
    eqToIso (by rw [hj]) ≪≫ (upperStarComp _ gU j).app _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4) for the closed
immersion: for a morphism `g : X' ⟶ X` and the base changes `i' : Z' ⟶ X'`, `gZ : Z' ⟶ Z`,
`j' : U' ⟶ X'`, `gU : U' ⟶ U`, there is a canonical isomorphism `g^* i_* G ≅ i'_* gZ^* G`. Both
sides are supported on `Z'`, and their restrictions to `Z'` are `gZ^* i^* i_* G ≅ gZ^* G` by the
counit isomorphism `AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`. The
corresponding isomorphism `g^* j_! ≅ j'_! gU^*` is
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekBaseChangeIso`. -/
noncomputable def upperStarLowerStarClosedBaseChangeIso
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))
    (hi : i' ≫ g = gZ ≫ i) (hj : j' ≫ g = gU ≫ j)
    (G : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R)) :
    (g)^*[ModuleCat.{u + 1} R].obj ((i)_*[ModuleCat.{u + 1} R].obj G) ≅
      (i')_*[ModuleCat.{u + 1} R].obj ((gZ)^*[ModuleCat.{u + 1} R].obj G) :=
  have h := isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i' j' hij' _
    (isZero_upperStar_upperStar_lowerStar i j g j' gU hij hj G)
  @asIso _ _ _ _ ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i').unit.app _) h ≪≫
    (i')_*[ModuleCat.{u + 1} R].mapIso (((upperStarComp _ i' g).app _).symm ≪≫
      eqToIso (by rw [hi]) ≪≫ (upperStarComp _ gZ i).app _ ≪≫
      (gZ)^*[ModuleCat.{u + 1} R].mapIso
        (asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit.app G)))

omit [IsClosedImmersion i] [QuasiCompact j] [IsClosedImmersion i'] [IsOpenImmersion j']
  [QuasiCompact j'] in
/-- The pullback along `g` of an extension by zero from `U` vanishes on the preimage `Z'` of the
complement of `U`. -/
lemma isZero_upperStar_upperStar_openImmersionLowerShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (hi : i' ≫ g = gZ ≫ i)
    (N : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) :
    IsZero ((i')^*[ModuleCat.{u + 1} R].obj
      ((g)^*[ModuleCat.{u + 1} R].obj ((j)_!open[ModuleCat.{u + 1} R].obj N))) := by
  have := isZero_upperStar_openImmersionLowerShriek (ModuleCat.{u + 1} R) j i
    (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) N
  refine ((gZ)^*[ModuleCat.{u + 1} R].map_isZero this).of_iso ?_
  exact ((upperStarComp _ i' g).app _).symm ≪≫
    eqToIso (by rw [hi]) ≪≫ (upperStarComp _ gZ i).app _

omit [IsClosedImmersion i] [QuasiCompact j] [IsClosedImmersion i'] [QuasiCompact j'] in
/-- The pullback along `g` of the counit `j_! j^* M ⟶ M`, followed by the unit
`g^* M ⟶ i'_* i'^* g^* M`, vanishes. -/
lemma upperStar_map_counit_comp_unit_eq_zero
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (hi : i' ≫ g = gZ ≫ i)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (g)^*[ModuleCat.{u + 1} R].map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app M) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i').unit.app
        ((g)^*[ModuleCat.{u + 1} R].obj M) = 0 := by
  have h := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i').unit.naturality
    ((g)^*[ModuleCat.{u + 1} R].map
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app M))
  dsimp at h
  rw [h, (isZero_upperStar_upperStar_openImmersionLowerShriek i j g i' gZ hij hi _).eq_of_src
      ((i')^*[ModuleCat.{u + 1} R].map _) 0, Functor.map_zero, comp_zero]

omit [IsClosedImmersion i] [QuasiCompact j] [IsClosedImmersion i'] [QuasiCompact j'] in
/-- The counit `j'_! j'^* g^* M ⟶ g^* M`, followed by the pullback along `g` of the unit
`M ⟶ i_* i^* M`, vanishes. -/
lemma counit_comp_upperStar_map_unit_eq_zero
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (hj : j' ≫ g = gU ≫ j)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j').counit.app
        ((g)^*[ModuleCat.{u + 1} R].obj M) ≫
      (g)^*[ModuleCat.{u + 1} R].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M) = 0 := by
  have h :=
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j').counit.naturality
    ((g)^*[ModuleCat.{u + 1} R].map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M))
  dsimp at h
  rw [← h, (isZero_upperStar_upperStar_lowerStar i j g j' gU hij hj _).eq_of_tgt
      ((j')^*[ModuleCat.{u + 1} R].map _) 0, Functor.map_zero, zero_comp]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4) for the sequence:
for a morphism `g : X' ⟶ X` and the base changes `i' : Z' ⟶ X'`, `gZ : Z' ⟶ Z`, `j' : U' ⟶ X'`,
`gU : U' ⟶ U`, the pullback `g^*` carries the open–closed sequence
`0 ⟶ j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ 0` of `M` to the open–closed sequence of `g^* M`: there is an
isomorphism of short complexes which is the identity on the middle term `g^* M`
(`AlgebraicGeometry.ProEtale.openClosedShortComplexBaseChangeIso_hom_τ₂`).

Both are short exact (`g^*` is exact), so it suffices that the first map of each composes to zero
with the second map of the other: `i'^* g^* j_! = 0` and `j'^* g^* i_* = 0` since `Z'` and `U'`
lie over `Z` and `U`. -/
noncomputable def openClosedShortComplexBaseChangeIso
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))
    (hi : i' ≫ g = gZ ≫ i) (hj : j' ≫ g = gU ≫ j)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (openClosedShortComplex R i j hij M).map (g)^*[ModuleCat.{u + 1} R] ≅
      openClosedShortComplex R i' j' hij' ((g)^*[ModuleCat.{u + 1} R].obj M) :=
  ShortComplex.ShortExact.isoOfCompEqZero
    ((shortExact_openClosedShortComplex i j hij M).map_of_exact _)
    (shortExact_openClosedShortComplex i' j' hij' _)
    (Iso.refl ((g)^*[ModuleCat.{u + 1} R].obj M))
    (by rw [Iso.refl_hom]; erw [Category.id_comp]
        exact upperStar_map_counit_comp_unit_eq_zero i j g i' gZ hij hi M)
    (by rw [Iso.refl_inv]; erw [Category.id_comp]
        exact counit_comp_upperStar_map_unit_eq_zero i j g j' gU hij hj M)

@[simp]
lemma openClosedShortComplexBaseChangeIso_hom_τ₂
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))
    (hi : i' ≫ g = gZ ≫ i) (hj : j' ≫ g = gU ≫ j)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (openClosedShortComplexBaseChangeIso i j g i' j' gZ gU hij hij' hi hj M).hom.τ₂ = 𝟙 _ :=
  rfl

end BaseChange

end ProEtale

end AlgebraicGeometry
