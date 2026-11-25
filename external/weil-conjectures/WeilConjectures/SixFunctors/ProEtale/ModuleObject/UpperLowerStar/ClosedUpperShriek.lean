/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite

/-!
# Sections with support and the exceptional inverse image along a closed immersion

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` an open
immersion onto the complement of its range. On module objects over `Λ_X = condensedRingObj Λ X`,
the sections with support in `Z` form the kernel

`Γ_Z N = ker(N ⟶ j_* j^* N)`

of the unit of `j^* ⊣ j_*` (`ProEtale.CondensedRing.sectionsWithSupport`), and
`i^!₀ N = i^* Γ_Z N` (`ProEtale.CondensedRing.closedUpperShriek`). It is right adjoint to the
pushforward `i_*` (`ProEtale.CondensedRing.lowerStarClosedUpperShriekAdjunction`). This is the
module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion`, used for
blueprint `lemma-sections-support-closed-subscheme`.

The adjunction is the composite of two adjunctions: a morphism `i_* P ⟶ N` is killed by the unit
`N ⟶ j_* j^* N` (since `j^* i_* P = 0`), so factors uniquely through `Γ_Z N`; and `Γ_Z N`,
which vanishes on `U`, is `i_* i^* Γ_Z N` (`i_*` is fully faithful with essential image the
module objects vanishing on `U`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Definition

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

/-- The module object `Γ_Z N = ker(N ⟶ j_* j^* N)` of sections of `N` with support in the
complement of `j`, the kernel of the unit of `j^* ⊣ j_*`. -/
noncomputable def sectionsWithSupport :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) where
  obj N := kernel ((upperStarLowerStarAdjunction Λ j).unit.app N)
  map φ := kernel.map _ _ φ ((j)_*⟦Λ⟧.map ((j)^*⟦Λ⟧.map φ))
    ((upperStarLowerStarAdjunction Λ j).unit.naturality φ).symm
  map_id N := equalizer.hom_ext (by simp)
  map_comp φ ψ := equalizer.hom_ext (by simp)

instance : (sectionsWithSupport Λ j).Additive where
  map_add {_ _ f g} := equalizer.hom_ext (by
    dsimp only [sectionsWithSupport]
    erw [kernel.lift_ι, Preadditive.add_comp, kernel.lift_ι, kernel.lift_ι, Preadditive.comp_add])

/-- The exceptional inverse image `i^!₀ N = i^* Γ_Z N` of module objects along a closed immersion
`i` with open complement `j`. -/
noncomputable def closedUpperShriek :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) :=
  sectionsWithSupport Λ j ⋙ (i)^*⟦Λ⟧

instance : (closedUpperShriek Λ i j).Additive := by
  unfold closedUpperShriek
  infer_instance

/-- The inclusion `Γ_Z N ⟶ N`. -/
noncomputable def sectionsWithSupportι : sectionsWithSupport Λ j ⟶ 𝟭 _ where
  app N := kernel.ι _
  naturality _ _ φ := by simp [sectionsWithSupport]

@[reassoc (attr := simp)]
lemma sectionsWithSupportι_app_comp_unit_app
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (sectionsWithSupportι Λ j).app N ≫ (upperStarLowerStarAdjunction Λ j).unit.app N = 0 :=
  kernel.condition _

/-- The counit `j^* j_* ⟶ 𝟭` of `j^* ⊣ j_*` on module objects along an open immersion is an
isomorphism: in the adjoint triple `j_! ⊣ j^* ⊣ j_*` the unit of the first adjunction is an
isomorphism. -/
lemma isIso_upperStarLowerStarAdjunction_counit_of_isOpenImmersion [IsOpenImmersion j] :
    IsIso (upperStarLowerStarAdjunction Λ j).counit :=
  (Adjunction.Triple.mk (openImmersionLowerShriekUpperStarAdjunction Λ j)
    (upperStarLowerStarAdjunction Λ j)).isIso_unit_iff_isIso_counit.1
    (inferInstance : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit)

attribute [local instance] isIso_upperStarLowerStarAdjunction_counit_of_isOpenImmersion

/-- `Γ_Z N` vanishes on `U`: `j^*` is exact and `j^*` of the unit `N ⟶ j_* j^* N` is an
isomorphism, inverse to the counit. -/
lemma isZero_upperStar_sectionsWithSupport [IsOpenImmersion j]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsZero ((j)^*⟦Λ⟧.obj ((sectionsWithSupport Λ j).obj N)) := by
  set adj := upperStarLowerStarAdjunction Λ j
  have : IsIso ((j)^*⟦Λ⟧.map (adj.unit.app N)) := by
    have : IsIso ((j)^*⟦Λ⟧.map (adj.unit.app N) ≫ adj.counit.app ((j)^*⟦Λ⟧.obj N)) := by
      rw [adj.left_triangle_components N]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  exact (isZero_kernel_of_mono ((j)^*⟦Λ⟧.map (adj.unit.app N))).of_iso
    (PreservesKernel.iso _ _)

/-- The module objects on `X` vanishing on `U`. -/
def supportedAway :
    ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  fun F ↦ IsZero ((j)^*⟦Λ⟧.obj F)

/-- `Γ_Z`, as a functor to the module objects vanishing on `U`. -/
noncomputable def sectionsWithSupportLift [IsOpenImmersion j] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      (supportedAway Λ j).FullSubcategory :=
  (supportedAway Λ j).lift (sectionsWithSupport Λ j) (isZero_upperStar_sectionsWithSupport Λ j)

/-- A morphism `F ⟶ N` from a module object vanishing on `U` is killed by the unit
`N ⟶ j_* j^* N`. -/
lemma comp_unit_app_eq_zero
    {F N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hF : supportedAway Λ j F) (f : F ⟶ N) :
    f ≫ (upperStarLowerStarAdjunction Λ j).unit.app N = 0 := by
  have h := (upperStarLowerStarAdjunction Λ j).unit.naturality f
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h
  rw [h, (((j)_*⟦Λ⟧).map_isZero hF).eq_of_tgt
    ((upperStarLowerStarAdjunction Λ j).unit.app F) 0, zero_comp]

@[reassoc (attr := simp)]
lemma sectionsWithSupport_map_ι
    {N N' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (g : N ⟶ N') :
    (sectionsWithSupport Λ j).map g ≫ (sectionsWithSupportι Λ j).app N' =
      (sectionsWithSupportι Λ j).app N ≫ g :=
  kernel.lift_ι _ _ _

/-- The lift of a morphism out of a module object vanishing on `U` to the sections with
support. -/
noncomputable def sectionsWithSupportLiftHom
    {F N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hF : supportedAway Λ j F) (f : F ⟶ N) : F ⟶ (sectionsWithSupport Λ j).obj N :=
  kernel.lift _ f (comp_unit_app_eq_zero Λ j hF f)

@[reassoc (attr := simp)]
lemma sectionsWithSupportLiftHom_ι
    {F N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hF : supportedAway Λ j F) (f : F ⟶ N) :
    sectionsWithSupportLiftHom Λ j hF f ≫ (sectionsWithSupportι Λ j).app N = f :=
  kernel.lift_ι _ _ _

instance (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono ((sectionsWithSupportι Λ j).app N) :=
  inferInstanceAs (Mono (kernel.ι _))

/-- The inclusion of the module objects vanishing on `U` is left adjoint to `Γ_Z`. -/
noncomputable def supportedAwayιAdjunction [IsOpenImmersion j] :
    (supportedAway Λ j).ι ⊣ sectionsWithSupportLift Λ j :=
  Adjunction.mkOfHomEquiv
    { homEquiv F N :=
        { toFun f := ObjectProperty.homMk (sectionsWithSupportLiftHom Λ j F.2 f)
          invFun g := g.hom ≫ (sectionsWithSupportι Λ j).app N
          left_inv f := sectionsWithSupportLiftHom_ι Λ j F.2 f
          right_inv g := by
            ext1
            exact (cancel_mono ((sectionsWithSupportι Λ j).app N)).1
              (sectionsWithSupportLiftHom_ι Λ j F.2 _) }
      homEquiv_naturality_left_symm f g := Category.assoc f.hom g.hom _
      homEquiv_naturality_right {F N N'} f g := by
        ext1
        refine (cancel_mono ((sectionsWithSupportι Λ j).app N')).1 ?_
        change sectionsWithSupportLiftHom Λ j F.2 (f ≫ g) ≫ _ =
          (sectionsWithSupportLiftHom Λ j F.2 f ≫ (sectionsWithSupport Λ j).map g) ≫ _
        rw [sectionsWithSupportLiftHom_ι, Category.assoc, sectionsWithSupport_map_ι,
          sectionsWithSupportLiftHom_ι_assoc] }

end Definition

section Adjunction

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j]

omit [IsClosedImmersion i] [QuasiCompact j] in
/-- The pullback along an open immersion of the pushforward along a closed immersion with
disjoint range vanishes. -/
lemma isZero_upperStar_lowerStar_of_disjoint
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((j)^*⟦Λ⟧.obj ((i)_*⟦Λ⟧.obj G)) :=
  isZero_of_isZero_X Λ ((ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j hij
    G.X).of_iso (upperStarObjXIso Λ j _))

/-- For a module object `F` vanishing on `U`, the unit `F ⟶ i_* i^* F` is an isomorphism: its
restriction to `Z` is inverse to the counit isomorphism, and its restriction to `U` is a map
between zero objects. -/
theorem isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsZero ((j)^*⟦Λ⟧.obj F)) :
    IsIso ((upperStarLowerStarAdjunction Λ i).unit.app F) := by
  set adj := upperStarLowerStarAdjunction Λ i
  have h₂ : IsIso ((i)^*⟦Λ⟧.map (adj.unit.app F)) := by
    have : IsIso ((i)^*⟦Λ⟧.map (adj.unit.app F) ≫ adj.counit.app ((i)^*⟦Λ⟧.obj F)) := by
      rw [adj.left_triangle_components F]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have h₁ : IsIso ((j)^*⟦Λ⟧.map (adj.unit.app F)) :=
    ⟨⟨0, hF.eq_of_src _ _, (isZero_upperStar_lowerStar_of_disjoint Λ i j hij.disjoint
      _).eq_of_src _ _⟩⟩
  exact (jointlyReflectIsomorphisms_upperStar_of_isCompl Λ i j hij).isIso_of_pairFunctor _ h₁ h₂

/-- The pushforward of module objects along a closed immersion with quasi-compact open complement
preserves epimorphisms: the cokernel of `i_* φ` vanishes on `Z`, since `i^* i_* φ` is `φ` up to
the counit isomorphism, and on `U`, since `j^* i_* = 0`. -/
lemma epi_lowerStar_map_of_isCompl (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {G H : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (φ : G ⟶ H) [Epi φ] : Epi ((i)_*⟦Λ⟧.map φ) := by
  set ε := (upperStarLowerStarAdjunction Λ i).counit
  have hε : (i)^*⟦Λ⟧.map ((i)_*⟦Λ⟧.map φ) = ε.app G ≫ φ ≫ inv (ε.app H) := by
    rw [← Category.assoc, IsIso.eq_comp_inv]
    exact ε.naturality φ
  have : Epi ((i)^*⟦Λ⟧.map ((i)_*⟦Λ⟧.map φ)) := by
    rw [hε]
    infer_instance
  refine Preadditive.epi_of_isZero_cokernel _ (isZero_of_isZero_upperStar_of_isCompl Λ i j hij _
    ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ _)) ?_)
  exact (IsZero.of_epi (cokernel.π ((j)^*⟦Λ⟧.map ((i)_*⟦Λ⟧.map φ)))
    (isZero_upperStar_lowerStar_of_disjoint Λ i j hij.disjoint H)).of_iso
      (PreservesCokernel.iso _ _)

/-- The pushforward of module objects along a closed immersion with quasi-compact open complement
is exact: it is left exact as a right adjoint and preserves epimorphisms
(`ProEtale.CondensedRing.epi_lowerStar_map_of_isCompl`). -/
theorem preservesFiniteColimits_lowerStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesFiniteColimits (i)_*⟦Λ⟧ := by
  have : ((i)_*⟦Λ⟧).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ epi_lowerStar_map_of_isCompl Λ i j hij φ⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels ((i)_*⟦Λ⟧)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- `i_*`, as a functor to the module objects vanishing on `U`. -/
noncomputable def lowerStarLift (hij : Disjoint (Set.range i.base) (Set.range j.base)) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) ⥤
      (supportedAway Λ j).FullSubcategory :=
  (supportedAway Λ j).lift ((i)_*⟦Λ⟧) (isZero_upperStar_lowerStar_of_disjoint Λ i j hij)

/-- The adjunction `i^* ⊣ i_*` restricted to the module objects vanishing on `U`. -/
noncomputable def upperStarLowerStarLiftAdjunction
    (hij : Disjoint (Set.range i.base) (Set.range j.base)) :
    (supportedAway Λ j).ι ⋙ (i)^*⟦Λ⟧ ⊣ lowerStarLift Λ i j hij :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        { toFun f := ObjectProperty.homMk
            ((upperStarLowerStarAdjunction Λ i).homEquiv _ _ f)
          invFun g := ((upperStarLowerStarAdjunction Λ i).homEquiv _ _).symm g.hom
          left_inv f := ((upperStarLowerStarAdjunction Λ i).homEquiv _ _).symm_apply_apply f
          right_inv g := by
            ext1
            exact ((upperStarLowerStarAdjunction Λ i).homEquiv _ _).apply_symm_apply g.hom }
      homEquiv_naturality_left_symm f g :=
        (upperStarLowerStarAdjunction Λ i).homEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right f g := by
        ext1
        exact (upperStarLowerStarAdjunction Λ i).homEquiv_naturality_right _ _ }

omit [IsClosedImmersion i] [QuasiCompact j] in
lemma upperStarLowerStarLiftAdjunction_unit_app_hom
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (F : (supportedAway Λ j).FullSubcategory) :
    ((upperStarLowerStarLiftAdjunction Λ i j hij).unit.app F).hom =
      (upperStarLowerStarAdjunction Λ i).unit.app F.obj :=
  (upperStarLowerStarAdjunction Λ i).homEquiv_id F.obj

omit [IsClosedImmersion i] [QuasiCompact j] in
lemma upperStarLowerStarLiftAdjunction_counit_app
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarLowerStarLiftAdjunction Λ i j hij).counit.app M =
      (upperStarLowerStarAdjunction Λ i).counit.app M :=
  (upperStarLowerStarAdjunction Λ i).homEquiv_symm_id M

/-- `i_*` is an equivalence onto the module objects vanishing on `U`, with inverse `i^*`. -/
noncomputable def lowerStarLiftEquivalence
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (supportedAway Λ j).FullSubcategory ≌
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) :=
  have : ∀ F, IsIso ((upperStarLowerStarLiftAdjunction Λ i j hij.disjoint).unit.app F) :=
    fun F ↦ by
    have : IsIso ((ObjectProperty.ι _).map
        ((upperStarLowerStarLiftAdjunction Λ i j hij.disjoint).unit.app F)) := by
      change IsIso ((upperStarLowerStarLiftAdjunction Λ i j hij.disjoint).unit.app F).hom
      rw [upperStarLowerStarLiftAdjunction_unit_app_hom]
      exact isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl Λ i j hij F.obj F.2
    exact isIso_of_fully_faithful (ObjectProperty.ι _) _
  have : ∀ M, IsIso ((upperStarLowerStarLiftAdjunction Λ i j hij.disjoint).counit.app M) :=
    fun M ↦ by
      rw [upperStarLowerStarLiftAdjunction_counit_app Λ i j hij.disjoint M]
      exact NatIso.isIso_app_of_isIso _ M
  (upperStarLowerStarLiftAdjunction Λ i j hij.disjoint).toEquivalence

/-- The adjunction `i_* ⊣ i^!₀` on module objects, for a closed immersion `i` with open
complement `j`: the composite of the equivalence between module objects on `Z` and module
objects on `X` vanishing on `U` (`ProEtale.CondensedRing.lowerStarLiftEquivalence`) and of the
coreflection given by the sections with support
(`ProEtale.CondensedRing.supportedAwayιAdjunction`). -/
noncomputable def lowerStarClosedUpperShriekAdjunction
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (i)_*⟦Λ⟧ ⊣ closedUpperShriek Λ i j :=
  (((lowerStarLiftEquivalence Λ i j hij).symm.toAdjunction.comp
    (supportedAwayιAdjunction Λ j)).ofNatIsoLeft
      (Iso.refl _ : _ ≅ (i)_*⟦Λ⟧)).ofNatIsoRight
    (Iso.refl _ : _ ≅ closedUpperShriek Λ i j)

end Adjunction

end AlgebraicGeometry.ProEtale.CondensedRing
