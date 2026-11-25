/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!
# Extension by zero of constructible module objects

Let `Λ` be a commutative condensed ring and `j : U ⟶ X` an open immersion into a scheme whose
underlying space is noetherian. The extension by zero `j_!` of module objects over `Λ` maps
constructible module objects (`ProEtale.IsConstructibleModuleObject`) to constructible module
objects (`ProEtale.CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek_obj`,
blueprint `proposition-proper-direct-image-extension-zero`): a stratification of `U` together with
the closed complement of `U`, a zero stratum, is a stratification of `X`.

We also record that zero module objects are constructible
(`ProEtale.isConstructibleModuleObject_of_isZero`).
-/

@[expose] public section

universe v w u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type w} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- A zero module object is finitely presented: it is the cokernel of the zero map between free
modules of rank zero. -/
lemma IsFinitelyPresented.of_isZero {M : Mod C R} (hM : IsZero M) :
    IsFinitelyPresented R M := by
  refine ⟨0, 0, 0, ⟨hM.iso ?_⟩⟩
  have h0 : IsZero (finiteFree R 0) := by
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun i ↦ i.elim0
  have := h0.epi (0 : finiteFree R 0 ⟶ finiteFree R 0)
  exact isZero_cokernel_of_epi _

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X Y : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- The pullback of a zero module object is zero. -/
lemma isZero_upperStar_mapMod_obj (f : Y ⟶ X) {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (hM : IsZero M) : IsZero (((ProEtale.upperStar A f).mapMod R).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  refine (Mod.forget _).map_injective ?_
  exact ((ProEtale.upperStar A f).map_isZero ((Mod.forget R).map_isZero hM)).eq_of_src _ _

/-- A zero module object is pro-étale locally finitely presented, for the identity cover. -/
lemma isLocallyFinitelyPresented_of_isZero {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (hM : IsZero M) : IsLocallyFinitelyPresented R M :=
  ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦
    Mod.IsFinitelyPresented.of_isZero (isZero_upperStar_mapMod_obj R _ hM)⟩

/-- A zero module object is constructible, for the trivial stratification. -/
lemma isConstructibleModuleObject_of_isZero {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (hM : IsZero M) : IsConstructibleModuleObject R M :=
  ⟨Scheme.Stratification.trivial X, fun _ ↦
    isLocallyFinitelyPresented_of_isZero _ (isZero_upperStar_mapMod_obj R _ hM)⟩


/-- Pro-étale local finite presentation is preserved by restriction of scalars along an
isomorphism of ring objects. -/
lemma IsLocallyFinitelyPresented.comap {S : Sheaf (Scheme.ProEt.topology X) A} [MonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] {N : Mod (Sheaf (Scheme.ProEt.topology X) A) S}
    (h : IsLocallyFinitelyPresented S N) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj N) := by
  obtain ⟨𝒰, h⟩ := h
  exact ⟨𝒰, fun i ↦ Mod.IsFinitelyPresented.of_iso
    ((Functor.mapModComapIso (ProEtale.upperStar A (𝒰.f i)) φ).app N).symm
    ((h i).comap ((ProEtale.upperStar A (𝒰.f i)).map φ))⟩
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Pro-étale local finite presentation of the pullback `f^* N` of a module object can be read
either over `f^* Λ_X` (as in `ProEtale.IsConstructibleModuleObject`) or over `Λ_W`, the two being
identified by the isomorphism of ring objects `α_f : f^* Λ_X ⟶ Λ_W`. -/
lemma isLocallyFinitelyPresented_mapMod_iff {W X : Scheme.{u}} (f : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLocallyFinitelyPresented ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N) ↔
      IsLocallyFinitelyPresented (condensedRingObj Λ W) ((f)^*⟦Λ⟧.obj N) := by
  let α := condensedPullbackHom Λ f
  let e := (Mod.extendScalarsIsoComapInv α).app
    (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N)
  refine ⟨fun h ↦ IsLocallyFinitelyPresented.of_iso e.symm
      (IsLocallyFinitelyPresented.comap _ (asIso α).inv h),
    fun h ↦ IsLocallyFinitelyPresented.of_iso ?_ (IsLocallyFinitelyPresented.comap _ α h)⟩
  exact (Mod.comap α).mapIso e ≪≫ (Mod.comapEquivalenceOfIsIso α).counitIso.app _

/-- The pullback of `j_! M` along `g ≫ j` is pro-étale locally finitely presented if the pullback
of `M` along `g` is: `(g ≫ j)^* j_! M ≅ g^* j^* j_! M ≅ g^* M`. -/
lemma isLocallyFinitelyPresented_mapMod_comp_openImmersionLowerShriek_obj {W U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ U)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : IsLocallyFinitelyPresented ((g)^*[Ab.{u + 1}].obj (condensedRingObj Λ U))
      (((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ U)).obj M)) :
    IsLocallyFinitelyPresented ((g ≫ j)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((g ≫ j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj ((j)_!open⟦Λ⟧.obj M)) := by
  refine (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2 (IsLocallyFinitelyPresented.of_iso ?_
    ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 hM))
  exact (upperStar Λ g).mapIso
    (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M)) ≪≫
    ((upperStarComp Λ g j).app _).symm

/-- The pullback of `j_! M` along a morphism whose range misses the range of `j` is zero, hence
pro-étale locally finitely presented. -/
lemma isLocallyFinitelyPresented_mapMod_openImmersionLowerShriek_obj_of_disjoint
    {W U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (h : W ⟶ X)
    (hjh : Disjoint (Set.range j.base) (Set.range h.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsLocallyFinitelyPresented ((h)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((h)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj ((j)_!open⟦Λ⟧.obj M)) :=
  (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2 (isLocallyFinitelyPresented_of_isZero _
    (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j h hjh M))

/-- Blueprint `proposition-proper-direct-image-extension-zero` (extension by zero, on sheaves): for
an open immersion `j : U ⟶ X` into a noetherian scheme, `j_!` maps constructible module objects to
constructible module objects (add the closed complement as a zero stratum to a stratification
of `U`). -/
theorem isConstructibleModuleObject_openImmersionLowerShriek_obj {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ U) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) ((j)_!open⟦Λ⟧.obj M) := by
  have : QuasiCompact j := ⟨fun _ _ _ ↦
    j.isOpenEmbedding.isEmbedding.isCompact_iff.2 (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  obtain ⟨SU, hSU⟩ := hM
  obtain ⟨Z, i, _, hij⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i.base = (Set.range j.base)ᶜ :=
    ⟨_, j.closedComplement, inferInstance, j.range_closedComplement⟩
  refine ⟨Stratification.openClosed j i hij SU (Stratification.trivial Z), fun k ↦ ?_⟩
  change IsLocallyFinitelyPresented
      ((Sum.rec (motive := fun s ↦ Sum.elim SU.domain (Stratification.trivial Z).domain s ⟶ X)
        (fun l ↦ SU.immersion l ≫ j) (fun l ↦ (Stratification.trivial Z).immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((Sum.rec (motive := fun s ↦ Sum.elim SU.domain (Stratification.trivial Z).domain s ⟶ X)
        (fun l ↦ SU.immersion l ≫ j) (fun l ↦ (Stratification.trivial Z).immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj
          ((j)_!open⟦Λ⟧.obj M))
  generalize finSumFinEquiv.symm k = s
  rcases s with l | l
  · exact isLocallyFinitelyPresented_mapMod_comp_openImmersionLowerShriek_obj Λ j _ M (hSU l)
  · refine isLocallyFinitelyPresented_mapMod_openImmersionLowerShriek_obj_of_disjoint Λ j _ ?_ M
    dsimp only
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact disjoint_compl_right.mono_right ((Set.image_subset_range _ _).trans hij.le)

end AlgebraicGeometry.ProEtale.CondensedRing
