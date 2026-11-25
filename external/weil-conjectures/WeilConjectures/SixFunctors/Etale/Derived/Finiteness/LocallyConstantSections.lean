/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PointConstantSheafMap
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.LocallyConstantMittagLeffler
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

/-!
# Global sections of finite locally constant sheaves on connected schemes

Let `X` be a connected scheme, `s` a geometric point and `Λ` a finite ring.

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.hom_ext_of_sheafFiber`: morphisms of
  finite locally constant sheaves are determined by their stalks at `s`;
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.sectionsGerm_injective`: global sections
  are determined by their germ at `s`;
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.isIso_constantSheafAdj_counit`: if the
  germ map `Γ(X, G) ⟶ G_s` is bijective, `G` is the constant sheaf `Γ(X, G)_X` (through the counit
  of the constant sheaf adjunction).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **The stalk at one geometric point is faithful on finite locally constant sheaves** of a
connected scheme (Galois correspondence). -/
theorem IsFiniteLocallyConstantSheaf.hom_ext_of_sheafFiber
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (hG : IsFiniteLocallyConstantSheaf G) {f g : F ⟶ G}
    (h : (pointSmallEtale s).sheafFiber.map f = (pointSmallEtale s).sheafFiber.map g) :
    f = g := by
  obtain ⟨Gp, e, ⟨i⟩⟩ := Scheme.exists_equivalence_isFiniteLocallyConstantSheaf X s Λ
  let f' : (⟨F, hF⟩ : ObjectProperty.FullSubcategory
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        Scheme.IsFiniteLocallyConstantSheaf F)) ⟶ ⟨G, hG⟩ := ObjectProperty.homMk f
  let g' : (⟨F, hF⟩ : ObjectProperty.FullSubcategory
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        Scheme.IsFiniteLocallyConstantSheaf F)) ⟶ ⟨G, hG⟩ := ObjectProperty.homMk g
  have h1 : (e.functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} Λ Gp)
      (ModuleCat.{u + 1} Λ)).map f' = (e.functor ⋙ ObjectProperty.ι _ ⋙
        forget₂ (Rep.{u + 1} Λ Gp) (ModuleCat.{u + 1} Λ)).map g' := by
    rw [← cancel_mono (i.hom.app _), i.hom.naturality, i.hom.naturality]
    exact congrArg (i.hom.app _ ≫ ·) h
  have h2 : f' = g' := (e.functor ⋙ ObjectProperty.ι _ ⋙
      forget₂ (Rep.{u + 1} Λ Gp) (ModuleCat.{u + 1} Λ)).map_injective h1
  exact congrArg (fun φ ↦ (ObjectProperty.ι _).map φ) h2

/-- The germ at the geometric point `s` of global sections. -/
noncomputable abbrev sectionsGerm (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    G.obj.obj (op (Etale.mk (𝟙 X))) ⟶ (pointSmallEtale s).sheafFiber.obj G :=
  (pointSmallEtale s).toPresheafFiber (Etale.mk (𝟙 X)) (Over.homMk s) G.obj

/-- **A finite locally constant sheaf on a connected scheme is constant as soon as its global
sections map bijectively to one stalk**: the counit `Γ(X, G)_X ⟶ G` of the constant sheaf
adjunction is then an isomorphism on that stalk, hence an isomorphism. -/
theorem IsFiniteLocallyConstantSheaf.isIso_constantSheafAdj_counit
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hG : IsFiniteLocallyConstantSheaf G)
    (h : Function.Bijective (sectionsGerm s G)) :
    IsIso ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (Etale.isTerminalMkId X)).counit.app G) := by
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) (Etale.isTerminalMkId X)
  let M := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (Etale.mk (𝟙 X))) |>.obj G
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hstalk := (pointSmallEtale s).sheafFiberConstantSheafIso_inv_comp_sheafFiber_map
    (Etale.isTerminalMkId X) (Over.homMk s) M G (adj.counit.app G)
  have h1 : adj.homEquiv M G (adj.counit.app G) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact adj.right_triangle_components G
  rw [h1, Category.id_comp] at hstalk
  have : IsIso ((pointSmallEtale s).sheafFiber.map (adj.counit.app G)) := by
    rw [Iso.inv_comp_eq] at hstalk
    rw [hstalk]
    have : IsIso (sectionsGerm s G) := (ConcreteCategory.isIso_iff_bijective _).2 h
    infer_instance
  have hfin : Finite M := by
    have : Finite ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj G) := by
      have := (ModuleCat.isFinitelyGenerated_iff _).1
        (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := G) Ω s)
      exact Module.finite_of_finite Λ
    exact Finite.of_injective _ h.1
  have : Module.Finite Λ M := Module.Finite.of_finite
  exact IsFiniteLocallyConstantSheaf.isIso_of_isIso_sheafFiber_map s
    (Etale.isFiniteLocallyConstantSheaf_constantSheaf M) hG _

/-- **Global sections of a finite locally constant sheaf on a connected scheme are determined by
their germ at one geometric point.** -/
theorem IsFiniteLocallyConstantSheaf.sectionsGerm_injective
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hG : IsFiniteLocallyConstantSheaf G) :
    Function.Injective (sectionsGerm s G) := by
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) (Etale.isTerminalMkId X)
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  rw [injective_iff_map_eq_zero]
  intro t ht
  let L : ModuleCat.of Λ Λ ⟶ G.obj.obj (op (Etale.mk (𝟙 X))) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ t)
  have hstalk := (pointSmallEtale s).sheafFiberConstantSheafIso_inv_comp_sheafFiber_map
    (Etale.isTerminalMkId X) (Over.homMk s) (ModuleCat.of Λ Λ) G ((adj.homEquiv _ _).symm L)
  rw [Equiv.apply_symm_apply] at hstalk
  have h0 : (adj.homEquiv _ _).symm L = 0 := by
    refine IsFiniteLocallyConstantSheaf.hom_ext_of_sheafFiber s
      (Etale.isFiniteLocallyConstantSheaf_constantSheaf (ModuleCat.of Λ Λ)) hG ?_
    rw [← cancel_epi ((pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of Λ Λ)).inv,
      hstalk, Functor.map_zero, comp_zero]
    refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
    change sectionsGerm s G (c • t) = 0
    rw [map_smul, ht, smul_zero]
  have hL : L = 0 := by
    have := congrArg (adj.homEquiv _ _) h0
    rwa [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero] at this
  simpa [L] using congrArg (fun φ ↦ φ.hom 1) hL

end AlgebraicGeometry.Scheme
