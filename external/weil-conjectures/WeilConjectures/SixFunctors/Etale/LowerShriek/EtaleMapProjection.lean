/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.Functor.KanExtension.ProjectionFormula
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor

/-!
# Extension by zero along an étale morphism: derived adjunction and projection formula

For an étale morphism `f : V ⟶ U`, the extension by zero
`AlgebraicGeometry.Etale.etaleLowerShriek` is exact for any Grothendieck abelian coefficient
category with sheafification, so it induces a left adjoint of `D(f^*)` on derived categories.
It also satisfies the projection formula `f_!(F ⊗ f^*G) ≅ f_!F ⊗ G`: at the presheaf level
both sides are `⨁_α F(α) ⊗ G(W)` over the lifts `α` of `W` through `f`, and sheafification
is monoidal.

## Main definitions

- `AlgebraicGeometry.Etale.derivedEtaleLowerShriekUpperStarAdjunction`: `D(f_!) ⊣ D(f^*)`.
- `AlgebraicGeometry.Etale.etaleLowerShriekTensorIso`: `f_!(F ⊗ f^*G) ≅ f_!F ⊗ G`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : Etale f)

/-- The extension by zero along an étale morphism is left adjoint to the restriction along the
localization functor. -/
noncomputable def Etale.etaleLowerShriekAdjunction :
    Etale.etaleLowerShriek A f h ⊣ Etale.localizationRestriction A f h :=
  have : (MorphismProperty.Over.map ⊤ h).IsContinuous V.smallEtaleTopology
      U.smallEtaleTopology :=
    inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale))
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    A V.smallEtaleTopology U.smallEtaleTopology

/-- The extension by zero along an étale morphism is left exact for any Grothendieck abelian
coefficient category with sheafification: pointwise on presheaves it is a direct sum of
evaluations, and sheafification is left exact. -/
instance Etale.preservesFiniteLimits_etaleLowerShriek_of_hasSmallSiteSheafify :
    PreservesFiniteLimits (Etale.etaleLowerShriek A f h) := by
  have : PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      (V.Etaleᵒᵖ ⥤ A) ⥤ U.Etaleᵒᵖ ⥤ A) :=
    SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A h
  unfold Etale.etaleLowerShriek Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

instance : PreservesFiniteColimits (Etale.etaleLowerShriek A f h) :=
  have := (Etale.etaleLowerShriekAdjunction A f h).leftAdjoint_preservesColimits
  inferInstance

instance : (Etale.etaleLowerShriek A f h).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The derived adjunction `D(f_!) ⊣ D(f^*)` for an étale morphism `f`, both functors being
exact. -/
noncomputable def Etale.derivedEtaleLowerShriekUpperStarAdjunction :
    (Etale.etaleLowerShriek A f h).mapDerivedCategory ⊣ D((f)^*[A]) :=
  let _ : CatCommSq ((Etale.etaleLowerShriek A f h).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (Etale.etaleLowerShriek A f h).mapDerivedCategory :=
    ⟨(Etale.etaleLowerShriek A f h).mapDerivedCategoryFactors.symm⟩
  let _ : CatCommSq (((f)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q D((f)^*[A]) :=
    ⟨((f)^*[A]).mapDerivedCategoryFactors.symm⟩
  ((Etale.etaleLowerShriekUpperStarAdjunction A f h).mapHomologicalComplex
    (ComplexShape.up ℤ)).localization DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
      DerivedCategory.Q (HomologicalComplex.quasiIso _ _) _ _

section Projection

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]

variable {V U : Scheme.{u}} {f : V ⟶ U} (h : Etale f)

/-- **The presheaf-level projection formula for extension by zero along an étale morphism.**
For presheaves `F` on `V_ét` and `G` on `U_ét`, the projection map
`Lan(F ⊗ f^*G) ⟶ Lan F ⊗ G` of the left Kan extension along the localization functor is an
isomorphism: at `W` both sides are `⨁_α F(α) ⊗ G(W)` over the lifts `α` of `W` through `f`
(`AlgebraicGeometry.SmallSite.exists_final_discrete_costructuredArrow_overMap`,
`CategoryTheory.Functor.isIso_lanProjectionMap_app`). -/
theorem Etale.isIso_lanProjectionMap_overMap (F : V.Etaleᵒᵖ ⥤ A) (G : U.Etaleᵒᵖ ⥤ A) :
    IsIso ((MorphismProperty.Over.map ⊤ h).op.lanProjectionMap F G) := by
  have : HasCoproducts.{u} A := hasCoproducts_shrink.{u, u + 1}
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W ↦ ?_
  obtain ⟨ι, s, hs, hiso⟩ := SmallSite.exists_final_discrete_costructuredArrow_overMap h W.unop
  exact Functor.isIso_lanProjectionMap_app _ F G W s hiso

variable [HasSmallSiteSheafify A]

/-- Extension by zero commutes with sheafification: `j_!(a P) ≅ a(Lan P)` for presheaves `P` on
`V_ét`, both functors being left adjoint to the restriction of presheaves. -/
noncomputable def Etale.presheafToSheafCompEtaleLowerShriekIso :
    presheafToSheaf V.smallEtaleTopology A ⋙ Etale.etaleLowerShriek A f h ≅
      (MorphismProperty.Over.map ⊤ h).op.lan ⋙ presheafToSheaf U.smallEtaleTopology A :=
  ((sheafificationAdjunction V.smallEtaleTopology A).comp
      (Etale.etaleLowerShriekAdjunction A f h)).leftAdjointUniq
    ((((MorphismProperty.Over.map ⊤ h).op.lanAdjunction A).comp
      (sheafificationAdjunction U.smallEtaleTopology A)).ofNatIsoRight (Iso.refl _))

/-- **The projection formula for extension by zero along an étale morphism**, for sheaves:
`j_!(F ⊗ f^*G) ≅ j_!F ⊗ G`. It is the sheafification of the presheaf-level projection formula
(`AlgebraicGeometry.Etale.isIso_lanProjectionMap_overMap`), sheafification being monoidal and
commuting with extension by zero (`AlgebraicGeometry.Etale.presheafToSheafCompEtaleLowerShriekIso`).
-/
noncomputable def Etale.etaleLowerShriekTensorIso (F : Sheaf V.smallEtaleTopology A)
    (G : Sheaf U.smallEtaleTopology A) :
    (Etale.etaleLowerShriek A f h).obj (F ⊗ ((f)^*[A]).obj G) ≅
      (Etale.etaleLowerShriek A f h).obj F ⊗ G :=
  have := Etale.isIso_lanProjectionMap_overMap A h F.obj G.obj
  (Etale.etaleLowerShriek A f h).mapIso
      (tensorIso (asIso ((sheafificationAdjunction _ A).counit.app F)).symm
          (asIso ((sheafificationAdjunction _ A).counit.app (((f)^*[A]).obj G))).symm ≪≫
        Functor.Monoidal.μIso (presheafToSheaf V.smallEtaleTopology A) _ _ ≪≫
        (presheafToSheaf V.smallEtaleTopology A).mapIso (whiskerLeftIso F.obj
          ((sheafToPresheaf _ A).mapIso
            ((Etale.upperStarIsoLocalizationRestriction A f h).app G)))) ≪≫
    (Etale.presheafToSheafCompEtaleLowerShriekIso A h).app _ ≪≫
    (presheafToSheaf U.smallEtaleTopology A).mapIso
      (asIso ((MorphismProperty.Over.map ⊤ h).op.lanProjectionMap F.obj G.obj)) ≪≫
    (Functor.Monoidal.μIso (presheafToSheaf U.smallEtaleTopology A) _ _).symm ≪≫
    whiskerLeftIso _ (asIso ((sheafificationAdjunction _ A).counit.app G))

omit [HasSmallSiteSheafify A] in
lemma Etale.etaleLowerShriekTensorIso_hom_naturality {F F' : Sheaf V.smallEtaleTopology A}
    {G G' : Sheaf U.smallEtaleTopology A} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (Etale.etaleLowerShriek A f h).map (φ ⊗ₘ ((f)^*[A]).map ψ) ≫
        (Etale.etaleLowerShriekTensorIso A h F' G').hom =
      (Etale.etaleLowerShriekTensorIso A h F G).hom ≫
        ((Etale.etaleLowerShriek A f h).map φ ⊗ₘ ψ) := by
  have hP := (MorphismProperty.Over.map ⊤ h).op.lanProjectionMap_naturality φ.hom ψ.hom
  have c1 : ∀ {P Q : Sheaf V.smallEtaleTopology A} (g : P ⟶ Q),
      g ≫ inv ((sheafificationAdjunction _ A).counit.app Q) =
        inv ((sheafificationAdjunction _ A).counit.app P) ≫
          (presheafToSheaf _ A).map ((sheafToPresheaf _ A).map g) := fun g ↦ by
    rw [IsIso.comp_inv_eq, Category.assoc]
    erw [(sheafificationAdjunction _ A).counit.naturality g]
    rw [IsIso.inv_hom_id_assoc]
    rfl
  have c2 : ∀ {P Q : Sheaf U.smallEtaleTopology A} (g : P ⟶ Q),
      (presheafToSheaf _ A).map ((sheafToPresheaf _ A).map g) ≫
        (sheafificationAdjunction _ A).counit.app Q =
          (sheafificationAdjunction _ A).counit.app P ≫ g :=
    fun g ↦ (sheafificationAdjunction _ A).counit.naturality g
  have e2 := (Etale.upperStarIsoLocalizationRestriction A f h).hom.naturality ψ
  have e3 : ((sheafToPresheaf _ A).map φ ⊗ₘ (sheafToPresheaf _ A).map (((f)^*[A]).map ψ)) ≫
      (F'.obj ◁ (sheafToPresheaf _ A).map
        ((Etale.upperStarIsoLocalizationRestriction A f h).app G').hom) =
      (F.obj ◁ (sheafToPresheaf _ A).map
        ((Etale.upperStarIsoLocalizationRestriction A f h).app G).hom) ≫
        ((sheafToPresheaf _ A).map φ ⊗ₘ (sheafToPresheaf _ A).map
          ((Etale.localizationRestriction A f h).map ψ)) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 2
    exact Category.comp_id _
  simp only [Etale.etaleLowerShriekTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, asIso_inv, tensorIso_hom, whiskerLeftIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Category.assoc (φ ⊗ₘ _), tensorHom_comp_tensorHom, c1, c1,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.μIso_hom, Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp, e3]
  have e1 := (Etale.presheafToSheafCompEtaleLowerShriekIso A h).hom.naturality
    ((sheafToPresheaf _ A).map φ ⊗ₘ (sheafToPresheaf _ A).map
      ((Etale.localizationRestriction A f h).map ψ))
  simp only [Functor.comp_map] at e1
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% e1]
  rw [← Functor.map_comp_assoc (presheafToSheaf U.smallEtaleTopology A)]
  erw [hP]
  rw [Functor.map_comp_assoc, Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv,
    ← Functor.OplaxMonoidal.δ_natural_assoc]
  have fin : ((presheafToSheaf U.smallEtaleTopology A).map
        ((MorphismProperty.Over.map ⊤ h).op.lan.map φ.hom) ⊗ₘ
        (presheafToSheaf U.smallEtaleTopology A).map ψ.hom) ≫
      (presheafToSheaf U.smallEtaleTopology A).obj
        ((MorphismProperty.Over.map ⊤ h).op.lan.obj F'.obj) ◁
          (sheafificationAdjunction U.smallEtaleTopology A).counit.app G' =
      (presheafToSheaf U.smallEtaleTopology A).obj
        ((MorphismProperty.Over.map ⊤ h).op.lan.obj F.obj) ◁
          (sheafificationAdjunction U.smallEtaleTopology A).counit.app G ≫
        ((Etale.etaleLowerShriek A f h).map φ ⊗ₘ ψ) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    erw [c2]
    simp only [Category.comp_id, Category.id_comp]
    rfl
  erw [fin]
  rfl

/-- The projection isomorphism `j_!F ⊗ G ≅ j_!(F ⊗ f^*G)` as a natural isomorphism of functors
of `G`. -/
noncomputable def Etale.tensorLeftEtaleLowerShriekIso (F : Sheaf V.smallEtaleTopology A) :
    tensorLeft ((Etale.etaleLowerShriek A f h).obj F) ≅
      (f)^*[A] ⋙ tensorLeft F ⋙ Etale.etaleLowerShriek A f h :=
  NatIso.ofComponents (fun G ↦ (Etale.etaleLowerShriekTensorIso A h F G).symm) fun {G G'} ψ ↦ by
    have := Etale.etaleLowerShriekTensorIso_hom_naturality A h (𝟙 F) ψ
    rw [CategoryTheory.Functor.map_id] at this
    dsimp
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, ← id_tensorHom, ← id_tensorHom]
    exact this.symm

attribute [local instance] Sheaf.braidedCategory in
/-- **Extension by zero along an étale morphism preserves flat sheaves**: for flat `F`, the
functor `j_!F ⊗ -` is isomorphic to `j_!(F ⊗ f^*(-))`, a composite of exact functors. -/
instance Etale.preservesFlat_etaleLowerShriek :
    (Etale.etaleLowerShriek A f h).PreservesFlat where
  flat_obj {F} hF := by
    have := hF.tensorLeft.preservesFiniteColimits
    have := hF.tensorLeft.preservesFiniteLimits
    have hl : exactFunctor _ _
        (tensorLeft ((Etale.etaleLowerShriek A f h).obj F)) :=
      (exactFunctor_iff _).2
        ⟨preservesFiniteLimits_of_natIso (Etale.tensorLeftEtaleLowerShriekIso A h F).symm,
          preservesFiniteColimits_of_natIso (Etale.tensorLeftEtaleLowerShriekIso A h F).symm⟩
    have := hl.preservesFiniteColimits
    have := hl.preservesFiniteLimits
    exact ⟨hl, (exactFunctor_iff _).2
      ⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _),
        preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)⟩⟩

omit [HasSmallSiteSheafify A] in
/-- **The projection formula for extension by zero along an étale morphism**, as the
invertibility of the projection map `f_!(f^*G ⊗ F) ⟶ G ⊗ f_!F` of the adjunction `f_! ⊣ f^*`
(`CategoryTheory.Functor.Monoidal.projectionMap`). It is conjugate to the internal-hom comparison
of `f^*`, which is an isomorphism (`AlgebraicGeometry.Etale.isIso_ihomComparison_upperStar`). -/
theorem Etale.isIso_projectionMap_etaleLowerShriek
    [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
    [(U.smallEtaleTopology.W (A := A)).IsMonoidal] [(V.smallEtaleTopology.W (A := A)).IsMonoidal]
    (G : Sheaf U.smallEtaleTopology A) :
    IsIso (Functor.Monoidal.projectionMap (Etale.etaleLowerShriekUpperStarAdjunction A f h) G) := by
  have : Etale f := h
  have := Etale.isIso_ihomComparison_upperStar A f G
  exact Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison _ G

end Projection

end AlgebraicGeometry
