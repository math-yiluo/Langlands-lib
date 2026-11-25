/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficientsProjection
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalization

/-!
# The rationalization formula on free modules

Let `R = ℤ_ℓ,X` and `A = ℚ̄_ℓ,X`, as abelian sheaves on `X_proét`. The rationalization comparison
`κ_M : ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M`
(`AlgebraicGeometry.ProEtale.rationalizationComparison`) at a free module `M = R ⊗ Z` is
`κ_{R ⊗ 𝟙} ▷ Z`, up to isomorphisms:

* `⨁_B colim (R ⊗ Z) ≅ (⨁_B colim R) ⊗ Z`, the tensor product commuting with colimits;
* `ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z) ≅ A ⊗ Z` on underlying abelian sheaves, by the projection formula
  `CategoryTheory.Sheaf.isIso_extendScalarsAbProjection` for the sheafified free
  `ℚ̄_ℓ`-module functor.

Hence the rationalization formula holds on every free module as soon as it holds on `R`
(`AlgebraicGeometry.ProEtale.isIso_rationalizationComparison_app_free_of_regular`), and so for
every `ℤ_ℓ,X`-module (`AlgebraicGeometry.ProEtale.isIso_rationalizationComparison_of_regular`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace CategoryTheory

section Rationalization

variable {C D : Type*} [Category* C] [Preadditive C] [Category* D] [Preadditive D] (l : ℕ)
  (G : C ⥤ D) (B : Type)

/-- An additive functor preserving sequential colimits commutes with
`A ↦ colim (A --ℓ--> A --ℓ--> ⋯)`. -/
noncomputable def ellRatCompIso [HasColimitsOfShape ℕ C] [HasColimitsOfShape ℕ D] [G.Additive]
    [PreservesColimitsOfShape ℕ G] (A : C) :
    (ellRat l).obj (G.obj A) ≅ G.obj ((ellRat l).obj A) :=
  HasColimit.isoOfNatIso (ellMulTowerCompIso G A) ≪≫ (preservesColimitIso _ _).symm

/-- The isomorphism `colim (G A --ℓ--> ⋯) ≅ G (colim (A --ℓ--> ⋯))` on the copies of `G A`. -/
@[reassoc (attr := simp)]
lemma ι_ellRatCompIso_hom [HasColimitsOfShape ℕ C] [HasColimitsOfShape ℕ D] [G.Additive]
    [PreservesColimitsOfShape ℕ G] (A : C) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj (G.obj A)) n ≫ (ellRatCompIso l G A).hom =
      G.map (colimit.ι ((ellMulTower l).obj A) n) := by
  simp [ellRatCompIso]

/-- A functor preserving coproducts indexed by `B` commutes with `A ↦ ⨁_B A`. -/
noncomputable def sigmaConstCompIso [HasColimitsOfShape (Discrete B) C]
    [HasColimitsOfShape (Discrete B) D] [PreservesColimitsOfShape (Discrete B) G] (A : C) :
    (sigmaConstFunctor B).obj (G.obj A) ≅ G.obj ((sigmaConstFunctor B).obj A) :=
  HasColimit.isoOfNatIso (Functor.constComp _ _ _).symm ≪≫ (preservesColimitIso _ _).symm

omit [Preadditive C] [Preadditive D] in
/-- The isomorphism `⨁_B G A ≅ G (⨁_B A)` on the summands. -/
@[reassoc (attr := simp)]
lemma ι_sigmaConstCompIso_hom [HasColimitsOfShape (Discrete B) C]
    [HasColimitsOfShape (Discrete B) D] [PreservesColimitsOfShape (Discrete B) G] (A : C)
    (b : Discrete B) :
    colimit.ι ((Functor.const (Discrete B)).obj (G.obj A)) b ≫ (sigmaConstCompIso G B A).hom =
      G.map (colimit.ι ((Functor.const (Discrete B)).obj A) b) := by
  simp [sigmaConstCompIso]

variable [HasColimitsOfShape ℕ C] [HasColimitsOfShape ℕ D] [HasColimitsOfShape (Discrete B) C]
  [HasColimitsOfShape (Discrete B) D]

/-- An additive functor preserving sequential colimits and coproducts indexed by `B` commutes
with `A ↦ ⨁_B colim (A --ℓ--> A --ℓ--> ⋯)`. -/
noncomputable def ellRatSigmaConstCompIso [G.Additive] [PreservesColimitsOfShape ℕ G]
    [PreservesColimitsOfShape (Discrete B) G] (A : C) :
    (sigmaConstFunctor B).obj ((ellRat l).obj (G.obj A)) ≅
      G.obj ((sigmaConstFunctor B).obj ((ellRat l).obj A)) :=
  (sigmaConstFunctor B).mapIso (ellRatCompIso l G A) ≪≫ sigmaConstCompIso G B _

/-- The isomorphism `⨁_B colim (G A --ℓ--> ⋯) ≅ G (⨁_B colim (A --ℓ--> ⋯))` on the copies
of `G A`. -/
@[reassoc (attr := simp)]
lemma ι_ι_ellRatSigmaConstCompIso_hom [G.Additive] [PreservesColimitsOfShape ℕ G]
    [PreservesColimitsOfShape (Discrete B) G] (A : C) (b : B) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj (G.obj A)) n ≫
      colimit.ι ((Functor.const (Discrete B)).obj ((ellRat l).obj (G.obj A))) ⟨b⟩ ≫
        (ellRatSigmaConstCompIso l G B A).hom =
      G.map (colimit.ι ((ellMulTower l).obj A) n ≫
        colimit.ι ((Functor.const (Discrete B)).obj ((ellRat l).obj A)) ⟨b⟩) := by
  simp only [ellRatSigmaConstCompIso, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map,
    colim_map, ι_colimMap_assoc, Functor.const_map_app, ι_sigmaConstCompIso_hom]
  rw [ι_ellRatCompIso_hom_assoc, Functor.map_comp]

/-- The map `⨁_B colim (A --ℓ--> ⋯) ⟶ ⨁_B colim (A' --ℓ--> ⋯)` induced by `f : A ⟶ A'`. -/
@[reassoc (attr := simp)]
lemma ι_ι_sigmaConstFunctor_map_ellRat_map {A A' : C} (f : A ⟶ A') (b : B) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj A) n ≫
      colimit.ι ((Functor.const (Discrete B)).obj ((ellRat l).obj A)) ⟨b⟩ ≫
        (sigmaConstFunctor B).map ((ellRat l).map f) =
      f ≫ colimit.ι ((ellMulTower l).obj A') n ≫
        colimit.ι ((Functor.const (Discrete B)).obj ((ellRat l).obj A')) ⟨b⟩ := by
  simp

end Rationalization

end CategoryTheory

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] (A : C) [MonObj A]

/-- A morphism out of a free module is the extension of its restriction along the unit. -/
lemma freeDesc_homEquiv {X : C} {M : Mod C A} (f : (free A).obj X ⟶ M) :
    freeDesc A ((λ_ X).inv ≫ η ▷ X ≫ f.hom) = f :=
  by simpa [freeForgetAdjunction, Adjunction.mkOfHomEquiv_homEquiv] using
    ((freeForgetAdjunction A).homEquiv X M).symm_apply_apply f

/-- The unit `X ⟶ A ⊗ X` of the free-forgetful adjunction. -/
lemma freeForgetAdjunction_unit_app (X : C) :
    (freeForgetAdjunction A).unit.app X = (λ_ X).inv ≫ η ▷ X := by
  simp [freeForgetAdjunction]

/-- `freeDesc` is natural in the target module. -/
lemma freeDesc_comp {X : C} {M N : Mod C A} (g : X ⟶ M.X) (f : M ⟶ N) :
    freeDesc A g ≫ f = freeDesc A (g ≫ f.hom) :=
  Mod.hom_ext _ _ (by simp)

/-- `A ◁ (X ⟶ 𝟙 ⊗ X ⟶ A ⊗ X) ≫ (A ⊗ (A ⊗ X) ⟶ A ⊗ X)` is the identity of the free module. -/
lemma whiskerLeft_unit_comp_act_free (X : C) :
    A ◁ ((λ_ X).inv ≫ η ▷ X) ≫ (α_ A A X).inv ≫ μ ▷ X = 𝟙 (A ⊗ X) := by
  rw [MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight, MonObj.mul_one]
  monoidal

/-- The regular module `A` is the free module `A ⊗ 𝟙` on the unit. -/
noncomputable def regularIsoFree : regular A ≅ (free A).obj (𝟙_ C) :=
  isoMk (ρ_ A).symm (by
    refine (rightUnitor_inv_naturality μ[A]).trans ?_
    rw [rightUnitor_tensor_inv, Category.assoc]
    rfl)

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The unit `Z ⟶ R ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)`, for `R = ℤ_ℓ,X`. -/
noncomputable def adicSheafExtendScalarsFreeUnit (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    Z ⟶ (AdicSheaf.toAb l X).obj
      ((adicSheafExtendScalars X l).obj ((Mod.free (padicIntAbSheaf X l)).obj Z)) :=
  (λ_ Z).inv ≫ η[padicIntAbSheaf X l] ▷ Z ≫
    adicSheafExtendScalarsUnitAb l X ((Mod.free (padicIntAbSheaf X l)).obj Z)

/-- The extension `A ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)`, linear over `A = ℚ̄_ℓ,X`, of the unit
`Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)`. It is an isomorphism, by the projection formula. -/
noncomputable def adicSheafExtendScalarsFreeDesc (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X) ⊗ Z ⟶ (AdicSheaf.toAb l X).obj
      ((adicSheafExtendScalars X l).obj ((Mod.free (padicIntAbSheaf X l)).obj Z)) :=
  (Mod.freeDesc _ (M := (AdicSheaf.forgetAb l X).obj
    ((adicSheafExtendScalars X l).obj ((Mod.free (padicIntAbSheaf X l)).obj Z)))
    (adicSheafExtendScalarsFreeUnit l X Z)).hom

/-- The unit `R ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` is `R ⊗ Z ⟶ A ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)`, being
`R`-linear. -/
lemma adicSheafExtendScalarsUnitAb_free (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    adicSheafExtendScalarsUnitAb l X ((Mod.free (padicIntAbSheaf X l)).obj Z) =
      padicIntSheafToAdicConstantSheaf X l ▷ Z ≫ adicSheafExtendScalarsFreeDesc l X Z := by
  rw [adicSheafExtendScalarsUnitAb, Mod.forget_map, ← Mod.freeDesc_homEquiv _
    ((adicSheafExtendScalarsRestrictAdjunction X l).unit.app _), Mod.freeDesc_hom,
    adicSheafExtendScalarsFreeDesc, Mod.freeDesc_hom, ← whisker_exchange_assoc]
  rfl

/-- The adjunction between `Z ↦ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` and the underlying abelian sheaf. -/
noncomputable def adicSheafExtendScalarsFreeAdjunction :
    Mod.free (padicIntAbSheaf X l) ⋙ adicSheafExtendScalars X l ⊣ AdicSheaf.toAb l X :=
  (Mod.freeForgetAdjunction _).comp (adicSheafExtendScalarsRestrictAdjunction X l)

/-- The unit of `Z ↦ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` ⊣ underlying abelian sheaf. -/
lemma adicSheafExtendScalarsFreeAdjunction_unit_app (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (adicSheafExtendScalarsFreeAdjunction l X).unit.app Z =
      adicSheafExtendScalarsFreeUnit l X Z := by
  simp [adicSheafExtendScalarsFreeAdjunction, Mod.freeForgetAdjunction_unit_app,
    adicSheafExtendScalarsFreeUnit, adicSheafExtendScalarsUnitAb]

/-- The adjunction between `Z ↦ ℚ̄_ℓ,X ⊗ F Z` and the underlying abelian sheaf, for the sheafified
free `ℚ̄_ℓ`-module functor `F`. -/
noncomputable def adicSheafFreeAdjunction :
    weilCoefficientsFree X l ⋙ Mod.free (adicConstantSheaf l X) ⊣ AdicSheaf.toAb l X :=
  (weilCoefficientsFreeAdjunction X l).comp (Mod.freeForgetAdjunction _)

/-- `ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z) ≅ ℚ̄_ℓ,X ⊗ F Z`, both being left adjoint to the underlying abelian
sheaf. -/
noncomputable def adicSheafExtendScalarsFreeIso :
    Mod.free (padicIntAbSheaf X l) ⋙ adicSheafExtendScalars X l ≅
      weilCoefficientsFree X l ⋙ Mod.free (adicConstantSheaf l X) :=
  (adicSheafExtendScalarsFreeAdjunction l X).leftAdjointUniq (adicSheafFreeAdjunction l X)

/-- Under `ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z) ≅ ℚ̄_ℓ,X ⊗ F Z`, the map `A ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` is the
projection formula map `A ⊗ Z ⟶ U (ℚ̄_ℓ,X ⊗ F Z)`. -/
lemma adicSheafExtendScalarsFreeDesc_comp_toAb_map_freeIso_hom
    (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    adicSheafExtendScalarsFreeDesc l X Z ≫
      (AdicSheaf.toAb l X).map ((adicSheafExtendScalarsFreeIso l X).hom.app Z) =
      Sheaf.extendScalarsAbProjection (ProEt.topology X) (ULift.{u + 1} (PadicAlgCl l))
        (adicConstantSheaf l X) Z := by
  have h1 : adicSheafExtendScalarsFreeUnit l X Z ≫
      ((AdicSheaf.forgetAb l X).map ((adicSheafExtendScalarsFreeIso l X).hom.app Z)).hom =
      (adicSheafFreeAdjunction l X).unit.app Z := by
    rw [← adicSheafExtendScalarsFreeAdjunction_unit_app]
    exact Adjunction.unit_leftAdjointUniq_hom_app _ _ Z
  have h2 : adicSheafExtendScalarsFreeDesc l X Z ≫
      (AdicSheaf.toAb l X).map ((adicSheafExtendScalarsFreeIso l X).hom.app Z) =
      (Mod.freeDesc _ (adicSheafExtendScalarsFreeUnit l X Z) ≫
        (AdicSheaf.forgetAb l X).map ((adicSheafExtendScalarsFreeIso l X).hom.app Z)).hom :=
    rfl
  rw [h2, Mod.freeDesc_comp, h1, Mod.freeDesc_hom, adicSheafFreeAdjunction,
    Adjunction.comp_unit_app, Mod.freeForgetAdjunction_unit_app,
    MonoidalCategory.whiskerLeft_comp_assoc, Sheaf.extendScalarsAbProjection]
  congr 1
  have h3 : Mod.act ((AdicSheaf.forgetAb l X).obj
      ((weilCoefficientsFree X l ⋙ Mod.free (adicConstantSheaf l X)).obj Z)).X =
      Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l X) _ _ ≫
        (weilCoefficientsForgetAb l X).map ((α_ _ _ ((weilCoefficientsFree X l).obj Z)).inv ≫
          μ[adicConstantSheaf l X] ▷ _) :=
    rfl
  rw [h3]
  refine (Functor.LaxMonoidal.μ_natural_right_assoc (weilCoefficientsForgetAb l X)
    (adicConstantSheaf l X) ((λ_ ((weilCoefficientsFree X l).obj Z)).inv ≫
      η[adicConstantSheaf l X] ▷ _) _).trans ?_
  rw [← Functor.map_comp, Mod.whiskerLeft_unit_comp_act_free, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The map `A ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` is an isomorphism, by the projection formula. -/
instance isIso_adicSheafExtendScalarsFreeDesc (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    IsIso (adicSheafExtendScalarsFreeDesc l X Z) := by
  have : IsIso (adicSheafExtendScalarsFreeDesc l X Z ≫
      (AdicSheaf.toAb l X).map ((adicSheafExtendScalarsFreeIso l X).hom.app Z)) := by
    rw [adicSheafExtendScalarsFreeDesc_comp_toAb_map_freeIso_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((AdicSheaf.toAb l X).map
    ((adicSheafExtendScalarsFreeIso l X).hom.app Z))

/-- Multiplication by a scalar `v ∈ ℚ̄_ℓ` on the abelian sheaf `ℚ̄_ℓ,X`. -/
noncomputable abbrev adicConstantSheafAbScalarMul (v : PadicAlgCl l) :
    (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X) ⟶
      (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X) :=
  (weilCoefficientsForgetAb l X).map
    ((ULift.up v : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 (adicConstantSheaf l X))

/-- The action of `A = ℚ̄_ℓ,X` on the underlying abelian sheaf of an `ℓ`-adic sheaf commutes with
the multiplication by scalars. -/
@[reassoc]
lemma adicConstantSheafAbScalarMul_whiskerRight_act (P : AdicSheaf l X) (v : PadicAlgCl l) :
    adicConstantSheafAbScalarMul l X v ▷ (weilCoefficientsForgetAb l X).obj P.X ≫
      Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l X) (adicConstantSheaf l X) P.X ≫
        (weilCoefficientsForgetAb l X).map (Mod.act P.X) =
      (Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l X) (adicConstantSheaf l X) P.X ≫
        (weilCoefficientsForgetAb l X).map (Mod.act P.X)) ≫ adicScalarMul l P v := by
  rw [adicConstantSheafAbScalarMul, Functor.LaxMonoidal.μ_natural_left_assoc, Category.assoc,
    ← Functor.map_comp, MonoidalLinear.smul_whiskerRight, id_whiskerRight, Linear.smul_comp,
    Category.id_comp, adicScalarMul, ← Functor.map_comp, Linear.comp_smul]
  erw [Category.comp_id]

/-- The map `A ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` commutes with the multiplication by scalars. -/
@[reassoc]
lemma adicConstantSheafAbScalarMul_whiskerRight_freeDesc
    (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) (v : PadicAlgCl l) :
    adicConstantSheafAbScalarMul l X v ▷ Z ≫ adicSheafExtendScalarsFreeDesc l X Z =
      adicSheafExtendScalarsFreeDesc l X Z ≫ adicScalarMul l
        ((adicSheafExtendScalars X l).obj ((Mod.free (padicIntAbSheaf X l)).obj Z)) v := by
  have h : adicSheafExtendScalarsFreeDesc l X Z =
      _ ◁ adicSheafExtendScalarsFreeUnit l X Z ≫
        Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l X) (adicConstantSheaf l X)
          ((adicSheafExtendScalars X l).obj ((Mod.free (padicIntAbSheaf X l)).obj Z)).X ≫
        (weilCoefficientsForgetAb l X).map (Mod.act
          ((adicSheafExtendScalars X l).obj ((Mod.free (padicIntAbSheaf X l)).obj Z)).X) :=
    rfl
  rw [h]
  refine (whisker_exchange_assoc _ _ _).symm.trans ?_
  refine ((_ ◁ adicSheafExtendScalarsFreeUnit l X Z) ≫=
    adicConstantSheafAbScalarMul_whiskerRight_act l X _ v).trans ?_
  simp only [Category.assoc]

/-- The isomorphism `(ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ 𝟙)) ⊗ Z ≅ A ⊗ Z ≅ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` on underlying
abelian sheaves. -/
noncomputable def adicSheafExtendScalarsFreeTensorHom (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj
        ((Mod.free (padicIntAbSheaf X l)).obj (𝟙_ _))) ⊗ Z ⟶
      (AdicSheaf.toAb l X).obj
        ((adicSheafExtendScalars X l).obj ((Mod.free (padicIntAbSheaf X l)).obj Z)) :=
  inv (adicSheafExtendScalarsFreeDesc l X (𝟙_ _)) ▷ Z ≫ (ρ_ _).hom ▷ Z ≫
    adicSheafExtendScalarsFreeDesc l X Z

/-- `(ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ 𝟙)) ⊗ Z ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)` is an isomorphism. -/
instance isIso_adicSheafExtendScalarsFreeTensorHom (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    IsIso (adicSheafExtendScalarsFreeTensorHom l X Z) := by
  dsimp only [adicSheafExtendScalarsFreeTensorHom]
  infer_instance

/-- The maps `m ↦ (b / ℓⁿ) ⊗ m` on `R ⊗ 𝟙` and on `R ⊗ Z` are compatible with
`(ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ 𝟙)) ⊗ Z ≅ ℚ̄_ℓ ⊗_{ℤ_ℓ} (R ⊗ Z)`. -/
lemma rationalizationComparisonι_free_unit_whiskerRight_comp
    (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) (b : padicAlgClBasisIndex l) (n : ℕ) :
    rationalizationComparisonι l X ((Mod.free (padicIntAbSheaf X l)).obj (𝟙_ _)) b n ▷ Z ≫
      adicSheafExtendScalarsFreeTensorHom l X Z =
      (ρ_ (padicIntAbSheaf X l)).hom ▷ Z ≫
        rationalizationComparisonι l X ((Mod.free (padicIntAbSheaf X l)).obj Z) b n := by
  have key : padicIntSheafToAdicConstantSheaf X l ▷ 𝟙_ _ ≫
      adicConstantSheafAbScalarMul l X ((b : PadicAlgCl l) / (l : PadicAlgCl l) ^ n) ▷ 𝟙_ _ ≫
      adicSheafExtendScalarsFreeDesc l X (𝟙_ _) ≫ inv (adicSheafExtendScalarsFreeDesc l X (𝟙_ _)) ≫
      (ρ_ _).hom =
      (ρ_ _).hom ≫ padicIntSheafToAdicConstantSheaf X l ≫
        adicConstantSheafAbScalarMul l X ((b : PadicAlgCl l) / (l : PadicAlgCl l) ^ n) := by
    rw [IsIso.hom_inv_id_assoc, rightUnitor_naturality, rightUnitor_naturality_assoc]
  rw [rationalizationComparisonι, rationalizationComparisonι, adicSheafExtendScalarsUnitAb_free,
    adicSheafExtendScalarsUnitAb_free, Category.assoc, Category.assoc,
    ← adicConstantSheafAbScalarMul_whiskerRight_freeDesc,
    ← adicConstantSheafAbScalarMul_whiskerRight_freeDesc,
    adicSheafExtendScalarsFreeTensorHom]
  have := congrArg (· ▷ Z ≫ adicSheafExtendScalarsFreeDesc l X Z) key
  simp only [comp_whiskerRight, Category.assoc] at this
  simpa only [comp_whiskerRight, Category.assoc] using this

/-- **The rationalization formula on free modules**: if the rationalization comparison is an
isomorphism at `R ⊗ 𝟙`, then it is an isomorphism at every free module `R ⊗ Z`, being
`κ_{R ⊗ 𝟙} ▷ Z` up to isomorphisms. -/
theorem isIso_rationalizationComparison_app_free_of_unit
    (h : IsIso ((rationalizationComparison l X).app
      ((Mod.free (padicIntAbSheaf X l)).obj (𝟙_ _))))
    (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    IsIso ((rationalizationComparison l X).app ((Mod.free (padicIntAbSheaf X l)).obj Z)) := by
  let e₁ := ellRatSigmaConstCompIso l (tensorRight Z) (padicAlgClBasisIndex l)
    (padicIntAbSheaf X l ⊗ 𝟙_ _)
  let e₂ := (ellRat l ⋙ sigmaConstFunctor (padicAlgClBasisIndex l)).mapIso
    (whiskerRightIso (ρ_ (padicIntAbSheaf X l)) Z)
  have key : e₁.hom ≫ (rationalizationComparison l X).app
      ((Mod.free (padicIntAbSheaf X l)).obj (𝟙_ _)) ▷ Z ≫
        adicSheafExtendScalarsFreeTensorHom l X Z =
      e₂.hom ≫ (rationalizationComparison l X).app ((Mod.free (padicIntAbSheaf X l)).obj Z) := by
    refine colimit.hom_ext fun ⟨b⟩ ↦ colimit.hom_ext fun n ↦ ?_
    have h₁ : colimit.ι ((ellMulTower l).obj ((padicIntAbSheaf X l ⊗ 𝟙_ _) ⊗ Z)) n ≫
        colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
          ((ellRat l).obj ((padicIntAbSheaf X l ⊗ 𝟙_ _) ⊗ Z))) ⟨b⟩ ≫ e₁.hom =
        (colimit.ι ((ellMulTower l).obj (padicIntAbSheaf X l ⊗ 𝟙_ _)) n ≫
          colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
            ((ellRat l).obj (padicIntAbSheaf X l ⊗ 𝟙_ _))) ⟨b⟩) ▷ Z :=
      ι_ι_ellRatSigmaConstCompIso_hom l (tensorRight Z) (padicAlgClBasisIndex l)
      (padicIntAbSheaf X l ⊗ 𝟙_ _) b n
    have h₂ : colimit.ι ((ellMulTower l).obj ((padicIntAbSheaf X l ⊗ 𝟙_ _) ⊗ Z)) n ≫
        colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
          ((ellRat l).obj ((padicIntAbSheaf X l ⊗ 𝟙_ _) ⊗ Z))) ⟨b⟩ ≫ e₂.hom =
        (ρ_ (padicIntAbSheaf X l)).hom ▷ Z ≫
          colimit.ι ((ellMulTower l).obj (padicIntAbSheaf X l ⊗ Z)) n ≫
          colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
            ((ellRat l).obj (padicIntAbSheaf X l ⊗ Z))) ⟨b⟩ :=
      ι_ι_sigmaConstFunctor_map_ellRat_map l (padicAlgClBasisIndex l) _ b n
    have h₃ := ι_ι_rationalizationComparisonApp l X
      ((Mod.free (padicIntAbSheaf X l)).obj (𝟙_ _)) b n
    have h₄ := ι_ι_rationalizationComparisonApp l X ((Mod.free (padicIntAbSheaf X l)).obj Z) b n
    have h₅ := rationalizationComparisonι_free_unit_whiskerRight_comp l X Z b n
    erw [reassoc_of% h₁, reassoc_of% h₂]
    erw [← comp_whiskerRight_assoc, Category.assoc, h₃, h₅, h₄]
  have : IsIso (e₂.hom ≫ (rationalizationComparison l X).app
      ((Mod.free (padicIntAbSheaf X l)).obj Z)) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_left e₂.hom _

/-- **The rationalization formula on free modules**: if the rationalization comparison is an
isomorphism at `R = ℤ_ℓ,X`, then it is an isomorphism at every free module `R ⊗ Z`. -/
theorem isIso_rationalizationComparison_app_free_of_regular
    (h : IsIso ((rationalizationComparison l X).app (Mod.regular (padicIntAbSheaf X l))))
    (Z : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    IsIso ((rationalizationComparison l X).app ((Mod.free (padicIntAbSheaf X l)).obj Z)) :=
  isIso_rationalizationComparison_app_free_of_unit l X
    ((NatTrans.isIso_app_iff_of_iso _ (Mod.regularIsoFree _)).1 h) Z

/-- **The rationalization formula**: if the rationalization comparison is an isomorphism at
`R = ℤ_ℓ,X`, then it is an isomorphism, both sides being right exact and agreeing on free
modules. -/
theorem isIso_rationalizationComparison_of_regular
    (h : IsIso ((rationalizationComparison l X).app (Mod.regular (padicIntAbSheaf X l)))) :
    IsIso (rationalizationComparison l X) :=
  isIso_rationalizationComparison_of_free l X
    (isIso_rationalizationComparison_app_free_of_regular l X h)

end AlgebraicGeometry.ProEtale
