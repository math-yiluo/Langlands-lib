/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.TensorComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheafTensorProj
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldUpperStarCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportSection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-!
# Residue field module sheaves commute with tensor products and pullbacks

Write `G_X = residueFieldModuleSheaf X ℓ E` for the equivalence between module objects over
`𝔽_{E,X}` and pro-étale sheaves of `𝔽_E`-modules. It commutes with the tensor products
(`ProEtale.residueFieldModuleSheafTensorIso`, transported from
`ProEtale.finiteCoefficientModEquivalenceTensorIso`),
hence preserves flat objects. On underlying abelian sheaves, this tensor isomorphism sends the
projection `M ⊗ N ⟶ M ⊗_{𝔽_{E,X}} N` to the tensor map of the underlying abelian sheaf functor
(`ProEtale.tensorObjπ_comp_map_residueFieldModuleSheafTensorIso_hom`). Consequently the
commutation `f^* ⋙ G_X ≅ G_Y ⋙ f^*` with the pullbacks
(`ProEtale.residueFieldModuleSheafUpperStarIso`) is compatible with the tensor isomorphisms of
`G_X`, `G_Y` and the comonoidal structures of the pullbacks
(`ProEtale.tensorCompatible_residueFieldModuleSheafUpperStarIso`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {Λ : Type w} [CommRing Λ]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- On underlying abelian sheaves, the inverse of `isoOfSheafComposeForget₂ e he` is the inverse
of `e`. -/
lemma sheafCompose_map_isoOfSheafComposeForget₂_inv_app {𝒜 : Type*} [Category* 𝒜]
    {P Q : 𝒜 ⥤ Sheaf J (ModuleCat.{w} Λ)}
    (e : P ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      Q ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})) (he) (a : 𝒜) :
    (sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map ((isoOfSheafComposeForget₂ e he).inv.app a) =
      e.inv.app a := by
  rw [← cancel_epi ((sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map
      ((isoOfSheafComposeForget₂ e he).hom.app a)), ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, sheafCompose_map_isoOfSheafComposeForget₂_hom_app,
    Iso.hom_inv_id_app]
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

section FiniteCoefficient

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

omit [Fact ℓ.Prime] [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On underlying abelian sheaves, the tensor isomorphism `finiteCoefficientModEquivalenceTensorIso`
precomposed with the projection `M ⊗ N ⟶ M ⊗_{Λ_X} N` is the tensor map `μ` of the underlying
abelian sheaf functor. -/
@[reassoc]
lemma tensorObjπ_comp_map_finiteCoefficientModEquivalenceTensorIso_hom
    (A B : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    Mod.tensorObjπ A B ≫ (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) Ab.{u + 1})).map
        (((finiteCoefficientModEquivalenceTensorIso X T).hom.app A).app B) =
      Functor.LaxMonoidal.μ (sheafCompose (ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) Ab.{u + 1}))
        ((finiteCoefficientModEquivalence X T).functor.obj A)
        ((finiteCoefficientModEquivalence X T).functor.obj B) := by
  have hπ : Mod.tensorObjπ A B ≫
      (Mod.comapTensorIso (constRingSheafToCondensedRingObj X T) A B).inv.hom =
      Mod.tensorObjπ ((Mod.comap (constRingSheafToCondensedRingObj X T)).obj A)
        ((Mod.comap (constRingSheafToCondensedRingObj X T)).obj B) := by
    rw [← Mod.tensorπ_comapTensorIso_hom_hom (constRingSheafToCondensedRingObj X T) A B,
      Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom', Category.comp_id]
  have e : ((finiteCoefficientModEquivalenceTensorIso X T).hom.app A).app B =
      (Sheaf.modToSheafModule _ (ULift.{u + 1} T)).map
        (Mod.comapTensorIso (constRingSheafToCondensedRingObj X T) A B).inv ≫
      ((Sheaf.modToSheafModuleTensorIso _ (ULift.{u + 1} T)).hom.app
        ((Mod.comap (constRingSheafToCondensedRingObj X T)).obj A)).app
        ((Mod.comap (constRingSheafToCondensedRingObj X T)).obj B) :=
    rfl
  rw [e, Functor.map_comp, Sheaf.sheafCompose_map_modToSheafModule_map, reassoc_of% hπ]
  exact Sheaf.tensorObjπ_comp_map_modToSheafModuleTensorIso_hom _ _ _ _

end FiniteCoefficient

/-- **`G_X` commutes with the tensor products**: `G_X (M ⊗ N) ≅ G_X M ⊗ G_X N`, transported from
the tensor isomorphism `finiteCoefficientModEquivalenceTensorIso` along the identification
`residueFieldModuleSheafIsoOfSection` of `G_X` with the functor of
`finiteCoefficientModEquivalence`. -/
noncomputable def residueFieldModuleSheafTensorIso : (residueFieldModuleSheaf X ℓ E).TensorIso :=
  Functor.TensorIso.ofIso (finiteCoefficientModEquivalenceTensorIso X (integersResidueField ℓ E))
    (residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).symm

/-- `G_X` preserves flat objects, being an equivalence commuting with the tensor products. -/
instance preservesFlat_residueFieldModuleSheaf : (residueFieldModuleSheaf X ℓ E).PreservesFlat :=
  Functor.preservesFlat_of_isEquivalence_of_tensorIso _ (residueFieldModuleSheafTensorIso X ℓ E)

/-- On underlying abelian sheaves, `residueFieldModuleSheafIsoOfSection` is the identification
`residueFieldModuleSheafCompForgetIso`. -/
lemma sheafCompose_map_residueFieldModuleSheafIsoOfSection_hom_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)) :
    (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        ((residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).hom.app M) =
      (residueFieldModuleSheafCompForgetIso X).hom.app M :=
  Sheaf.sheafCompose_map_isoOfSheafComposeForget₂_hom_app (Λ := ResidueFieldCoeff.{u} ℓ E)
    (P := residueFieldModuleSheaf X ℓ E)
    (Q := (finiteCoefficientModEquivalence X (integersResidueField ℓ E)).functor) _ _ M

/-- On underlying abelian sheaves, the inverse of `residueFieldModuleSheafIsoOfSection` is the
identification `residueFieldModuleSheafCompForgetIso`. -/
lemma sheafCompose_map_residueFieldModuleSheafIsoOfSection_inv_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)) :
    (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        ((residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).inv.app M) =
      (residueFieldModuleSheafCompForgetIso X).inv.app M :=
  Sheaf.sheafCompose_map_isoOfSheafComposeForget₂_inv_app (Λ := ResidueFieldCoeff.{u} ℓ E)
    (P := residueFieldModuleSheaf X ℓ E)
    (Q := (finiteCoefficientModEquivalence X (integersResidueField ℓ E)).functor) _ _ M

/-- On underlying abelian sheaves, the tensor isomorphism of `G_X` precomposed with the projection
`M ⊗ N ⟶ M ⊗_{𝔽_{E,X}} N` is the tensor map `μ` of the underlying abelian sheaf functor. -/
@[reassoc]
lemma tensorObjπ_comp_map_residueFieldModuleSheafTensorIso_hom
    (A B : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)) :
    Mod.tensorObjπ A B ≫ (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        ((residueFieldModuleSheafTensorIso X ℓ E).iso A B).hom =
      Functor.LaxMonoidal.μ (sheafCompose (ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}))
        ((residueFieldModuleSheaf X ℓ E).obj A) ((residueFieldModuleSheaf X ℓ E).obj B) := by
  rw [residueFieldModuleSheafTensorIso, Functor.TensorIso.ofIso_iso_hom]
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.map_comp]
  rw [sheafCompose_map_residueFieldModuleSheafIsoOfSection_hom_app]
  erw [Category.id_comp, tensorObjπ_comp_map_finiteCoefficientModEquivalenceTensorIso_hom_assoc]
  refine (Functor.LaxMonoidal.μ_natural (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}))
      ((residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).inv.app A)
      ((residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).inv.app
        B)).symm.trans ?_
  rw [sheafCompose_map_residueFieldModuleSheafIsoOfSection_inv_app,
    sheafCompose_map_residueFieldModuleSheafIsoOfSection_inv_app]
  erw [MonoidalCategory.id_tensorHom_id,
    Category.id_comp]

/-- The form of `tensorObjπ_comp_map_residueFieldModuleSheafTensorIso_hom` with the components of
the natural transformation underlying the tensor isomorphism. -/
@[reassoc]
lemma tensorObjπ_comp_map_residueFieldModuleSheafTensorIso_hom_app_app
    (A B : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)) :
    Mod.tensorObjπ A B ≫ (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        (((residueFieldModuleSheafTensorIso X ℓ E).hom.app A).app B) =
      Functor.LaxMonoidal.μ (sheafCompose (ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}))
        ((residueFieldModuleSheaf X ℓ E).obj A) ((residueFieldModuleSheaf X ℓ E).obj B) :=
  tensorObjπ_comp_map_residueFieldModuleSheafTensorIso_hom X ℓ E A B

section Aux

attribute [local instance high] isTopologicalRing_residueField

set_option hygiene false in
local notation "residueFieldCommRingObj" =>
  @Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E) _ CommRing.toRing _

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On underlying abelian sheaves, the unit of the pullback of module objects followed by
`residueFieldModuleSheafUpperStarIsoAux` is the identification
`sheafComposeForget₂CompUpperStarIso` of the pullbacks of the underlying abelian sheaves. -/
@[reassoc]
lemma upperStarUnitHom_comp_map_residueFieldModuleSheafUpperStarIsoAux_hom_app {S T : Scheme.{u}}
    (a : S ⟶ T)
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (residueFieldCommRingObj) T)) :
    upperStarUnitHom (residueFieldCommRingObj) a M ≫
        (sheafCompose (ProEt.topology S)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
          ((residueFieldModuleSheafUpperStarIsoAux ℓ E a).hom.app M) =
      (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom.app
        ((residueFieldModuleSheaf T ℓ E).obj M) := by
  rw [sheafCompose_map_residueFieldModuleSheafUpperStarIsoAux_hom_app' ℓ E a M]
  erw [Sheaf.moduleLiftCompIso_hom_app, Sheaf.moduleLiftCompIso_inv_app, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [← upperStarForgetIso_hom_app, Iso.hom_inv_id_app_assoc]
  all_goals exact fun f c ↦ Mod.sectionActRingHom_comp_hom f _

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The natural form of
`upperStarUnitHom_comp_map_residueFieldModuleSheafUpperStarIsoAux_hom_app`. -/
lemma upperStarForgetIso_hom_comp_whiskerRight_residueFieldModuleSheafUpperStarIsoAux_hom
    {S T : Scheme.{u}} (a : S ⟶ T) :
    (upperStarForgetIso (residueFieldCommRingObj) a).hom ≫
        Functor.whiskerRight (residueFieldModuleSheafUpperStarIsoAux ℓ E a).hom
          (sheafCompose (ProEt.topology S)
            (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})) =
      Functor.whiskerLeft (residueFieldModuleSheaf T ℓ E)
        (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom := by
  ext M : 2
  exact upperStarUnitHom_comp_map_residueFieldModuleSheafUpperStarIsoAux_hom_app ℓ E a M

end Aux


omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On underlying abelian sheaves, the units of the pullbacks of module objects followed by
`residueFieldModuleSheafUpperStarIso` are the identifications
`sheafComposeForget₂CompUpperStarIso` of the pullbacks of the underlying abelian sheaves. -/
lemma upperStarForgetIso_hom_comp_whiskerRight_residueFieldModuleSheafUpperStarIso_hom
    {S T : Scheme.{u}} (a : S ⟶ T) :
    (upperStarForgetIso (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) a).hom ≫
        Functor.whiskerRight (residueFieldModuleSheafUpperStarIso ℓ E a).hom
          (sheafCompose (ProEt.topology S)
            (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})) =
      Functor.whiskerLeft (residueFieldModuleSheaf T ℓ E)
        (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom :=
  upperStarForgetIso_hom_comp_whiskerRight_residueFieldModuleSheafUpperStarIsoAux_hom ℓ E a

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On underlying abelian sheaves, the unit of the pullback of module objects followed by
`residueFieldModuleSheafUpperStarIso` is the identification `sheafComposeForget₂CompUpperStarIso`
of the pullbacks of the underlying abelian sheaves. -/
@[reassoc]
lemma upperStarUnitHom_comp_map_residueFieldModuleSheafUpperStarIso_hom_app {S T : Scheme.{u}}
    (a : S ⟶ T) (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (residueFieldRingObj T ℓ E)) :
    upperStarUnitHom (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) a M ≫
        (sheafCompose (ProEt.topology S)
          (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
          ((residueFieldModuleSheafUpperStarIso ℓ E a).hom.app M) =
      (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom.app
        ((residueFieldModuleSheaf T ℓ E).obj M) := by
  simpa using NatTrans.congr_app
    (upperStarForgetIso_hom_comp_whiskerRight_residueFieldModuleSheafUpperStarIso_hom ℓ E a) M

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Taking underlying abelian sheaves of a residue-field module map recovers its underlying map. -/
private lemma sheafCompose_map_residueFieldModuleSheaf_map
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)}
    (f : M ⟶ N) :
    (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map
        ((residueFieldModuleSheaf X ℓ E).map f) = f.hom :=
  rfl

/-- **The commutation of `G` with the pullbacks is compatible with the tensor products**: the
isomorphism `f^* ⋙ G_X ≅ G_Y ⋙ f^*` of `residueFieldModuleSheafUpperStarIso` is compatible with
the tensor isomorphisms of `G_X`, `G_Y` and the comonoidal structures of the pullbacks. On
underlying abelian sheaves, after the projection onto the relative tensor product, both
composites are the comonoidal structure of the pullback of abelian sheaves followed by the
tensor map of the underlying abelian sheaf functor. -/
lemma tensorCompatible_residueFieldModuleSheafUpperStarIso {S T : Scheme.{u}} (a : S ⟶ T) :
    NatTrans.TensorCompatible (residueFieldModuleSheafUpperStarIso ℓ E a).hom
      (Functor.TensorComparison.comp
        (Functor.OplaxMonoidal.δNatTrans
          (a)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧)
        (residueFieldModuleSheafTensorIso S ℓ E).hom)
      (Functor.TensorComparison.comp (residueFieldModuleSheafTensorIso T ℓ E).hom
        (Functor.OplaxMonoidal.δNatTrans
          (a)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])) := by
  intro M N
  apply (sheafCompose (ProEt.topology S)
    (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1})).map_injective
  rewrite [← cancel_epi ((a)^*[Ab.{u + 1}].map (Mod.tensorObjπ M N) ≫
    upperStarUnitHom (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) a (M ⊗ N))]
  simp only [Functor.map_comp, Category.assoc, Functor.TensorComparison.comp_app_app,
    Functor.OplaxMonoidal.δNatTrans_app_app]
  have hι := (sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a).hom.naturality
    (((residueFieldModuleSheafTensorIso T ℓ E).hom.app M).app N)
  dsimp at hι
  conv_lhs =>
    rw [upperStarUnitHom_comp_map_residueFieldModuleSheafUpperStarIso_hom_app_assoc
        ℓ E a (M ⊗ N),
      ← reassoc_of% hι, ← Functor.map_comp_assoc]
    rw [tensorObjπ_comp_map_residueFieldModuleSheafTensorIso_hom_app_app T ℓ E M N]
    rw [upperStar_map_μ_comp_sheafComposeForget₂CompUpperStarIso (ResidueFieldCoeff.{u} ℓ E) a
      ((residueFieldModuleSheaf T ℓ E).obj M) ((residueFieldModuleSheaf T ℓ E).obj N)]
  have hμ := Functor.LaxMonoidal.μ_natural (sheafCompose (ProEt.topology S)
      (forget₂ (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Ab.{u + 1}))
      ((residueFieldModuleSheafUpperStarIso ℓ E a).hom.app M)
      ((residueFieldModuleSheafUpperStarIso ℓ E a).hom.app N)
  simp only [Functor.comp_obj] at hμ
  conv_rhs =>
    rw [sheafCompose_map_residueFieldModuleSheaf_map S ℓ E,
      map_tensorObjπ_upperStarUnitHom_δ_hom_assoc
        (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) a M N]
    rw [tensorObjπ_comp_map_residueFieldModuleSheafTensorIso_hom_app_app_assoc S ℓ E
      ((a)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧.obj M)
      ((a)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧.obj N)]
    rw [← hμ, tensorHom_comp_tensorHom_assoc,
      upperStarUnitHom_comp_map_residueFieldModuleSheafUpperStarIso_hom_app ℓ E a M,
      upperStarUnitHom_comp_map_residueFieldModuleSheafUpperStarIso_hom_app ℓ E a N]
  rfl

end AlgebraicGeometry.ProEtale
