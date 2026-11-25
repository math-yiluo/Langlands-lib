/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSingletonKoszulCone
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import all WeilConjectures.AlgebraicGeometry.IntegralConstantSectionProjection
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.SixFunctors.ProEtale.InternalDiscreteQuotientComparison

/-! # Residue-kernel powers annihilate the actual positive quotient maps

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
and proetale.tex, Lemma naive-completion (099M).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open scoped CategoryTheory.Obj
section Generic
universe v w
variable {A : Type v} [Category.{w} A] [Abelian A]
  [IsGrothendieckAbelian.{w} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [SymmetricCategory A]
open CategoryTheory.MonoidalCategory

private def extendTensorUnderlying {R S : A}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod A R) :
    (Mod.extendScalarsObj φ M).X ≅ ((Mod.comap φ).obj (Mod.regular S) ⊗ M).X where
  hom := Mod.extendDescHom φ (Mod.tensorObjπ ((Mod.comap φ).obj (Mod.regular S)) M) (by
    rw [← Mod.restrictedRegular_rightAction φ]
    exact Mod.tensorObjπ_condition ((Mod.comap φ).obj (Mod.regular S)) M)
  inv := coequalizer.desc (Mod.extendπ φ M) (by
    change (((β_ S R).hom ≫ Mod.act (A := R)
      ((Mod.comap φ).obj (Mod.regular S)).X) ▷ M.X) ≫ Mod.extendπ φ M = _
    rw [Mod.restrictedRegular_rightAction φ]
    exact Mod.extendπ_condition φ M)
  hom_inv_id := by
    apply coequalizer.hom_ext
    simp only [Mod.extendDescHom, Mod.extendπ, Mod.tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl
  inv_hom_id := by
    apply coequalizer.hom_ext
    simp only [Mod.extendDescHom, Mod.extendπ, Mod.tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl

private def extendComapTensorIso {R S : A}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod A R) :
    (Mod.comap φ).obj ((Mod.extendScalars φ).obj M) ≅
      (Mod.comap φ).obj (Mod.regular S) ⊗ M := by
  let e : ((Mod.comap φ).obj ((Mod.extendScalars φ).obj M)).X ≅
      ((Mod.comap φ).obj (Mod.regular S) ⊗ M).X := extendTensorUnderlying φ M
  refine Mod.isoMk e ?_
  apply (cancel_epi (R ◁ Mod.extendπ φ M)).mp
  rw [Mod.act_comap_obj]
  simp only [Category.assoc]
  erw [whisker_exchange_assoc, Mod.whiskerLeft_extendπ_smul_assoc]
  have he : Mod.extendπ φ M ≫ e.hom =
      Mod.tensorObjπ ((Mod.comap φ).obj (Mod.regular S)) M :=
    Mod.extendπ_extendDescHom φ _ _
  erw [he, ← whiskerLeft_comp_assoc, he,
    Mod.whiskerLeft_tensorπ_smul]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
  rfl

private theorem tensor_single_scalar_f (P : CochainComplex A ℤ)
    (s : End (𝟙_ A)) (q : ℤ) :
    (HomologicalComplex.rightUnitor P).inv.f q ≫
      (P ◁ (HomologicalComplex.single A (.up ℤ) 0).map s.asHom).f q ≫
        (HomologicalComplex.rightUnitor P).hom.f q = (unitEndAction (P.X q) s).asHom := by
  change (HomologicalComplex.rightUnitor' P).inv q ≫ _ ≫ _ = _
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  rw [HomologicalComplex.single_map_f_self]
  change (ρ_ (P.X q)).inv ≫
    P.X q ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv ≫
      (𝟙 (P.X q) ▷ _) ≫ P.X q ◁
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).hom ≫ s.asHom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv) ≫
        HomologicalComplex.ιTensorObj P (HomologicalComplex.tensorUnit A (.up ℤ))
          q 0 q (add_zero q) ≫ (HomologicalComplex.rightUnitor P).hom.f q = _
  simp only [id_whiskerRight, Category.id_comp, whiskerLeft_comp, Category.assoc]
  rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  have hu : P.X q ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv ≫
      HomologicalComplex.ιTensorObj P (HomologicalComplex.tensorUnit A (.up ℤ))
        q 0 q (add_zero q) ≫ (HomologicalComplex.rightUnitor P).hom.f q =
      (ρ_ (P.X q)).hom := by
    apply (cancel_epi (ρ_ (P.X q)).inv).mp
    rw [Iso.inv_hom_id]
    have hh := congrArg (fun f ↦ f.f q) (HomologicalComplex.rightUnitor P).inv_hom_id
    change (HomologicalComplex.rightUnitor' P).inv q ≫ _ = _ at hh
    rw [HomologicalComplex.rightUnitor'_inv] at hh
    simpa only [Category.assoc, HomologicalComplex.id_f] using hh
  rw [hu]
  rfl

end Generic

section SectionScalars
open scoped TensorProduct
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedTensor
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})
@[reducible] private local instance : MonoidalCategory (ConstantCompletion.Mod O) :=
  SheafOfModules.monoidalCategory O
private local instance : SymmetricCategory (ConstantCompletion.Mod O) :=
  SheafOfModules.symmetricCategory O
private local instance : MonoidalPreadditive (ConstantCompletion.Mod O) :=
  Classical.choice (SheafOfModules.tensorClosed O).1

private abbrev inclusion := SheafOfModules.forget
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⋙
    PresheafOfModules.restrictScalars (𝟙 _)

@[reducible] private noncomputable instance inclusionLax : (inclusion O).LaxMonoidal :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 _)).rightAdjointLaxMonoidal

private theorem inclusion_unit : Functor.LaxMonoidal.ε (inclusion O) =
    𝟙 (𝟙_ (PresheafOfModules.{u} (O.obj ⋙ forget₂ CommRingCat RingCat))) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O) (𝟙 _)
  let F := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O) (𝟙 _)
  have hη : Functor.OplaxMonoidal.η F =
      adj.counit.app (SheafOfModules.unit (siteModuleRings O)) := by
    change (SheafOfModules.sheafificationObjUnitIso O).hom = _
    rfl
  change adj.homEquiv _ _ (Functor.OplaxMonoidal.η F) = _
  erw [hη, Adjunction.homEquiv_unit]
  exact adj.right_triangle_components (𝟙_ (ConstantCompletion.Mod O))

private theorem pure_rightUnitor (M : ConstantCompletion.Mod O) (U : Cᵒᵖ)
    (x : M.val.obj U) (r : O.obj.obj U) :
    (ρ_ M).hom.val.app U (pure O M (SheafOfModules.unit (siteModuleRings O)) U x r) = r • x := by
  have h := Functor.LaxMonoidal.right_unitality (inclusion O) M
  erw [inclusion_unit] at h
  change (ρ_ (inclusion O |>.obj M)).hom =
    ((inclusion O).obj M ◁ 𝟙 (PresheafOfModules.unit (O.obj ⋙ forget₂ CommRingCat RingCat))) ≫
      Functor.LaxMonoidal.μ (inclusion O) M (SheafOfModules.unit (siteModuleRings O)) ≫
        (inclusion O).map (ρ_ M).hom at h
  erw [whiskerLeft_id, Category.id_comp] at h
  exact congrArg (fun k ↦ (k.app U) (x ⊗ₜ[O.obj.obj U] r)) h.symm

private def sectionScalar (a : (O.obj ⋙ forget CommRingCat).sections)
    (M : ConstantCompletion.Mod O) : End M :=
  End.of ⟨PresheafOfModules.sectionsSMul M.val ⟨a.val, a.property⟩⟩

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.sheafCompose

private theorem unit_action_apply (M : ConstantCompletion.Mod O)
    (s : End (SheafOfModules.unit (siteModuleRings O))) (U : Cᵒᵖ) (x : M.val.obj U) :
    (unitEndAction M s).asHom.val.app U x =
      (show O.obj.obj U from s.asHom.val.app U (1 : O.obj.obj U)) • x := by
  have h : M ◁ s.asHom ≫ (ρ_ M).hom = (ρ_ M).hom ≫
      (sectionScalar O (SheafOfModules.unitHomEquiv _ s.asHom) M).asHom := by
    apply pure_hom_ext O M (SheafOfModules.unit (siteModuleRings O)) M
    intro V m r
    let r₀ : O.obj.obj V := r
    let F : O.obj.obj V →ₗ[O.obj.obj V] O.obj.obj V := (s.asHom.val.app V).hom
    have ht : (M ◁ s.asHom).val.app V
        (pure O M (SheafOfModules.unit (siteModuleRings O)) V m r) =
        pure O M (SheafOfModules.unit (siteModuleRings O)) V m (F r₀) := by
      calc
        _ = (𝟙 M ⊗ₘ s.asHom).val.app V
            (pure O M (SheafOfModules.unit (siteModuleRings O)) V m r) :=
          congrArg (fun f ↦ f.val.app V
            (pure O M (SheafOfModules.unit (siteModuleRings O)) V m r))
              (id_tensorHom M s.asHom).symm
        _ = _ := pure_map O (𝟙 M) s.asHom V m r
    have hF : F r₀ = F 1 * r₀ := by
      have hh := F.map_smul r₀ (1 : O.obj.obj V)
      simpa only [smul_eq_mul, mul_one, mul_comm] using hh
    change (ρ_ M).hom.val.app V ((M ◁ s.asHom).val.app V
      (pure O M (SheafOfModules.unit (siteModuleRings O)) V m r)) =
        F 1 • ((ρ_ M).hom.val.app V
          (pure O M (SheafOfModules.unit (siteModuleRings O)) V m r))
    calc
      _ = (ρ_ M).hom.val.app V
          (pure O M (SheafOfModules.unit (siteModuleRings O)) V m (F r₀)) :=
        congrArg ((ρ_ M).hom.val.app V) ht
      _ = F r₀ • m := pure_rightUnitor O M V m (F r₀)
      _ = F 1 • (r₀ • m) := by rw [hF, mul_smul]
      _ = _ := congrArg (fun x ↦ F 1 • x) (pure_rightUnitor O M V m r₀).symm
  have hh := congrArg (fun f ↦ f.val.app U x)
    (congrArg (fun f ↦ (ρ_ M).inv ≫ f) h)
  simp only [Iso.inv_hom_id_assoc] at hh
  change (unitEndAction M s).asHom.val.app U x =
    (show O.obj.obj U from s.asHom.val.app U (1 : O.obj.obj U)) • x at hh
  exact hh

private theorem koszul_scalar_power_apply
    (a : (O.obj ⋙ forget CommRingCat).sections) (k : ℕ) (U : Cᵒᵖ)
    (r : O.obj.obj U) : (ringedKoszulScalar O a ^ k).asHom.val.app U r = a.val U ^ k * r := by
  induction k generalizing r with
  | zero => simp [End.one_asHom]
  | succ k ih =>
    erw [pow_succ, End.mul_asHom]
    change (ringedKoszulScalar O a ^ k).asHom.val.app U
      ((ringedKoszulScalar O a).asHom.val.app U r) = _
    erw [ih]
    have h : (ringedKoszulScalar O a).asHom.val.app U r = a.val U * r := by
      let F : O.obj.obj U →ₗ[O.obj.obj U] O.obj.obj U :=
        ((ringedKoszulScalar O a).asHom.val.app U).hom
      have h1 : F 1 = a.val U := by
        let e := SheafOfModules.unitHomEquiv (SheafOfModules.unit (siteModuleRings O))
        have he := e.apply_symm_apply ⟨a.val, a.property⟩
        exact congrArg (fun t ↦ t.val U) he
      change F r = _
      calc
        _ = r * F 1 := by
          simpa only [smul_eq_mul, mul_one] using F.map_smul r (1 : O.obj.obj U)
        _ = _ := by rw [h1, mul_comm]
    erw [h, pow_succ, mul_assoc]

private theorem scalar_power_zero_of_restriction
    (D : Sheaf J CommRingCat.{u}) (φ : O ⟶ D)
    (a : (O.obj ⋙ forget CommRingCat).sections) (k : ℕ)
    (h : ∀ U : Cᵒᵖ, φ.hom.app U (a.val U ^ k) = 0)
    (M : ConstantCompletion.Mod O) (L : ConstantCompletion.Mod D)
    (e : (ConstantCompletion.res φ).obj L ≅ M) :
    unitEndAction M (ringedKoszulScalar O a ^ k) = 0 := by
  apply End.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [unit_action_apply, koszul_scalar_power_apply, mul_one]
  change a.val U ^ k • x = 0
  have hinj : Function.Injective (e.inv.val.app U) := by
    apply Function.LeftInverse.injective (g := e.hom.val.app U)
    intro y
    exact ConcreteCategory.congr_hom
      (congrArg (fun t ↦ t.val.app U) e.inv_hom_id) y
  apply hinj
  rw [map_zero, map_smul]
  change φ.hom.app U (a.val U ^ k) •
    (show L.val.obj U from e.inv.val.app U x) = 0
  rw [h U, zero_smul]

end SectionScalars

section PointConstants
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.IntegralModelsStacks

private abbrev liftRingMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{u + 1} A →+* ULift.{u + 1} B :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

private abbrev discreteContinuous (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteObj A ⟶ Profinite.continuousCoefficientRingObj A :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (constantToContinuous A)

private theorem discreteContinuous_natural (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B)
    (g : Profinite.continuousCoefficientRingObj A ⟶ Profinite.continuousCoefficientRingObj B)
    (h : FiniteConstantModel.constantFunctions A ≫ g.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom (liftRingMap f).toAddMonoidHom) ≫
          FiniteConstantModel.constantFunctions B) :
    discreteContinuous A ≫ g = discreteMap f ≫ discreteContinuous B := by
  let J := coherentTopology Profinite.{u}
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : PreservesFilteredColimits V :=
    comp_preservesFilteredColimits (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : J.PreservesSheafification V := GrothendieckTopology.instPreservesSheafification _ _
  let q : CommRingCat.of (ULift.{u + 1} A) ⟶ CommRingCat.of (ULift.{u + 1} B) :=
    CommRingCat.ofHom (liftRingMap f)
  have hn : (pointConstantAbIso A).hom ≫ discreteMap f =
      (constantSheaf J Ab.{u + 1}).map (V.map q) ≫ (pointConstantAbIso B).hom :=
    ((constantCommuteCompose J V).inv.naturality q).symm
  have hs : FiniteConstantModel.scalarToContinuous A ≫ g =
      (constantSheaf J Ab.{u + 1}).map (V.map q) ≫
        FiniteConstantModel.scalarToContinuous B := by
    have hA := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
        (Profinite.continuousCoefficientRingObj A)).apply_symm_apply
          (FiniteConstantModel.constantFunctions A)
    have hB := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
        (Profinite.continuousCoefficientRingObj B)).apply_symm_apply
          (FiniteConstantModel.constantFunctions B)
    rw [Adjunction.homEquiv_unit] at hA hB
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (Profinite.continuousCoefficientRingObj B).property
    change toSheafify J _ ≫ (FiniteConstantModel.scalarToContinuous A).hom ≫ g.hom =
      toSheafify J _ ≫ sheafifyMap J ((Functor.const Profinite.{u}ᵒᵖ).map (V.map q)) ≫
        (FiniteConstantModel.scalarToContinuous B).hom
    calc
      _ = FiniteConstantModel.constantFunctions A ≫ g.hom := by
        erw [← Category.assoc, hA]
      _ = (Functor.const Profinite.{u}ᵒᵖ).map (V.map q) ≫
          FiniteConstantModel.constantFunctions B := h
      _ = (Functor.const Profinite.{u}ᵒᵖ).map (V.map q) ≫
          (toSheafify J _ ≫ (FiniteConstantModel.scalarToContinuous B).hom) :=
        congrArg (fun t ↦ (Functor.const Profinite.{u}ᵒᵖ).map (V.map q) ≫ t) hB.symm
      _ = _ := by rw [← Category.assoc, toSheafify_naturality, Category.assoc]
  apply (cancel_epi (pointConstantAbIso A).hom).mp
  calc
    _ = ((pointConstantAbIso A).hom ≫ discreteContinuous A) ≫ g :=
      (Category.assoc _ _ _).symm
    _ = FiniteConstantModel.scalarToContinuous A ≫ g :=
      congrArg (fun t ↦ t ≫ g) (pointConstantAbIso_scalar A)
    _ = (constantSheaf J Ab.{u + 1}).map (V.map q) ≫
        FiniteConstantModel.scalarToContinuous B := hs
    _ = (constantSheaf J Ab.{u + 1}).map (V.map q) ≫
        ((pointConstantAbIso B).hom ≫ discreteContinuous B) :=
      congrArg (fun t ↦ (constantSheaf J Ab.{u + 1}).map (V.map q) ≫ t)
        (pointConstantAbIso_scalar B).symm
    _ = _ := by rw [← Category.assoc, ← hn, Category.assoc]

end PointConstants

namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private local instance actualAbSheafify : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X
private local instance actualSiteSmall : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local irreducible] IntegralConstantModel.pointComparison upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric
  AdicCompletion.modulesClosed AdicCompletion.modulesMonoidalPreadditive

private abbrev discreteFiniteRing (n : ℕ) :=
  IntegralModelsStacks.smallRing X
    (condensedRingObj (IntegralModelsStacks.discreteObj
      (Padic.coefficientExtensionRing l E (n + 1))) X)

private abbrev discreteFiniteMap (n : ℕ) : ring l E X ⟶ discreteFiniteRing l E X n :=
  IntegralModelsStacks.smallMap X ((upperStarFromPoint X).map
    (IntegralModelsStacks.discreteMap
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))))

private theorem discreteFinite_square (n : ℕ) :
    ∃ f : IntegralConstantCompletion.finiteRing l E X n ≅ discreteFiniteRing l E X n,
      IntegralConstantCompletion.quotientMap l E X false n ≫ f.hom =
        (IntegralModelsStacks.smallIso X (Padic.coefficientExtensionIntegers l E)).hom ≫
          discreteFiniteMap l E X n := by
  let A := Padic.coefficientExtensionIntegers l E
  let B := ULift.{u + 1} A
  let I := Padic.coefficientExtensionIdeal l E (n + 1)
  let K := IntegralConstantCompletion.ideal l E
  have hI : K ^ (n + 1) = Ideal.map ULift.ringEquiv.symm.toRingHom I := by
    simp only [K, I, IntegralConstantCompletion.ideal, Padic.coefficientExtensionIdeal,
      Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_pow]
    rfl
  let q : (A ⧸ I) ≃+* (B ⧸ K ^ (n + 1)) :=
    Ideal.quotientEquiv I (K ^ (n + 1)) ULift.ringEquiv.symm hI
  let t : (B ⧸ K ^ (n + 1)) ≃+* ULift.{u + 1} (A ⧸ I) :=
    q.symm.trans ULift.ringEquiv.symm
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let f := (constantSheaf J CommRingCat.{u + 1}).mapIso t.toCommRingCatIso ≪≫
    IntegralModelsStacks.smallIso X (A ⧸ I)
  refine ⟨f, ?_⟩
  change (constantSheaf J CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (K ^ (n + 1)))) ≫
      ((constantSheaf J CommRingCat.{u + 1}).map t.toCommRingCatIso.hom ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp]
  have ht : CommRingCat.ofHom (Ideal.Quotient.mk (K ^ (n + 1))) ≫
      t.toCommRingCatIso.hom = CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change ULift.up (q.symm (Ideal.Quotient.mk _ b)) = _
    rw [Ideal.quotientEquiv_symm_mk]
    rfl
  rw [ht]
  exact IntegralModelsStacks.smallIso_naturality X (Ideal.Quotient.mk I)

private theorem discreteFinite_residue_power
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      (residue l E X).hom.app (op U) (a.val (op U)) = 0)
    (n : ℕ) (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :
    (discreteFiniteMap l E X n).hom.app (op U) (a.val (op U) ^ (n + 1)) = 0 := by
  let e := IntegralModelsStacks.smallIso X (Padic.coefficientExtensionIntegers l E)
  let b := e.inv.hom.app (op U) (a.val (op U))
  have heb : e.hom.hom.app (op U) b = a.val (op U) :=
    ConcreteCategory.congr_hom (congrArg (fun q ↦ q.hom.app (op U)) e.inv_hom_id) _
  obtain ⟨f₀, hf₀⟩ := discreteFinite_square l E X 0
  have hb₀ : (IntegralConstantCompletion.quotientMap l E X false 0).hom.app (op U) b =
      0 := by
    apply (ConcreteCategory.bijective_of_isIso (f₀.hom.hom.app (op U))).injective
    have h := ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app (op U)) hf₀) b
    change f₀.hom.hom.app (op U)
      ((IntegralConstantCompletion.quotientMap l E X false 0).hom.app (op U) b) =
      (discreteFiniteMap l E X 0).hom.app (op U) (e.hom.hom.app (op U) b) at h
    rw [heb] at h
    simpa only [map_zero] using h.trans (ha U)
  have hb : b ∈ Ideal.span
      {((ConstantCompletion.algebraSection
        (ConstantCompletion.baseMap (IntegralConstantCompletion.topology X)
          (IntegralConstantCompletion.integers l E) (IntegralConstantCompletion.ideal l E)
            false) (ULift.up (Padic.coefficientExtensionUniformizer l E))).val (op U))} := by
    have h : b ∈ RingHom.ker
        ((IntegralConstantCompletion.quotientMap l E X false 0).hom.app (op U)).hom := hb₀
    rw [IntegralConstantCompletion.finite_kernel l E X false 0 U] at h
    simpa only [Nat.zero_add, pow_one] using h
  have hbn : (IntegralConstantCompletion.quotientMap l E X false n).hom.app (op U)
      (b ^ (n + 1)) = 0 := by
    have h := Ideal.pow_mem_pow hb (n + 1)
    rw [Ideal.span_singleton_pow,
      ← IntegralConstantCompletion.finite_kernel l E X false n U] at h
    exact h
  obtain ⟨f, hf⟩ := discreteFinite_square l E X n
  have h := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.hom.app (op U)) hf) (b ^ (n + 1))
  change f.hom.hom.app (op U)
      ((IntegralConstantCompletion.quotientMap l E X false n).hom.app (op U)
        (b ^ (n + 1))) = (discreteFiniteMap l E X n).hom.app (op U)
          (e.hom.hom.app (op U) (b ^ (n + 1))) at h
  rw [hbn, map_zero, map_pow, heb] at h
  exact h.symm

private def finiteScalarPoint (n : ℕ) :
    IntegralModelsStacks.discreteObj (Padic.coefficientExtensionRing l E (n + 1)) ⟶
      DerivedNakayama.quotientRing l E (n + 1) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (IntegralModelsStacks.constantToContinuous (Padic.coefficientExtensionRing l E (n + 1)))

private instance finiteScalarPoint_mon (n : ℕ) : IsMonHom (finiteScalarPoint l E n) := by
  unfold finiteScalarPoint
  infer_instance

set_option linter.style.haveILetI false in
private theorem finiteScalarPoint_square (n : ℕ) :
    IntegralModelsStacks.scalarPointMap l E ≫
        (IntegralConstantModel.pointComparison l E).inv.hom ≫
          DerivedNakayama.reductionRing l E (n + 1) =
      IntegralModelsStacks.discreteMap
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ≫
        finiteScalarPoint l E n := by
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionRing l E (n + 1)
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let tB : TopologicalSpace B := inferInstance
  have hB : @IsTopologicalRing B tB _ := inferInstance
  let tA : TopologicalSpace A := by
    letI := spectralNorm.normedField (Padic l) E
    infer_instance
  letI : TopologicalSpace A := tA
  have : IsTopologicalRing A := by
    letI := spectralNorm.normedField (Padic l) E
    infer_instance
  letI : TopologicalSpace B := tB
  letI : IsTopologicalRing B := hB
  let f := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
  let g : Profinite.continuousCoefficientRingObj A ⟶
      Profinite.continuousCoefficientRingObj B :=
    (IntegralConstantModel.pointComparison l E).inv.hom ≫
      DerivedNakayama.reductionRing l E (n + 1)
  have hc : FiniteConstantModel.constantFunctions A ≫ g.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom (liftRingMap f).toAddMonoidHom) ≫
          FiniteConstantModel.constantFunctions B := by
    dsimp only [g]
    rw [IntegralModelsStacks.pointComparison_inv_eq]
    ext S a
    rfl
  exact discreteContinuous_natural A B f g hc

private def smallComapIso
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (M : Mod _ S) :
    (IntegralModelsStacks.smallModules X R).obj ((Mod.comap a).obj M) ≅
      (ConstantCompletion.res (IntegralModelsStacks.smallMap X a)).obj
        ((IntegralModelsStacks.smallModules X S).obj M) := by
  let e := (InternalAbelianSheafModule.scalarRestrictionIso.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) a).app M
  exact (SheafOfModules.pushforward (F := AsSmall.down) (𝟙 _)).mapIso e

private theorem finiteModuleStructure (M : AdicCompletion.Modules l E X) (n : ℕ) :
    ∃ L : ConstantCompletion.Mod.{u + 1} (discreteFiniteRing l E X n),
      Nonempty ((ConstantCompletion.res (discreteFiniteMap l E X n)).obj L ≅
        (modules l E X).obj ((AdicCompletion.modulesMonoidal l E X).tensorObj M
          (AdicCompletion.finiteModule l E X n))) := by
  let c := coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
  let b := IntegralModelsStacks.scalarMap l E X
  let q := AdicCompletion.quotient l E X n
  let d := (upperStarFromPoint X).map (IntegralModelsStacks.discreteMap
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))
  let z := (upperStarFromPoint X).map (finiteScalarPoint l E n)
  have sq : b ≫ c ≫ q = d ≫ z := by
    dsimp only [b, c, q, d, z, IntegralModelsStacks.scalarMap, coefficientMap,
      AdicCompletion.quotient]
    rw [← Functor.map_comp, ← Functor.map_comp, finiteScalarPoint_square, Functor.map_comp]
  let : HasCoequalizers (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    Abelian.hasCoequalizers
  let T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n) := (Mod.extendScalars.{u + 1, u + 2} q).obj M
  let B := (Mod.comap z).obj T
  let L := (IntegralModelsStacks.smallModules X _).obj B
  let t : (Mod.comap q).obj T ≅ M ⊗ AdicCompletion.finiteModule l E X n :=
    extendComapTensorIso q M ≪≫
      (β_ ((Mod.comap q).obj (Mod.regular (AdicCompletion.finiteRing l E X n))) M) ≪≫
        tensorIso (Iso.refl M) (AdicCompletion.finiteModuleIso l E X n).symm
  refine ⟨L, ⟨?_⟩⟩
  refine (smallComapIso X d B).symm ≪≫
    (IntegralModelsStacks.smallModules X _).mapIso ((Mod.comapComp d z).symm.app T) ≪≫
    (IntegralModelsStacks.smallModules X _).mapIso ((Mod.comapCongr sq.symm).app T) ≪≫
    (IntegralModelsStacks.smallModules X _).mapIso ((Mod.comapComp b (c ≫ q)).app T) ≪≫
    (IntegralModelsStacks.smallModules X _).mapIso
      ((Mod.comap b).mapIso ((Mod.comapComp c q).app T)) ≪≫ ?_
  unfold modules
  exact (Mod.comap c ⋙ Mod.comap b ⋙
    IntegralModelsStacks.smallModules X (constantRing l E X)).mapIso t

private local instance scalarModulesGrothendieck :
    IsGrothendieckAbelian.{u + 1} (ConstantCompletion.Mod (ring l E X)) :=
  SheafOfModules.isGrothendieckAbelian _
@[reducible] private local instance scalarModulesMonoidal :
    MonoidalCategory (ConstantCompletion.Mod (ring l E X)) :=
  SheafOfModules.monoidalCategory.{u + 1} (ring l E X)
private local instance scalarModulesSymmetric :
    SymmetricCategory (ConstantCompletion.Mod (ring l E X)) :=
  SheafOfModules.symmetricCategory.{u + 1} (ring l E X)
private local instance scalarModulesPreadditive :
    MonoidalPreadditive (ConstantCompletion.Mod (ring l E X)) :=
  Classical.choice (SheafOfModules.tensorClosed (ring l E X)).1
private local instance scalarModulesClosed : MonoidalClosed (ConstantCompletion.Mod (ring l E X)) :=
  Classical.choice (SheafOfModules.tensorClosed (ring l E X)).2.1

/-- The sole arithmetic input for constructing the finite augmentation: the
(n+1)st power of a residue-zero scalar kills the actual level-n quotient unit.
There is no Koszul augmentation or choice of chain maps in this assertion.

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
and proetale.tex, Lemma naive-completion (099M).
(auxiliary; not a blueprint node).

Proof: the kernel of the discrete residue map is the sheaf ideal generated by
the constant uniformizer pi. This follows from the quotient description of the
constant coefficient sheaves and the point coefficient comparison. Locally a
residue-zero section is pi times a section. Its (n+1)st power is therefore
pi^(n+1) times a section, and is zero in the actual positive quotient
O_E/pi^(n+1). The finite coefficient identifications ensure that this is the
prescribed quotient, with its prescribed quotient map. On a term of P the
quotient unit sends x to x tensor 1. Balancing moves multiplication by a^(n+1)
to the quotient factor, where it is zero by the preceding local calculation.
Scalar restriction and the section-action equivalence preserve this equality.
The tensor of the positive scalar power followed by the right unitor is
termwise this same multiplication: only degree zero occurs in O[0], and
unitors send x tensor 1 to x. Equality is local for sheaf morphisms, so the local zero
equalities give zero on each term, and complex extensionality proves the claim. No
boundedness, flatness, or regularity is used; zero objects and the empty
scheme satisfy the same zero equations. -/
theorem quotient_scalar_annihilation
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      (residue l E X).hom.app (op U) (a.val (op U)) = 0)
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
    (ringedSingletonKoszulPower (ring l E X) a (complex l E X P) n).asHom ≫
      (ringedKoszulRightUnitIso (ring l E X) (complex l E X P)).hom ≫
        (quotientUnits l E X P).app (op n) = 0 := by
  let O := ring l E X
  let N := complex l E X P
  let Q := (quotients l E X P).obj (op n)
  let f := (quotientUnits l E X P).app (op n)
  let s := ringedKoszulScalar O a ^ (n + 1)
  have hz (q : ℤ) : unitEndAction (Q.X q) s = 0 := by
    obtain ⟨L, ⟨e⟩⟩ := finiteModuleStructure l E X (P.X q) n
    change (ConstantCompletion.res (discreteFiniteMap l E X n)).obj L ≅ Q.X q at e
    exact scalar_power_zero_of_restriction (ring l E X) (discreteFiniteRing l E X n)
      (discreteFiniteMap l E X n) a (n + 1)
      (fun U ↦ discreteFinite_residue_power l E X a ha n U.unop) (Q.X q) L e
  apply HomologicalComplex.hom_ext
  intro q
  apply (cancel_epi ((HomologicalComplex.rightUnitor N).inv.f q)).mp
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, comp_zero]
  unfold ringedSingletonKoszulPower ringedKoszulTensor ringedKoszulRightUnitIso
  change (HomologicalComplex.rightUnitor N).inv.f q ≫
      (N ◁ (HomologicalComplex.single _ (.up ℤ) 0).map s.asHom).f q ≫
        (HomologicalComplex.rightUnitor N).hom.f q ≫ f.f q = 0
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc _ _ ((HomologicalComplex.rightUnitor N).hom.f q),
    tensor_single_scalar_f, unitEndAction_naturality, hz, End.zero_asHom, comp_zero]

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
