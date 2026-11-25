/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomSelfAdjunction
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Bidual
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorIdentification

/-!
# Hom complexes of `ℓ`-adic sheaves in the condensed model

Let `U : AdicSheaf l Y ⥤ Mod_{ℚ̲̄_ℓ,Y}` be the comparison of the two models of `ℓ`-adic sheaves
(forget the `ℚ̄_ℓ`-linear structure, then restrict scalars along the coefficient isomorphism).
This file records:

* the biduality morphisms of `ℓ`-adic sheaves satisfy the triangle identity
  (`CategoryTheory.Mod.bidual_comp_ihomMap_bidual`);
* precomposition with quasi-isomorphisms is a quasi-isomorphism of hom complexes of `ℓ`-adic
  sheaves into a K-injective complex
  (`AlgebraicGeometry.ProEtaleWeilSheaf.precompQuasiIso_ordinaryIhomBifunctor`);
* `U` commutes with internal homs, the internal hom of `ℓ`-adic sheaves being
  `ordinaryIhomBifunctor` and that of condensed modules the closed structure `Mod.monoidalClosed`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryIhomBifunctorMapIso`);
* hence, for a K-injective complex `I` with `F I ≅ W`, `F` the derived comparison, the functors
  `F ∘ RHom(-, I)` and `[F -, W]` are isomorphic
  (`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryRHomCondensedIso`), and the derived double-dual
  morphism of `ℓ`-adic complexes is invertible exactly where the double-dual morphism of the
  closed structure of the condensed model is
  (`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_bifunctorRHomBidual_app_iff`): both are units of
  self-adjunctions of isomorphic functors.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite
open MonoidalClosed hiding assoc id_comp comp_id
open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The triangle identity of the biduality morphisms: `Hom_A(M, N) ⟶ Hom_A(M, N)` obtained from
the biduality of `Hom_A(M, N)` followed by the dual of the biduality of `M` is the identity. -/
lemma bidual_comp_ihomMap_bidual (M N : Mod C A) :
    bidual ((ihom M).obj N) N ≫ (ihomMap (bidual M N)).app N = 𝟙 _ := by
  rw [bidual, ← transpose_comp, comp_id, bidual, transpose_transpose]

end CategoryTheory.Mod

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  (P : ObjectProperty C) [P.IsMonoidal] [P.IsMonoidalClosed]

/-- The double-dual morphism of a full monoidal closed braided subcategory is the double-dual
morphism of the ambient category. -/
lemma hom_toIhomIhom (W X : P.FullSubcategory) :
    (toIhomIhom W X).hom = toIhomIhom W.obj X.obj := by
  rw [toIhomIhom, toIhomIhom, curry_eq, curry_eq]
  rfl

end CategoryTheory.ObjectProperty

namespace CochainComplex

variable {C C' : Type*} [Category* C] [Preadditive C] [HasCountableProducts C]
  {H : Cᵒᵖ ⥤ C ⥤ C} [∀ X, (H.obj X).Additive] [H.Additive]
  [Category* C'] [Preadditive C'] [HasCountableProducts C']
  {H' : C'ᵒᵖ ⥤ C' ⥤ C'} [∀ X, (H'.obj X).Additive] [H'.Additive]
  {U : C ⥤ C'} [U.Additive]
  [∀ n : ℤ, PreservesLimitsOfShape (Discrete (HomComplex.Triplet n)) U]
  (φ : BifunctorMapIso H H' U)

/-- The identification `U (bifunctorHomObj H K Y) ≅ bifunctorHomObj H' (U K) (U Y)` is natural
in `K`. -/
@[reassoc]
lemma bifunctorHomObjMapIso_hom_naturality {K K' : CochainComplex C ℤ} (g : K' ⟶ K)
    (Y : CochainComplex C ℤ) :
    (U.mapHomologicalComplex _).map (bifunctorHomMapLeft (H := H) (Y := Y) g) ≫
        (bifunctorHomObjMapIso K' Y φ).hom =
      (bifunctorHomObjMapIso K Y φ).hom ≫
        bifunctorHomMapLeft (H := H') (Y := (U.mapHomologicalComplex _).obj Y)
          ((U.mapHomologicalComplex _).map g) := by
  ext n p q h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, assoc, assoc,
    bifunctorHomObjMapIso_hom_f_π, bifunctorHomMapLeft_f_π, bifunctorHomObjMapIso_hom_f_π_assoc,
    Functor.mapHomologicalComplex_map_f, ← U.map_comp_assoc, bifunctorHomMapLeft_f_π,
    U.map_comp, assoc, φ.naturality_left]
  rfl

end CochainComplex

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})

/-- The comparison `AdicSheaf l Y ⥤ Mod_{ℚ̲̄_ℓ,Y}` of the two models of `ℓ`-adic sheaves. -/
noncomputable abbrev ordinaryCondensedFunctor :
    ProEtale.AdicSheaf l Y ⥤ Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) Y) :=
  ProEtale.AdicSheaf.forgetAb l Y ⋙ Mod.comap (ProEtale.nativeModuleCoefficientIso l Y).hom

/-- The biduality morphisms of `ℓ`-adic sheaves satisfy the triangle identity. -/
lemma ordinaryBidual_triangle (a b : ProEtale.AdicSheaf l Y) :
    Mod.bidual ((ProEtale.AdicSheaf.ihom a).obj b) b ≫
      (Mod.ihomMap (Mod.bidual a b)).app b = 𝟙 _ :=
  Mod.bidual_comp_ihomMap_bidual a b

/-- Precomposition with a quasi-isomorphism is a quasi-isomorphism of hom complexes of `ℓ`-adic
sheaves into a K-injective complex. -/
theorem precompQuasiIso_ordinaryIhomBifunctor (I : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
    [I.IsKInjective] : DerivedCategory.PrecompQuasiIso (ordinaryIhomBifunctor l Y) I :=
  fun _ _ a _ ↦ PrecompositionAux.ordinaryQuasiIso a

instance : (ordinaryCondensedFunctor l Y).IsEquivalence := by
  have : (ProEtale.AdicSheaf.forgetAb l Y).IsEquivalence :=
    ProEtale.nativeScalarForgetting_isEquivalence l Y
  have : (Mod.comap (ProEtale.nativeModuleCoefficientIso l Y).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (ProEtale.nativeModuleCoefficientIso l Y).hom).isEquivalence_functor
  infer_instance

end AlgebraicGeometry.ProEtaleWeilSheaf

end

public section

open CategoryTheory Category Limits MonoidalCategory Opposite
open MonoidalClosed hiding assoc id_comp comp_id
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})

/-- A monoidal structure on the comparison of the two models of `ℓ`-adic sheaves. -/
@[instance_reducible]
noncomputable def ordinaryCondensedFunctorMonoidal : (ordinaryCondensedFunctor l Y).Monoidal :=
  letI : (ProEtale.AdicSheaf.forgetAb l Y).Monoidal :=
    (ProEtale.nativeScalarForgetting_monoidal l Y).some
  inferInstanceAs (ProEtale.AdicSheaf.forgetAb l Y ⋙
    Mod.comap (ProEtale.nativeModuleCoefficientIso l Y).hom).Monoidal

/-- The comparison of the two models of `ℓ`-adic sheaves commutes with internal homs. -/
noncomputable def ordinaryIhomBifunctorMapIso :
    CochainComplex.BifunctorMapIso (ordinaryIhomBifunctor l Y) MonoidalClosed.internalHom
      (ordinaryCondensedFunctor l Y) :=
  letI := ordinaryCondensedFunctorMonoidal l Y
  { iso a b := (ordinaryCondensedFunctor l Y).mapIso ((OrdinaryModuleHom.ihomIso a).app b) ≪≫
      Functor.Monoidal.ihomObjIso (ordinaryCondensedFunctor l Y) a b
    naturality_left {a a'} f b := by
      have h := congr_app (OrdinaryModuleHom.ihomIso_naturality f) b
      have h' := Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app
        (ordinaryCondensedFunctor l Y) f b
      simp only [NatTrans.comp_app] at h
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.Monoidal.ihomObjIso_hom,
        Functor.Monoidal.commIhom, asIso_hom]
      erw [← Functor.map_comp_assoc, h, Functor.map_comp, assoc, h']
      rfl
    naturality_right a {b b'} g := by
      have h := (OrdinaryModuleHom.ihomIso a).hom.naturality g
      have h' :=
        (Functor.LaxMonoidal.ihomComparison (ordinaryCondensedFunctor l Y) a).naturality g
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.Monoidal.ihomObjIso_hom,
        Functor.Monoidal.commIhom, asIso_hom]
      erw [← Functor.map_comp_assoc, h, Functor.map_comp, assoc, h']
      rfl }


section Comparison

variable {I : CochainComplex (ProEtale.AdicSheaf l Y) ℤ} [I.IsKInjective]
  {W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) Y))}

instance : (ordinaryCondensedFunctor l Y).PreservesKInjectiveComplexes :=
  have : (ordinaryCondensedFunctor l Y).asEquivalence.symm.functor.Additive :=
    haveI : (ordinaryCondensedFunctor l Y).asEquivalence.functor.Additive :=
      inferInstanceAs (ordinaryCondensedFunctor l Y).Additive
    Equivalence.inverse_additive _
  (ordinaryCondensedFunctor l Y).asEquivalence.symm.toAdjunction.preservesKInjectiveComplexes

/-- **The derived hom of `ℓ`-adic sheaves into `I` is the internal hom of the condensed model**:
for `F` the comparison of the two models of `ℓ`-adic complexes and `F(I) ≅ W`, the functors
`F ∘ RHom(-, I)` and `[F -, W]` are isomorphic. -/
noncomputable def ordinaryRHomCondensedIso
    (e : (ordinaryCondensedFunctor l Y).mapDerivedCategory.obj (DerivedCategory.Q.obj I) ≅ W) :
    DerivedCategory.bifunctorRHomOfComplex (ordinaryIhomBifunctor l Y) I ⋙
        (ordinaryCondensedFunctor l Y).mapDerivedCategory ≅
      (ordinaryCondensedFunctor l Y).mapDerivedCategory.op ⋙
        MonoidalClosed.internalHom.flip.obj W :=
  haveI := ProEtale.CondensedRing.isLeftDerivabilityStructure_localizerMorphismKFlat
    (Profinite.padicAlgClRingObj l) Y
  let U := ordinaryCondensedFunctor l Y
  let F := U.mapDerivedCategory
  let hI := precompQuasiIso_ordinaryIhomBifunctor l Y I
  let φ := ordinaryIhomBifunctorMapIso l Y
  let e₁ : DerivedCategory.Q.op ⋙ DerivedCategory.bifunctorRHomOfComplex
      (ordinaryIhomBifunctor l Y) I ≅
        DerivedCategory.bifunctorHomQFunctor (ordinaryIhomBifunctor l Y) I :=
    NatIso.ofComponents
      (fun M ↦ DerivedCategory.bifunctorRHomOfComplexQObjIso _ hI M.unop)
      (fun g ↦ DerivedCategory.bifunctorRHomOfComplexQObjIso_hom_naturality hI g.unop)
  let e₂ : DerivedCategory.bifunctorHomQFunctor (ordinaryIhomBifunctor l Y) I ⋙ F ≅
      (U.mapHomologicalComplex _).op ⋙ DerivedCategory.bifunctorHomQFunctor
        MonoidalClosed.internalHom ((U.mapHomologicalComplex _).obj I) :=
    NatIso.ofComponents
      (fun M ↦ (U.mapDerivedCategoryFactors.app _) ≪≫
        DerivedCategory.Q.mapIso (CochainComplex.bifunctorHomObjMapIso M.unop I φ))
      (fun {M M'} g ↦ by
        have h := U.mapDerivedCategoryFactors.hom.naturality
          (CochainComplex.bifunctorHomMapLeft (H := ordinaryIhomBifunctor l Y) (Y := I) g.unop)
        have h' := DerivedCategory.Q.congr_map
          (CochainComplex.bifunctorHomObjMapIso_hom_naturality φ g.unop I)
        simp only [Functor.map_comp] at h'
        simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, assoc]
        erw [reassoc_of% h, h']
        rfl)
  let e₃ := DerivedCategory.bifunctorHomQFunctorIsoIhom ((U.mapHomologicalComplex _).obj I)
  let eF : DerivedCategory.Q ⋙ F ≅ U.mapHomologicalComplex _ ⋙
      HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh :=
    U.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm
  let eW : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      ((U.mapHomologicalComplex _).obj I)) ≅ W :=
    (eF.app I).symm ≪≫ e
  let e₄ :=
    Functor.isoWhiskerRight (NatIso.op eF) (MonoidalClosed.internalHom.flip.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        ((U.mapHomologicalComplex _).obj I)))) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Q ⋙ F).op (MonoidalClosed.internalHom.flip.mapIso eW)
  Localization.liftNatIso DerivedCategory.Q.op
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).op
    (DerivedCategory.Q.op ⋙
      DerivedCategory.bifunctorRHomOfComplex (ordinaryIhomBifunctor l Y) I ⋙ F)
    (DerivedCategory.Q.op ⋙ F.op ⋙ MonoidalClosed.internalHom.flip.obj W) _ _
    (Functor.isoWhiskerRight e₁ F ≪≫ e₂ ≪≫ Functor.isoWhiskerLeft _ e₃ ≪≫ e₄)


/-- **Biduality of `ℓ`-adic complexes is biduality in the condensed model**: the derived
double-dual morphism `X ⟶ RHom(RHom(X, I), I)` of `ℓ`-adic complexes is an isomorphism if and
only if the double-dual morphism `F X ⟶ [[F X, W], W]` of the closed structure of the condensed
model is, for `F` the comparison of the two models and `F I ≅ W`. Both are units of
self-adjunctions of isomorphic functors (`ordinaryRHomCondensedIso`). -/
theorem isIso_bifunctorRHomBidual_app_iff
    [(HomotopyCategory.quasiIso (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) Y))
        (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]
    [BraidedCategory (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) Y)))]
    {E : CochainComplex.BifunctorEvaluation (ordinaryIhomBifunctor l Y)}
    (hE : E.TriangleIdentity)
    (e : (ordinaryCondensedFunctor l Y).mapDerivedCategory.obj (DerivedCategory.Q.obj I) ≅ W)
    (X : DerivedCategory (ProEtale.AdicSheaf l Y)) :
    IsIso ((DerivedCategory.bifunctorRHomBidual E
        (precompQuasiIso_ordinaryIhomBifunctor l Y I)).app X) ↔
      IsIso (toIhomIhom W ((ordinaryCondensedFunctor l Y).mapDerivedCategory.obj X)) := by
  let F := (ordinaryCondensedFunctor l Y).mapDerivedCategory
  let Fe := F.asEquivalence
  let adj₁ := DerivedCategory.bifunctorRHomSelfAdjunction
    (precompQuasiIso_ordinaryIhomBifunctor l Y I) hE
  let adj₂ := MonoidalClosed.ihomFlipSelfAdjunction W
  let Ψ := ordinaryRHomCondensedIso l Y e
  let iso : (DerivedCategory.bifunctorRHomOfComplex (ordinaryIhomBifunctor l Y) I).rightOp ⋙
      Fe.op.functor ≅ Fe.functor ⋙ (MonoidalClosed.internalHom.flip.obj W).rightOp :=
    NatIso.ofComponents (fun X ↦ (Ψ.app (op X)).op.symm)
      (fun f ↦ Quiver.Hom.unop_inj (Ψ.inv.naturality f.op).symm)
  have h := Adjunction.isIso_unit_app_iff_of_iso (adj₁.comp Fe.op.toAdjunction)
    (Fe.toAdjunction.comp adj₂) iso X
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    Equivalence.toAdjunction_unit, isIso_comp_right_iff, isIso_comp_left_iff,
    isIso_iff_of_reflects_iso _ Fe.inverse, MonoidalClosed.ihomFlipSelfAdjunction_unit_app] at h
  exact h

end Comparison

end AlgebraicGeometry.ProEtaleWeilSheaf
end
