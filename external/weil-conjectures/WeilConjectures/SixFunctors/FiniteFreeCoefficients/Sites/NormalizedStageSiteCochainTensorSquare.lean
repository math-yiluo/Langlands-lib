/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageSiteSheafTensorSquare

/-!
# Signed cochain lift of the scalar/site tensor square

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 07A4 and 0G7E;
finite coefficient scalar/site transport in the blueprint
lemma-change-coefficients-exceptional-inverse-image--3, Paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace WeilConjectures.FiniteFreeCoefficients.Sites

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- The sheafified scalar balancing tensorator `etaleScalarOplax` of
-- `NormalizedStageSiteSheafTensorSquare` is a local instance there.
attribute [local instance] etaleScalarOplax

-- The ordinary etale scalar extension is a left adjoint (Stacks 06YY), so it preserves the
-- coproducts of the signed total tensor; `ExceptionalCoefficientMaps` is not imported here.
local instance etaleScalarIsLeftAdjoint {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).IsLeftAdjoint :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ X).isLeftAdjoint

/-- The termwise canonical scalar/site mate on ordinary cochain complexes.
Source: Stacks 03EL and 07A4
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev scalarSiteCochain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  (NatTrans.mapHomologicalComplex
    (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv (.up ℤ)).app P

/-- Signed total tensor comparison for the etale-to-pro-etale inverse image.
Its homogeneous summands are the ordinary site tensor maps.
Source: Stacks 03EL and 07A4
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev siteTensorCochain (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)).app P).app Q

/-- Signed total tensor comparison for ordinary etale scalar extension.
Source: Stacks 07A4, normalized scalar tensor maps
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev etaleScalarTensorCochain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.etaleSheafExtendScalars φ X)).app P).app Q

/-- Signed total tensor comparison for ordinary pro-etale scalar extension.
Source: Stacks 07A4, normalized scalar tensor maps
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
abbrev proEtaleScalarTensorCochain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P Q : CochainComplex
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :=
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.sheafExtendScalars φ X)).app P).app Q

section SummandFormulas

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- On a summand of the signed total tensor, the cochain tensor comparison of an additive
oplax monoidal functor is its ordinary comparison `δ`.
Source: Stacks 0FPT (blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
@[reassoc]
theorem map_ιMapBifunctor_mapHomologicalComplexδ (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (K L : CochainComplex C ℤ) (p q n : ℤ)
    (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n) :
    G.map (HomologicalComplex.ιMapBifunctor K L (curriedTensor C) (.up ℤ) p q n h) ≫
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app K).app L).f n =
      Functor.OplaxMonoidal.δ G (K.X p) (L.X q) ≫
        HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor D) (.up ℤ) p q n h :=
  HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans G) (.up ℤ) K L p q n h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- On a summand of the signed total tensor, a tensor product of cochain maps is the
tensor product of its components.
Source: Stacks 0FPT (blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
@[reassoc]
theorem ιMapBifunctor_tensorHom_f {K K' L L' : CochainComplex C ℤ} (f : K ⟶ K')
    (g : L ⟶ L') (p q n : ℤ) (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor K L (curriedTensor C) (.up ℤ) p q n h ≫ (f ⊗ₘ g).f n =
      (f.f p ⊗ₘ g.f q) ≫
        HomologicalComplex.ιMapBifunctor K' L' (curriedTensor C) (.up ℤ) p q n h := by
  refine (HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor C) (.up ℤ) p q n h).trans ?_
  simp [MonoidalCategory.tensorHom_def]

end SummandFormulas

section SquareOfSummands

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  [Preadditive C] [MonoidalCategory C] [HasZeroObject C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Preadditive C'] [MonoidalCategory C'] [HasZeroObject C'] [MonoidalPreadditive C']
  [∀ (X₁ X₂ : GradedObject ℤ C'), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C') ((curriedTensor C').obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C') ((curriedTensor C').flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C'), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C'), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C'), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Preadditive D] [MonoidalCategory D] [HasZeroObject D] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Preadditive D'] [MonoidalCategory D'] [HasZeroObject D'] [MonoidalPreadditive D']
  [∀ (X₁ X₂ : GradedObject ℤ D'), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D') ((curriedTensor D').obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D') ((curriedTensor D').flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D'), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- A square of additive oplax monoidal functors whose ordinary tensor comparisons commute
induces the same square on signed total tensors of cochain complexes.
Source: Stacks 0FPT (blueprint: lem-sf-normalized-stage-site-cochain-tensor-square). -/
theorem mapHomologicalComplexδ_square (ν : C ⥤ C') (F : C' ⥤ D') (F' : C ⥤ D) (ν' : D ⥤ D')
    [ν.Additive] [F.Additive] [F'.Additive] [ν'.Additive]
    [ν.OplaxMonoidal] [F.OplaxMonoidal] [F'.OplaxMonoidal] [ν'.OplaxMonoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) ν]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F']
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) ν']
    (σ : ν ⋙ F ⟶ F' ⋙ ν')
    (h : ∀ M N : C, F.map (Functor.OplaxMonoidal.δ ν M N) ≫
        Functor.OplaxMonoidal.δ F (ν.obj M) (ν.obj N) ≫ (σ.app M ⊗ₘ σ.app N) =
      σ.app (M ⊗ N) ≫ ν'.map (Functor.OplaxMonoidal.δ F' M N) ≫
        Functor.OplaxMonoidal.δ ν' (F'.obj M) (F'.obj N))
    (P Q : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) ν).app P).app Q) ≫
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
          ((ν.mapHomologicalComplex (.up ℤ)).obj P)).app
          ((ν.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app P ⊗ₘ
          (NatTrans.mapHomologicalComplex σ (.up ℤ)).app Q) =
      (NatTrans.mapHomologicalComplex σ (.up ℤ)).app (P ⊗ Q) ≫
        (ν'.mapHomologicalComplex (.up ℤ)).map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F').app P).app Q) ≫
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) ν').app
          ((F'.mapHomologicalComplex (.up ℤ)).obj P)).app
          ((F'.mapHomologicalComplex (.up ℤ)).obj Q) := by
  ext n : 1
  refine HomologicalComplex.mapBifunctor.hom_ext_of_map (G := ν ⋙ F) fun p q hpq ↦ ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  erw [σ.naturality_assoc]
  erw [Functor.comp_map, ← Functor.map_comp_assoc, map_ιMapBifunctor_mapHomologicalComplexδ,
    Functor.map_comp, Category.assoc, map_ιMapBifunctor_mapHomologicalComplexδ_assoc,
    ιMapBifunctor_tensorHom_f]
  erw [Functor.comp_map, ← Functor.map_comp_assoc, map_ιMapBifunctor_mapHomologicalComplexδ,
    Functor.map_comp, Category.assoc, map_ιMapBifunctor_mapHomologicalComplexδ]
  have h' := h (P.X p) (Q.X q) =≫ HomologicalComplex.ιMapBifunctor
    ((ν'.mapHomologicalComplex (.up ℤ)).obj ((F'.mapHomologicalComplex (.up ℤ)).obj P))
    ((ν'.mapHomologicalComplex (.up ℤ)).obj ((F'.mapHomologicalComplex (.up ℤ)).obj Q))
    (curriedTensor D') (.up ℤ) p q n hpq
  simp only [Category.assoc] at h'
  exact h'

end SquareOfSummands

/-- The scalar/site square for signed total tensors commutes before localization.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 07A4 and 0G7E;
latest blueprint lemma-change-coefficients-exceptional-inverse-image--3, Paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-cochain-tensor-square)

Proof:
1. In degree n, form the direct sum over p + q = n of the ordinary scalar/site tensor
maps. All four functors are additive left adjoints and preserve these direct sums.
The four total comparisons above are exactly this canonical construction, using
`CochainComplex.mapBifunctor` for the signed total tensor.
2. Naturality in each variable commutes with the two differentials separately.
Additivity commutes with the scalar (-1)^p in the second differential, and all maps
preserve the bidegree, so the Koszul signs on both paths are the same.
3. On each summand the ordinary sheaf tensor square gives equality: locally each route
sends b tensor (p tensor q) to (b tensor p) tensor (1 tensor q). The direct-sum universal
property proves the equality of components, hence of cochain maps.
-/
theorem normalized_stage_site_cochain_tensor_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((ProEtale.sheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).map
          (siteTensorCochain A X P Q) ≫
        proEtaleScalarTensorCochain φ X
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
            (.up ℤ)).obj Q) ≫
        (scalarSiteCochain φ X P ⊗ₘ scalarSiteCochain φ X Q) =
      scalarSiteCochain φ X (P ⊗ Q) ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapHomologicalComplex
          (.up ℤ)).map (etaleScalarTensorCochain φ X P Q) ≫
        siteTensorCochain B X
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P)
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj Q) := by
  exact mapHomologicalComplexδ_square _ _ _ _ _
    (normalized_stage_site_sheaf_tensor_square φ X) P Q

end WeilConjectures.FiniteFreeCoefficients.Sites
