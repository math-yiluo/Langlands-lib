/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorCochainData
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorRepresentativeData
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorProjectionMateCanonical

/-! # The projection mate on resolving pairs

Source: Stacks 0GL1, 07A4, 06YS and 06YT
(blueprint: lem-sf-open-tensor-projection-mate-resolving).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
  (A : SemilinearSections.Closed.{c, v, r} J R) (T : SemilinearSections.Models.{c, v, r} J R A)

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
  (A' : SemilinearSections.Closed.{c, v, r} J' R')
  (T' : SemilinearSections.Models.{c, v, r} J' R' A')
  (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R)
  (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    SemilinearSections.Mod.{c, v, max c v r} J' R')
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G)
  (H : C ⥤ C')
  (sectionPull : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ),
    N.val.obj V → (G.obj N).val.obj (H.op.obj V))

/-- The unit-defined projection mate has the expected chain formula on pairs of
flat-term K-flat complexes. No derived projection isomorphism or formula on
arbitrary complexes is asserted here.
Source: Stacks 0GL1, proof of lemma-j-shriek-and-tensor; 07A4 and 06YS--06YT
(blueprint: lem-sf-open-tensor-projection-mate-resolving).

Proof: the ordinary projection and exactness of F and G show that F preserves
flat modules and K-flat complexes. For flatness conjugate tensor with F(M) to
F composed with tensor with M and G, using the ordinary projection and symmetry.
For K-flatness test against an acyclic complex P: G(P) is acyclic, the tensor
with the original K-flat complex is acyclic, and F preserves that acyclicity;
the chain projection and tensor symmetry identify the required test.
Consequently restrictionModel.derived applies to F(C) and P. On each signed total
summand, the adjunct of D.chain.inv is the unit tensor identity followed by
restrictionModel.chain: this follows from D.ordinaryInverse, hordinary and the
two summand formulas. Maps out of the total coproduct are determined on these
summands, so these are equal chain maps. The chain adjunction localizes to the
specified exactDerivedAdjunction. Insert its standard exact-functor factorization
isomorphisms and use ambientBoth and openBoth to replace the one-flat comparisons
by the simultaneous comparisons in restrictionModel.derived. Finally halpha and
injectivity of the adjunction bijection identify the localized chain map with
alpha; cancellation of the chain projection gives the displayed square. -/
theorem openTensorProjection_mate_resolving
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (ambientBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1} J R A T ambientModel)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (openBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1} J' R' A' T' openModel)
    (alpha : (𝟭 _).prod G.mapDerivedCategory ⋙ A'.tensor ⋙ F.mapDerivedCategory ⟶
      (F.mapDerivedCategory.prod (𝟭 _)) ⋙ A.tensor)
    (halpha : ∀ M N,
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).homEquiv _ _
          (alpha.app (M, N)) =
        A'.tensor.map (Prod.mkHom
            ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).unit.app M)
            (𝟙 (G.mapDerivedCategory.obj N))) ≫
          restriction.inv.app (F.mapDerivedCategory.obj M, N))
    (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R') C)
    (flatC : flatTerms.{c, v, r} J' R' C)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P) :
      DerivedCategory.Q.map (D.chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P))) ≫
        alpha.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _)) := by
  let canonical := canonicalProjectionMate A.tensor A'.tensor F.mapDerivedCategory
    G.mapDerivedCategory
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj) restriction
  have hcanonical (M N) :
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).homEquiv _ _
          (canonical.app (M, N)) =
        A'.tensor.map (Prod.mkHom
            ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).unit.app M)
            (𝟙 (G.mapDerivedCategory.obj N))) ≫
          restriction.inv.app (F.mapDerivedCategory.obj M, N) := by
    exact Equiv.apply_symm_apply _ _
  have heq (M N) : alpha.app (M, N) = canonical.app (M, N) := by
    apply (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).homEquiv
      _ _ |>.injective
    rw [halpha, hcanonical]
  simpa only [heq] using
    (openTensorProjection_mate_canonical.{c, v, r} J R A T J' R' A' T' F G adj H
      sectionPull D restriction restrictionModel hordinary ambientModel ambientBoth
      openModel openBoth C P hC flatC hP flatP)

end WeilConjectures.CoefSupportOpenTensor
