/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorCochainData
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorRepresentativeData
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
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

def canonicalProjectionMate
    {E : Type u₁} {D : Type u₂} [Category.{v₁} E] [Category.{v₂} D]
    (S : E × E ⥤ E) (T : D × D ⥤ D)
    (F : D ⥤ E) (G : E ⥤ D) (adj : F ⊣ G)
    (μ : S ⋙ G ≅ (G.prod G) ⋙ T) :
    (𝟭 D).prod G ⋙ T ⋙ F ⟶ (F.prod (𝟭 E)) ⋙ S where
  app X := (adj.homEquiv _ _).symm
    (T.map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫ μ.inv.app (F.obj X.1, X.2))
  naturality := by
    intro X Y f
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ (F.map (T.map (Prod.mkHom f.1 (G.map f.2))) ≫ _) =
      adj.homEquiv _ _ (_ ≫ S.map (Prod.mkHom (F.map f.1) f.2))
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    dsimp only [Functor.prod_obj, Functor.comp_obj, Functor.id_obj]
    simp only [Equiv.apply_symm_apply]
    have hμ := μ.inv.naturality (Prod.mkHom (F.map f.1) f.2)
    change T.map (Prod.mkHom (G.map (F.map f.1)) (G.map f.2)) ≫
      μ.inv.app (F.obj Y.1, Y.2) =
      μ.inv.app (F.obj X.1, X.2) ≫ G.map (S.map (Prod.mkHom (F.map f.1) f.2)) at hμ
    rw [Category.assoc, ← hμ]
    simp only [← Category.assoc, ← T.map_comp]
    congr 2
    apply Prod.hom_ext
    · exact adj.unit.naturality f.1
    · simp

private theorem canonicalProjectionMate_homEquiv
    {E : Type u₁} {D : Type u₂} [Category.{v₁} E] [Category.{v₂} D]
    (S : E × E ⥤ E) (T : D × D ⥤ D)
    (F : D ⥤ E) (G : E ⥤ D) (adj : F ⊣ G)
    (μ : S ⋙ G ≅ (G.prod G) ⋙ T)
    (X : D × E) :
    adj.homEquiv _ _ ((canonicalProjectionMate S T F G adj μ).app X) =
      T.map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫
        μ.inv.app (F.obj X.1, X.2) := by
  exact Equiv.apply_symm_apply _ _

private theorem exact_unit_app
    {E D : Type u₁} [Category.{v₁} E] [Category.{v₁} D]
    [Abelian E] [Abelian D] [HasDerivedCategory.{u₂} E] [HasDerivedCategory.{u₂} D]
    {L : E ⥤ D} {R : D ⥤ E} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex E ℤ) :
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).unit.app
        (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app _ ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) := by
  unfold SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    Adjunction.mapExactDerivedCategory
  rw [Adjunction.localization_unit_app]
  rfl

private theorem exact_hom_fac
    {E D : Type u₁} [Category.{v₁} E] [Category.{v₁} D]
    [Abelian E] [Abelian D] [HasDerivedCategory.{u₂} E] [HasDerivedCategory.{u₂} D]
    {L : E ⥤ D} {R : D ⥤ E} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex E ℤ) (N : CochainComplex D ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj N)
        (L.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        R.mapDerivedCategoryFactors.inv.app N := by
  rw [Adjunction.homEquiv_unit, exact_unit_app, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg
    (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫ ·)
    (R.mapDerivedCategoryFactors.inv.naturality f).symm

private theorem cancel_comparison
    {E : Type u₁} {D : Type u₂} [Category.{v₁} E] [Category.{v₂} D]
    (G : E ⥤ D) {U V : E} {W X : D} (a : U ≅ V) (e : G.obj U ≅ W)
    (z : X ⟶ W) (d : X ⟶ G.obj V)
    (h : d ≫ G.map a.inv ≫ e.hom = z) :
    z ≫ e.inv ≫ G.map a.hom = d := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp,
    a.inv_hom_id, G.map_id, Category.comp_id]

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory CoefficientClosedStructure.tensor
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction canonicalProjectionMate

private theorem projection_preserves_flat
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (M : SemilinearSections.Mod.{c, v, max c v r} J' R')
    (hM : SheafOfModules.IsFlatOnSite (J := J') (R := R') M) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) (F.obj M) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let := SheafOfModules.monoidalCategory R'
  have hf := SheafOfModules.flat_to_cat R' M hM
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft M) := hf.1.1
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft M) := hf.1.2
  let e : MonoidalCategory.tensorLeft (F.obj M) ≅
      G ⋙ MonoidalCategory.tensorLeft M ⋙ F :=
    NatIso.ofComponents (fun N ↦ D.ordinary M N) (by
      intro N N' f
      have hn := D.ordinaryNaturality (𝟙 M) f
      dsimp only [ordinaryTensorHom] at hn
      simp only [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom] at hn
      exact hn)
  have he : exactFunctor _ _ (MonoidalCategory.tensorLeft (F.obj M)) :=
    ⟨preservesFiniteLimits_of_natIso e.symm, preservesFiniteColimits_of_natIso e.symm⟩
  exact (exactFunctor _ _).prop_of_iso
    ((BraidedCategory.tensorLeftIsoTensorRight (F.obj M)) ≪≫
      (SheafOfModules.siteSheafTensorRightIso R (F.obj M)).symm) he

private theorem projection_preserves_kflat
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (K : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R') K) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
      ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let := SheafOfModules.monoidalCategory R'
  let := SheafOfModules.symmetricCategory R'
  let := SheafOfModules.tensorPreadditive R'
  intro Z hZ i
  have hg : ((G.mapHomologicalComplex (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map G
  have ht := hK _ hg
  have ht' : ((totalTensor.{c, v, r} J' R').obj
      (K, (G.mapHomologicalComplex (.up ℤ)).obj Z)).Acyclic := by
    intro j
    exact (ht j).of_iso (CochainComplex.Monoidal.braiding _ _)
  have hm : ((F.mapHomologicalComplex (.up ℤ)).obj
      ((totalTensor.{c, v, r} J' R').obj
        (K, (G.mapHomologicalComplex (.up ℤ)).obj Z))).Acyclic := by
    intro j
    exact (ht' j).map F
  exact ((hm i).of_iso (D.chain K Z).symm).of_iso
    (CochainComplex.Monoidal.braiding _ _)

private theorem tensorSummand_map
    {K K' L L' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (p q k : ℤ) (hpq : p + q = k) :
    tensorSummand.{c, v, r} J R K L p q k hpq ≫
      ((totalTensor.{c, v, r} J R).map (Prod.mkHom f g)).f k =
    ordinaryTensorHom.{c, v, r} J R (f.f p) (g.f q) ≫
      tensorSummand.{c, v, r} J R K' L' p q k hpq := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  change HomologicalComplex.ιMapBifunctor K L (MonoidalCategory.curriedTensor _)
      (.up ℤ) p q k hpq ≫
      (HomologicalComplex.mapBifunctorMap f (𝟙 L) (MonoidalCategory.curriedTensor _)
        (.up ℤ) ≫ HomologicalComplex.mapBifunctorMap (𝟙 K') g
        (MonoidalCategory.curriedTensor _) (.up ℤ)).f k = _
  have hm : HomologicalComplex.mapBifunctorMap f (𝟙 L) (MonoidalCategory.curriedTensor _)
      (.up ℤ) ≫ HomologicalComplex.mapBifunctorMap (𝟙 K') g
      (MonoidalCategory.curriedTensor _) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (MonoidalCategory.curriedTensor _) (.up ℤ) := by
    simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  rw [hm, HomologicalComplex.ι_mapBifunctorMap]
  change (f.f p ▷ L.X q) ≫ (K'.X p ◁ g.f q) ≫ _ =
    (f.f p ⊗ₘ g.f q) ≫ _
  erw [MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem projection_chain_adjunct
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (M : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (ho : M.ordinary = D.pullTensor)
    (K : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (L : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _ (D.chain K L).inv =
      (totalTensor.{c, v, r} J' R').map
        (Prod.mkHom ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) (𝟙 _)) ≫
      M.chain ((F.mapHomologicalComplex (.up ℤ)).obj K) L := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let := SheafOfModules.monoidalCategory R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R'
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  change tensorSummand.{c, v, r} J' R' K
      ((G.mapHomologicalComplex (.up ℤ)).obj L) p q k hpq ≫
      adj.unit.app _ ≫ G.map ((D.chain K L).inv.f k) = _
  have hn := adj.unit.naturality
    (tensorSummand.{c, v, r} J' R' K
      ((G.mapHomologicalComplex (.up ℤ)).obj L) p q k hpq)
  change _ ≫ adj.unit.app _ = adj.unit.app _ ≫ G.map (F.map _) at hn
  erw [reassoc_of% hn]
  erw [reassoc_of% (tensorSummand_map.{c, v, r} J' R'
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) (𝟙 _) p q k hpq), M.summand]
  have hs := D.summand K L p q k hpq
  have hi : F.map (tensorSummand.{c, v, r} J' R' K
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q k hpq) ≫
        (D.chain K L).inv.f k =
      (D.ordinary (K.X p) (L.X q)).inv ≫
        tensorSummand.{c, v, r} J R ((F.mapHomologicalComplex (.up ℤ)).obj K)
          L p q k hpq := by
    apply (cancel_epi (D.ordinary (K.X p) (L.X q)).hom).1
    erw [← Category.assoc, ← hs, Category.assoc]
    have hcomp : (D.chain K L).hom.f k ≫ (D.chain K L).inv.f k = 𝟙 _ :=
      congrArg (fun f ↦ f.f k) (D.chain K L).hom_inv_id
    erw [hcomp, Category.comp_id, Iso.hom_inv_id_assoc]
  erw [← G.map_comp, hi, G.map_comp, ← Category.assoc]
  erw [← Adjunction.homEquiv_unit, D.ordinaryInverse, ho]
  rfl

attribute [local irreducible] coefficientTotalTensor

/-- The canonical adjunction-transpose projection identity on resolving pairs.
The one-flat comparisons agree with the simultaneous K-flat models; both input
complexes are flat-term K-flat representatives. Source: Stacks 0GL1, 07A4 and
06YS--06YT (blueprint: lem-sf-open-tensor-projection-mate-canonical).

Proof: first show that F carries flat modules to flat modules. The ordinary
projection isomorphisms, their naturality, and symmetry identify tensoring with
F(M) with the composite of exact G, tensoring with the flat M, and exact F.
For a K-flat complex C, test F(C) against any acyclic complex P: exact G carries
P to an acyclic complex, K-flatness of C makes its tensor with G(P) acyclic,
and exact F preserves acyclicity. The chain projection and tensor symmetry
identify this with the required acyclicity test for F(C). Thus F(C) is K-flat
with flat terms. D.pullKFlat and D.pullFlat give the same properties for G(P).
On each signed total summand, D.ordinaryInverse, hordinary, D.summand and
restrictionModel.summand identify the adjunct of D.chain.inv with the tensor
of the cochain adjunction unit and identity followed by restrictionModel.chain.
Coproduct extensionality gives the cochain equality. Localize it using the
unit equation for exactDerivedAdjunction and the exact-functor factorization
isomorphisms. Apply restrictionModel.derived to F(C), P; naturality of the
simultaneous comparison handles the cochain unit. Finally ambientBoth and
openBoth replace the supplied comparisons by those simultaneous comparisons.
The defining hom-equivalence formula for canonicalProjectionMate, followed by
injectivity of that equivalence and cancellation of the chain isomorphism,
gives the displayed equation. -/
theorem openTensorProjection_mate_canonical
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (ambientBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1}
      J R A T ambientModel)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (openBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1}
      J' R' A' T' openModel)
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
        (canonicalProjectionMate A.tensor A'.tensor F.mapDerivedCategory
          G.mapDerivedCategory
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj)
          restriction).app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _)) := by
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  let GP := (G.mapHomologicalComplex (.up ℤ)).obj P
  let GFC := (G.mapHomologicalComplex (.up ℤ)).obj FC
  have hFC := projection_preserves_kflat J R J' R' F G adj H sectionPull D C hC
  have flatFC : flatTerms.{c, v, r} J R FC := fun i ↦
    projection_preserves_flat J R J' R' F G adj H sectionPull D (C.X i) (flatC i)
  have hGP := restrictionModel.kflat P hP flatP
  have hGFC := restrictionModel.kflat FC hFC flatFC
  let η := (adj.mapHomologicalComplex (.up ℤ)).unit.app C
  let U := (totalTensor.{c, v, r} J' R').obj (C, GP)
  let V := (totalTensor.{c, v, r} J R).obj (FC, P)
  let a := tensorModelIso.{c, v, r} J R A T FC P hFC hP
  let b := tensorModelIso.{c, v, r} J' R' A' T' C GP hC hGP
  let d := tensorModelIso.{c, v, r} J' R' A' T' GFC GP hGFC hGP
  let w := DerivedCategory.Q.map
    ((totalTensor.{c, v, r} J' R').map (Prod.mkHom η (𝟙 GP)))
  let z := DerivedCategory.Q.map (restrictionModel.chain FC P)
  let ad := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj
  let α := canonicalProjectionMate A.tensor A'.tensor F.mapDerivedCategory
    G.mapDerivedCategory ad restriction
  have hc : ad.homEquiv _ _
      (F.mapDerivedCategoryFactors.hom.app U ≫ DerivedCategory.Q.map (D.chain C P).inv) =
      w ≫ z ≫ G.mapDerivedCategoryFactors.inv.app V := by
    rw [exact_hom_fac]
    rw [projection_chain_adjunct J R A T J' R' A' T' F G adj H sectionPull
      D restriction restrictionModel hordinary C P, Functor.map_comp]
    exact Category.assoc _ _ _
  have hd : z ≫ G.mapDerivedCategoryFactors.inv.app V ≫
      G.mapDerivedCategory.map a.hom =
      d.hom ≫ A'.tensor.map (Prod.mkHom
        (G.mapDerivedCategoryFactors.inv.app FC) (G.mapDerivedCategoryFactors.inv.app P)) ≫
        restriction.inv.app (DerivedCategory.Q.obj FC, DerivedCategory.Q.obj P) := by
    apply cancel_comparison G.mapDerivedCategory a (G.mapDerivedCategoryFactors.app V) z
    dsimp only [Iso.app_hom]
    have ht := restrictionModel.derived FC P hFC hP flatFC flatP
    simp only [Category.assoc] at ⊢ ht
    exact ht
  have hn : w ≫ d.hom = b.hom ≫ A'.tensor.map
      (Prod.mkHom (DerivedCategory.Q.map η) (𝟙 (DerivedCategory.Q.obj GP))) := by
    let ρ : ObjectProperty
        (CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R')
    let f : (⟨C, hC⟩ : ρ.FullSubcategory) ⟶ ⟨GFC, hGFC⟩ := ObjectProperty.homMk η
    let g : (⟨GP, hGP⟩ : ρ.FullSubcategory) ⟶ ⟨GP, hGP⟩ := 𝟙 _
    have ht := T'.comparison.hom.naturality (Prod.mkHom f g)
    change w ≫ d.hom = b.hom ≫ A'.tensor.map
      (Prod.mkHom (DerivedCategory.Q.map η) (DerivedCategory.Q.map (𝟙 GP))) at ht
    simpa only [CategoryTheory.Functor.map_id] using ht
  have hr := restriction.inv.naturality
    (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 (DerivedCategory.Q.obj P)))
  change A'.tensor.map (Prod.mkHom
        (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app C))
        (G.mapDerivedCategory.map (𝟙 _))) ≫
      restriction.inv.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj C),
        DerivedCategory.Q.obj P) =
    restriction.inv.app (DerivedCategory.Q.obj FC, DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (A.tensor.map (Prod.mkHom
        (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _))) at hr
  simp only [CategoryTheory.Functor.map_id] at hr
  have hu : ad.unit.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map η ≫ G.mapDerivedCategoryFactors.inv.app FC ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app C) :=
    exact_unit_app adj C
  let f := b.hom ≫ A'.tensor.map
    (Prod.mkHom (𝟙 (DerivedCategory.Q.obj C)) (G.mapDerivedCategoryFactors.inv.app P))
  let out := a.hom ≫ A.tensor.map
    (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 (DerivedCategory.Q.obj P)))
  have hα : ad.homEquiv _ _
      (α.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P)) =
      A'.tensor.map (Prod.mkHom (ad.unit.app (DerivedCategory.Q.obj C)) (𝟙 _)) ≫
        restriction.inv.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj C),
          DerivedCategory.Q.obj P) := by
    exact canonicalProjectionMate_homEquiv A.tensor A'.tensor
      F.mapDerivedCategory G.mapDerivedCategory ad restriction _
  have hm : F.mapDerivedCategory.map f ≫
      α.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
      (F.mapDerivedCategoryFactors.hom.app U ≫
        DerivedCategory.Q.map (D.chain C P).inv) ≫ out := by
    apply (ad.homEquiv _ _).injective
    rw [ad.homEquiv_naturality_left, ad.homEquiv_naturality_right, hc]
    erw [hα]
    dsimp only [out]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hd, reassoc_of% hn, ← hr]
    dsimp only [f]
    simp only [Category.assoc, ← A'.tensor.map_comp_assoc]
    congr 2
    apply congrArg A'.tensor.map
    apply Prod.hom_ext
    · simpa only [prod_comp, Prod.mkHom, Category.id_comp] using hu
    · dsimp only [prod_comp, Prod.mkHom]
      erw [Category.id_comp]
  have ha : ambientModel FC P (Or.inr hP) = a :=
    ambientBoth FC P hFC hP
  have hb : openModel C GP (Or.inr hGP) = b := openBoth C GP hC hGP
  rw [ha, hb]
  have ht := congrArg (fun q ↦ DerivedCategory.Q.map (D.chain C P).hom ≫
    F.mapDerivedCategoryFactors.inv.app U ≫ q) hm
  dsimp only [f, out] at ht
  simp only [Functor.map_comp, Category.assoc] at ht
  simpa only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp] using ht

end WeilConjectures.CoefSupportOpenTensor
