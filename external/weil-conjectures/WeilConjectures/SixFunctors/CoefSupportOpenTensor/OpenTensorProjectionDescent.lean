/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorCochainData
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorRepresentativeData
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorProjectionMateResolving
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Descent of an ordinary open tensor projection

Source: Stacks 0GL1, 07A4, 06YS and 06YT
(blueprint: lem-sf-open-tensor-projection-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r u₁ u₂ v₁ v₂
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

private def projectionMate
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

private theorem isIso_app_of_iso
    {E D : Type*} [Category E] [Category D] {U V : E ⥤ D}
    (alpha : U ⟶ V) {X Y : E} (e : X ≅ Y) [IsIso (alpha.app X)] :
    IsIso (alpha.app Y) := by
  exact IsIso.of_isIso_fac_left (alpha.naturality e.hom)

private theorem extend_square
    {E : Type*} [Category E] {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : E}
    (a : X₀ ⟶ X₁) (b : Y₀ ⟶ Y₁) (c : Z₀ ⟶ Z₁)
    (l₀ : X₀ ≅ Z₀) (l₁ : X₁ ≅ Z₁) (r₀ : X₀ ≅ Y₀) (r₁ : X₁ ≅ Y₁)
    (alpha₀ : Y₀ ⟶ Z₀) (alpha₁ : Y₁ ⟶ Z₁) [IsIso c]
    (hl : a ≫ l₁.hom = l₀.hom ≫ c) (hr : a ≫ r₁.hom = r₀.hom ≫ b)
    (ha : b ≫ alpha₁ = alpha₀ ≫ c) (h₀ : r₀.hom ≫ alpha₀ = l₀.hom) :
    r₁.hom ≫ alpha₁ = l₁.hom := by
  have : IsIso a := IsIso.of_isIso_fac_right hl
  apply (cancel_epi a).1
  rw [← Category.assoc, hr, Category.assoc, ha, ← Category.assoc, h₀, hl]

private theorem resolving_exists
    (K : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :
    ∃ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
      (s : P ⟶ K),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∧
      flatTerms.{c, v, r} J R P ∧ QuasiIso s := by
  obtain ⟨P, s, hp, hf, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
  refine ⟨P, s, hp, fun n ↦ ?_, hs⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)

section Comparisons

variable
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')

private def leftComparison
    (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    DerivedCategory.Q.obj ((totalTensor.{c, v, r} J R).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj C, P)) ≅
    A.tensor.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj C),
      DerivedCategory.Q.obj P) :=
  ambientModel _ P (Or.inr hP) ≪≫
    A.tensor.mapIso (Iso.prod (F.mapDerivedCategoryFactors.symm.app C) (Iso.refl _))

private def rightComparison
    (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hGP : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R')
      ((G.mapHomologicalComplex (.up ℤ)).obj P)) :
    DerivedCategory.Q.obj ((totalTensor.{c, v, r} J R).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj C, P)) ≅
    F.mapDerivedCategory.obj (A'.tensor.obj
      (DerivedCategory.Q.obj C, G.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) :=
  DerivedCategory.Q.mapIso (D.chain C P) ≪≫
    F.mapDerivedCategoryFactors.symm.app _ ≪≫
    F.mapDerivedCategory.mapIso (openModel C _ (Or.inr hGP)) ≪≫
    F.mapDerivedCategory.mapIso
      (A'.tensor.mapIso (Iso.prod (Iso.refl _) (G.mapDerivedCategoryFactors.symm.app P)))

private theorem leftComparison_naturality
    (hn : RingedDerivedTensorNaturality.{c, v, r, (max c v r) + 1} J R A ambientModel)
    {C C₁ : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ}
    (f : C ⟶ C₁)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    DerivedCategory.Q.map ((totalTensor.{c, v, r} J R).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f) (𝟙 P))) ≫
      (leftComparison.{c, v, r} J R A J' R' F ambientModel C₁ P hP).hom =
    (leftComparison.{c, v, r} J R A J' R' F ambientModel C P hP).hom ≫
      A.tensor.map (Prod.mkHom (F.mapDerivedCategory.map (DerivedCategory.Q.map f)) (𝟙 _)) := by
  dsimp only [leftComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
    Iso.symm_hom, Iso.app, Iso.symm, Iso.refl_hom]
  rw [← Category.assoc, hn _ _ _ _ (Or.inr hP) (Or.inr hP)
    ((F.mapHomologicalComplex (.up ℤ)).map f) (𝟙 P), Category.assoc]
  simp only [Category.assoc]
  congr 1
  rw [← A.tensor.map_comp, ← A.tensor.map_comp]
  apply congrArg A.tensor.map
  apply Prod.hom_ext
  · exact F.mapDerivedCategoryFactors.inv.naturality f
  · simp

private theorem rightComparison_naturality
    (hn : RingedDerivedTensorNaturality.{c, v, r, (max c v r) + 1} J' R' A' openModel)
    {C C₁ : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ}
    (f : C ⟶ C₁)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hGP : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R')
      ((G.mapHomologicalComplex (.up ℤ)).obj P)) :
    DerivedCategory.Q.map ((totalTensor.{c, v, r} J R).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f) (𝟙 P))) ≫
      (rightComparison.{c, v, r} J R J' R' A' F G adj H sectionPull D openModel C₁ P hGP).hom =
    (rightComparison.{c, v, r} J R J' R' A' F G adj H sectionPull D openModel C P hGP).hom ≫
      F.mapDerivedCategory.map
        (A'.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (𝟙 _))) := by
  dsimp only [rightComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
    Iso.symm_hom, Iso.app, Iso.symm, Iso.refl_hom]
  have hc := congrArg DerivedCategory.Q.map (D.chainNaturality f (𝟙 P))
  simp only [Functor.map_comp] at hc
  rw [← Category.assoc, hc, Category.assoc]
  simp only [Category.assoc]
  congr 1
  have he := F.mapDerivedCategoryFactors.inv.naturality
    ((totalTensor.{c, v, r} J' R').map
      (Prod.mkHom f ((G.mapHomologicalComplex (.up ℤ)).map (𝟙 P))))
  dsimp only [Functor.comp_map] at he
  rw [← Category.assoc, he, Category.assoc]
  congr 1
  simp only [← F.mapDerivedCategory.map_comp]
  apply congrArg F.mapDerivedCategory.map
  rw [← Category.assoc, hn _ _ _ _ (Or.inr hGP) (Or.inr hGP) f
    ((G.mapHomologicalComplex (.up ℤ)).map (𝟙 P)), Category.assoc]
  congr 1
  rw [← A'.tensor.map_comp, ← A'.tensor.map_comp]
  apply congrArg A'.tensor.map
  apply Prod.hom_ext <;> simp

end Comparisons

/-- Descend the ordinary projection comparison, with its specified inverse transpose,
through the supplied tensor models. This constructs only the derived projection and
its representative equation; the restriction comparison and all ordinary data are inputs.
Source: Stacks 0GL1, proof of lemma-j-shriek-and-tensor; 07A4 and 06YS--06YT
(blueprint: lem-sf-open-tensor-projection-descent).

Proof: first observe that F preserves flat terms and K-flat complexes. For a flat
module M, tensor(F M,-) is identified by D.ordinary with the composite of exact
G, tensor(M,-), and exact F, hence is exact. For a K-flat C and an acyclic test
P, exact G makes G P acyclic; D.chain identifies tensor(F C,P) with
F tensor(C,G P), which is acyclic by K-flatness and exactness of F. Tensor
symmetry gives the acyclicity test in its prescribed order.
Resolve both inputs by flat-term K-flat complexes. For a K-flat P, the source
Tot(F C tensor P) computes the ambient tensor even though F C need not be K-flat.
The target F Tot(C tensor G P) computes the open tensor since G P is K-flat.
Compose the inverse ambient comparison, Q of D.chain, the exact F factorization,
and F of the open comparison. Chain naturality and the naturality of both one-flat
comparisons make this a natural isomorphism on resolving pairs. Two-variable
localization on flat-term K-flat complexes descends it to gamma. Resolve only C
and use the two one-flat naturality squares and D.chainNaturality to prove the
same equation for arbitrary C and flat-term K-flat P; cancel the localized
resolution maps. To identify the inverse transpose, work first with both inputs
flat-term K-flat. D.ordinaryInverse and the summand formulas for D.chain and the
restrictionModel identify its chain adjoint with unit tensor identity followed
by the inverse restriction comparison. The exact derived adjunction is the
localization of the chain adjunction, so the same equation holds after Q, with
the exact-functor factorization isomorphisms inserted. The supplied both-model
identities identify the simultaneous comparisons used here. Naturality and
localization then give the inverse equation on all derived inputs. No inference
from equality after finite evaluations is used. -/
theorem openTensorProjection_descent
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (ambientBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1} J R A T ambientModel)
    (ambientNaturality : RingedDerivedTensorNaturality.{c, v, r, (max c v r) + 1}
      J R A ambientModel)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (openBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1} J' R' A' T' openModel)
    (openNaturality : RingedDerivedTensorNaturality.{c, v, r, (max c v r) + 1}
      J' R' A' openModel) :
    ∃ gamma : (F.mapDerivedCategory.prod (𝟭 _)) ⋙ A.tensor ≅
    (𝟭 _).prod G.mapDerivedCategory ⋙ A'.tensor ⋙ F.mapDerivedCategory,
      (∀ M N,
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).homEquiv _ _
        (gamma.inv.app (M, N)) =
      A'.tensor.map (Prod.mkHom
          ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).unit.app M)
          (𝟙 (G.mapDerivedCategory.obj N))) ≫
        restriction.inv.app (F.mapDerivedCategory.obj M, N)) ∧
      (∀ (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P),
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _)) ≫
        gamma.hom.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (D.chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P)))) := by
  let alpha := projectionMate A.tensor A'.tensor F.mapDerivedCategory G.mapDerivedCategory
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj) restriction
  have halpha (M N) :
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).homEquiv _ _
          (alpha.app (M, N)) =
        A'.tensor.map (Prod.mkHom
            ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).unit.app M)
            (𝟙 (G.mapDerivedCategory.obj N))) ≫
          restriction.inv.app (F.mapDerivedCategory.obj M, N) := by
    exact Equiv.apply_symm_apply _ _
  have hres := openTensorProjection_mate_resolving.{c, v, r} J R A T J' R' A' T' F G adj H
    sectionPull D restriction restrictionModel hordinary ambientModel ambientBoth
    openModel openBoth alpha halpha
  have hflat
      (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
      (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R') C)
      (flatC : flatTerms.{c, v, r} J' R' C)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (flatP : flatTerms.{c, v, r} J R P) :
      IsIso (alpha.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P)) := by
    have h := hres C P hC flatC hP flatP
    have h' : (rightComparison.{c, v, r} J R J' R' A' F G adj H sectionPull D openModel C P
        (restrictionModel.kflat P hP flatP)).hom ≫
        alpha.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
        (leftComparison.{c, v, r} J R A J' R' F ambientModel C P hP).hom := by
      simpa only [rightComparison, leftComparison, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, Iso.app_hom, Iso.symm_hom, Iso.refl_hom, Category.assoc] using h
    exact IsIso.of_isIso_fac_left h'
  have hcomponents (X) : IsIso (alpha.app X) := by
    obtain ⟨C, f, hC, flatC, hf⟩ :=
      resolving_exists.{c, v, r} J' R' (DerivedCategory.Q.objPreimage X.1)
    obtain ⟨P, g, hP, flatP, hg⟩ :=
      resolving_exists.{c, v, r} J R (DerivedCategory.Q.objPreimage X.2)
    let := hf
    let := hg
    let eC := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X.1
    let eP := asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso X.2
    have := hflat C P hC flatC hP flatP
    exact isIso_app_of_iso alpha (Iso.prod eC eP)
  let : ∀ X, IsIso (alpha.app X) := hcomponents
  let : IsIso alpha := NatIso.isIso_of_isIso_app alpha
  refine ⟨(asIso alpha).symm, halpha, ?_⟩
  intro C P hP flatP
  obtain ⟨C₀, f, hC₀, flatC₀, hf⟩ := resolving_exists.{c, v, r} J' R' C
  let := hf
  let hGP := restrictionModel.kflat P hP flatP
  have h₀ := hres C₀ P hC₀ flatC₀ hP flatP
  have h₀' :
      (rightComparison.{c, v, r} J R J' R' A' F G adj H sectionPull D openModel C₀ P hGP).hom ≫
        alpha.app (DerivedCategory.Q.obj C₀, DerivedCategory.Q.obj P) =
      (leftComparison.{c, v, r} J R A J' R' F ambientModel C₀ P hP).hom := by
    simpa only [rightComparison, leftComparison, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.app_hom, Iso.symm_hom, Iso.refl_hom, Category.assoc] using h₀
  have hn := alpha.naturality (Prod.mkHom (DerivedCategory.Q.map f)
    (𝟙 (DerivedCategory.Q.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hn
  erw [G.mapDerivedCategory.map_id (DerivedCategory.Q.obj P)] at hn
  have : IsIso (Prod.mkHom (F.mapDerivedCategory.map (DerivedCategory.Q.map f))
      (𝟙 (DerivedCategory.Q.obj P))) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have h := extend_square _ _ _ _ _ _ _ _ _
    (leftComparison_naturality.{c, v, r} J R A J' R' F ambientModel ambientNaturality f P hP)
    (rightComparison_naturality.{c, v, r} J R J' R' A' F G adj H sectionPull D openModel
      openNaturality f P hGP) hn h₀'
  change (rightComparison.{c, v, r} J R J' R' A' F G adj H sectionPull D openModel C P hGP).hom ≫
      alpha.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
    (leftComparison.{c, v, r} J R A J' R' F ambientModel C P hP).hom at h
  have hfinal : (leftComparison.{c, v, r} J R A J' R' F ambientModel C P hP).hom ≫
      (asIso alpha).inv.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
      (rightComparison.{c, v, r} J R J' R' A' F G adj H sectionPull D openModel C P hGP).hom := by
    apply (cancel_mono (alpha.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P))).1
    rw [Category.assoc, show (asIso alpha).inv.app _ ≫ alpha.app _ = 𝟙 _ from
      NatTrans.congr_app (asIso alpha).inv_hom_id _]
    erw [Category.comp_id]
    exact h.symm
  simpa only [rightComparison, leftComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.app_hom, Iso.symm_hom, Iso.refl_hom, Category.assoc] using hfinal

end WeilConjectures.CoefSupportOpenTensor
