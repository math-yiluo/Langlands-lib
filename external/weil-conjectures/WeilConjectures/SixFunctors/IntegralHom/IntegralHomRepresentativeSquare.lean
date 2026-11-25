/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorComponents
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomReducedEvaluation
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal

/-! # Normalization of Hom reduction on fixed chain representatives

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open CategoryTheory.MonoidalCategory
open scoped ZeroObject
namespace WeilConjectures.IntegralHom

section HomModel
variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem homModelMap_isIso
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) (hI : I.IsKInjective) :
    IsIso (homModelMap.{t, u} Y R P I) := by
  have : I.IsKInjective := hI
  have : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  let eta := (CochainComplex.toKInjectiveResolution.{max u (t + 1)} _).app I
  have : QuasiIso eta :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
  have : ((CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} _).obj
      I).IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ I
  have hI' : ((𝟭 (CochainComplex (Modules.{t, u} Y R) ℤ)).obj I).IsKInjective := hI
  have hh := quasiIso_homComplex_mapOfUniverses.{t + 1, t, u} eta (𝟙 P)
  rw [op_id, (homComplexFunctor (R := R)).map_id, NatTrans.id_app,
    Category.id_comp] at hh
  have : IsIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := R)).obj (op P)).map eta)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hh
  unfold homModelMap
  infer_instance

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem twoTerm_tensor_isKInjective
    (I Q : CochainComplex (Modules.{t, u} Y R) ℤ) (hI : I.IsKInjective)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from
      SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from
      SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat RingCat)).obj R))) :
    (((totalTensor.{t, u} Y R).obj I).obj Q).IsKInjective := by
  classical
  let M := Modules.{t, u} Y R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients
    (R := R)).some
  have (X : M) : (CategoryTheory.MonoidalCategory.tensorLeft X).Additive :=
    SheafOfModules.tensorLeft_additive_independent R X
  have (X : M) : (CategoryTheory.MonoidalCategory.tensorRight X).Additive :=
    Functor.additive_of_iso (F := CategoryTheory.MonoidalCategory.tensorLeft X)
      (NatIso.ofComponents (fun Z ↦ CategoryTheory.BraidedCategory.braiding X Z)
        (fun f ↦ CategoryTheory.BraidedCategory.braiding_naturality_right X f))
  let : MonoidalPreadditive M :=
    { whiskerLeft_zero := fun {X Y Z} ↦
        (CategoryTheory.MonoidalCategory.tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦
        (CategoryTheory.MonoidalCategory.tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦
        (CategoryTheory.MonoidalCategory.tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦
        (CategoryTheory.MonoidalCategory.tensorRight X).map_add (f := f) (g := g) }
  have (X : M) : PreservesColimitsOfSize.{0, 0}
      (CategoryTheory.MonoidalCategory.tensorLeft X) :=
    preservesColimitsOfSize_shrink _
  have (X : M) : PreservesColimitsOfSize.{0, 0}
      (CategoryTheory.MonoidalCategory.tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  have : HasExactColimitsOfShape ℤ M :=
    HasExactColimitsOfShape.domain_of_functor ℤ (SheafOfModules.toSheaf _)
  have hdual (n : ℤ) : IsDualizable (Q.X n) := by
    by_cases hn : n = -1
    · subst n
      exact isDualizable_unit.of_iso eNeg.symm
    by_cases hn' : n = 0
    · subst n
      exact isDualizable_unit.of_iso eZero.symm
    exact CategoryTheory.IsZero.isDualizable (hzero n hn hn')
  let : ∀ n, HasRightDual (Q.X n) := fun n ↦ (hdual n).some
  have : Q.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff _ _).2 (by
    intro n hn
    exact hzero n (by omega) (by omega))
  have : Q.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff _ _).2 (by
    intro n hn
    exact hzero n (by omega) (by omega))
  let D := Q.rightDual
  have hd (n : ℤ) : ObjectProperty.flat (D.X n) := by
    have hh : IsDualizable (D.X n) :=
      ⟨{ rightDual := Q.X (-n)
         exact := BraidedCategory.exactPairing_swap (Q.X (-n)) (Q.X (-n))ᘁ }⟩
    exact hh.flat
  have : D.IsStrictlyLE 1 := by
    simpa using (inferInstance : Q.rightDual.IsStrictlyLE (-(-1 : ℤ)))
  have hk := CochainComplex.kFlat_of_isStrictlyLE_of_flat D 1 hd
  let π := HomotopyCategory.quotient M (.up ℤ)
  let := CochainComplex.exactPairingRightDual Q (-1) 0
  let := BraidedCategory.exactPairing_swap Q D
  let : ExactPairing (π.obj D) (π.obj Q) := ExactPairing.map π D Q
  let adj := tensorRightAdjunction (π.obj D) (π.obj Q)
  have := adj.isLeftAdjoint
  have : I.IsKInjective := hI
  refine ⟨fun {A} f hA ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  change π.map f = π.map 0
  rw [Functor.map_zero]
  apply (adj.homEquiv (π.obj A) (π.obj I)).symm.injective
  have hAD : (A ⊗ D).Acyclic := by
    have hz : QuasiIso (0 : (0 : CochainComplex M ℤ) ⟶ A) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hA i)
    let T := CategoryTheory.MonoidalCategory.tensorRight D
    have hf : QuasiIso (T.map (0 : (0 : CochainComplex M ℤ) ⟶ A)) := hk.2 _ hz
    have ht : (T.obj (0 : CochainComplex M ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (T.map (0 : (0 : CochainComplex M ℤ) ⟶ A)) i).1 (ht i)
  have hg : (adj.homEquiv (π.obj A) (π.obj I)).symm (π.map f) = 0 := by
    apply CochainComplex.IsKInjective.rightOrthogonal I
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hAD
  rw [hg]
  symm
  erw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]

end HomModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

private noncomputable def scalarHomBijection
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (adj : integralDerivedReduction l E Y D hl n ⊣ scalarReductionDerivedRestriction l E Y n)
    (A K : completedIntegralDerivedCategory l E Y D hl)
    (N : Derived.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)) :
    (A ⟶ (scalarReductionDerivedRestriction l E Y n).obj
      ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
        (op ((integralDerivedReduction l E Y D hl n).obj K), N))) ≃
      (A ⟶ (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, (scalarReductionDerivedRestriction l E Y n).obj N)) :=
  (adj.homEquiv A _).symm.trans
    (((m.target.adjunction ((integralDerivedReduction l E Y D hl n).obj K)).homEquiv
      ((integralDerivedReduction l E Y D hl n).obj A) N).symm.trans
      ((Iso.homCongr (m.mu.app (K, A)).symm (Iso.refl N)).trans
        ((adj.homEquiv _ N).trans ((a.adjunction K).homEquiv A _))))

private theorem scalarHomBijection_precomp
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (adj : integralDerivedReduction l E Y D hl n ⊣ scalarReductionDerivedRestriction l E Y n)
    {A B : completedIntegralDerivedCategory l E Y D hl} (g : A ⟶ B)
    (K : completedIntegralDerivedCategory l E Y D hl)
    (N : Derived.{t, u} Y (integralCoefficientCommRingSheaf l E Y n))
    (f : B ⟶ (scalarReductionDerivedRestriction l E Y n).obj
      ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
        (op ((integralDerivedReduction l E Y D hl n).obj K), N))) :
    scalarHomBijection l E Y D hl a n m adj A K N (g ≫ f) =
      g ≫ scalarHomBijection l E Y D hl a n m adj B K N f := by
  dsimp only [scalarHomBijection, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_left_symm]
  erw [(m.target.adjunction _).homEquiv_naturality_left_symm]
  dsimp only [Iso.homCongr, Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  simp only [Category.comp_id]
  have hmu := m.mu.hom.naturality (Prod.mkHom (𝟙 K) g)
  dsimp only [Functor.comp_map, Functor.prod_map] at hmu
  erw [(integralDerivedReduction l E Y D hl n).map_id K] at hmu
  change (integralDerivedReduction l E Y D hl n).map
      (a.tensor.map (Prod.mkHom (𝟙 K) g)) ≫ (m.mu.app (K, B)).hom =
    (m.mu.app (K, A)).hom ≫ m.target.tensor.map
      (Prod.mkHom (𝟙 ((integralDerivedReduction l E Y D hl n).obj K))
        ((integralDerivedReduction l E Y D hl n).map g)) at hmu
  change (a.adjunction K).homEquiv A _ (adj.homEquiv _ _
    ((m.mu.app (K, A)).hom ≫ m.target.tensor.map
        (Prod.mkHom (𝟙 _) ((integralDerivedReduction l E Y D hl n).map g)) ≫
      ((m.target.adjunction _).homEquiv _ _).symm
        ((adj.homEquiv B _).symm f))) = _
  rw [← Category.assoc, ← hmu, Category.assoc, adj.homEquiv_naturality_left]
  exact (a.adjunction K).homEquiv_naturality_left g _

private noncomputable def scalarHomIso
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (adj : integralDerivedReduction l E Y D hl n ⊣ scalarReductionDerivedRestriction l E Y n)
    (K : completedIntegralDerivedCategory l E Y D hl)
    (N : Derived.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)) :
    (scalarReductionDerivedRestriction l E Y n).obj
        ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
          (op ((integralDerivedReduction l E Y D hl n).obj K), N)) ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, (scalarReductionDerivedRestriction l E Y n).obj N) := by
  let X := (scalarReductionDerivedRestriction l E Y n).obj
    ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
      (op ((integralDerivedReduction l E Y D hl n).obj K), N))
  let Z := (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
    (op K, (scalarReductionDerivedRestriction l E Y n).obj N)
  let e (A : completedIntegralDerivedCategory l E Y D hl) :=
    scalarHomBijection l E Y D hl a n m adj A K N
  let alpha := e X (𝟙 X)
  let beta := (e Z).symm (𝟙 Z)
  have hb : e Z beta = 𝟙 Z := Equiv.apply_symm_apply _ _
  have hr {A : completedIntegralDerivedCategory l E Y D hl} (f : A ⟶ X) :
      e A f = f ≫ alpha := by
    simpa only [Category.comp_id] using
      scalarHomBijection_precomp l E Y D hl a n m adj f K N (𝟙 X)
  refine ⟨alpha, beta, ?_, ?_⟩
  · apply (e X).injective
    change e X (alpha ≫ beta) = e X (𝟙 X)
    rw [hr]
    change (alpha ≫ beta) ≫ alpha = alpha
    rw [Category.assoc]
    rw [← hr beta, hb, Category.comp_id]
  · rw [← hr beta, hb]

private theorem scalarHomIso_rep
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (adj : integralDerivedReduction l E Y D hl n ⊣ scalarReductionDerivedRestriction l E Y n)
    (A K : completedIntegralDerivedCategory l E Y D hl)
    (N : Derived.{t, u} Y (integralCoefficientCommRingSheaf l E Y n))
    (f : A ⟶ (scalarReductionDerivedRestriction l E Y n).obj
      ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
        (op ((integralDerivedReduction l E Y D hl n).obj K), N))) :
    scalarHomBijection l E Y D hl a n m adj A K N f =
      f ≫ (scalarHomIso l E Y D hl a n m adj K N).hom := by
  change scalarHomBijection l E Y D hl a n m adj A K N f =
    f ≫ scalarHomBijection l E Y D hl a n m adj _ K N (𝟙 _)
  simpa only [Category.comp_id] using
    scalarHomBijection_precomp l E Y D hl a n m adj f K N (𝟙 _)

private theorem scalarHomIso_comparison
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (adj : integralDerivedReduction l E Y D hl n ⊣ scalarReductionDerivedRestriction l E Y n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    let H := (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)
    let X := U.obj (F.obj H)
    ((a.adjunction K).homEquiv X (U.obj (F.obj L))).symm
        (U.map (comparison l E Y D hl m K L) ≫
          (scalarHomIso l E Y D hl a n m adj K (F.obj L)).hom) =
      adj.homEquiv (a.tensor.obj (K, X)) (F.obj L)
        (m.mu.hom.app (K, X) ≫
          m.target.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H))) ≫
          m.mu.inv.app (K, H) ≫ F.map ((a.adjunction K).counit.app L)) := by
  dsimp only
  rw [← scalarHomIso_rep]
  dsimp only [scalarHomBijection, Equiv.trans_apply]
  erw [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit]
  erw [adj.counit.naturality]
  erw [(m.target.adjunction _).homEquiv_naturality_left_symm]
  dsimp only [comparison, Functor.id_obj, Functor.id_map]
  erw [Equiv.symm_apply_apply]
  dsimp only [Iso.homCongr, Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  simp only [Category.comp_id]
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The localized signed map is the normalized reduction comparison, for fixed
resolutions and a fixed augmented two-term coefficient resolution.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2;
Stacks Tags 07A6, 08J7 and 08J9
(blueprint: lem-sf-integral-hom-representative-square).

Proof: the augmentation identifies Q with the finite coefficient unit after
restriction of scalars. Its two free terms make Q K-flat, and make I tensor Q
K-injective: it is the cone, with the appropriate shift, of the multiplication
map on I. Thus Hom(P,I) and Hom(P,I tensor Q) compute the two needed derived
internal Homs. Resolve Hom(P,I) by a K-flat complex when applying the tensor
presentation. The augmentation and the canonical derived scalar counit give
the source comparison s. For t, first apply the scalar internal-Hom adjunction
on every slice, then the same augmentation and the Hom localization comparison.
Transport these comparisons along eP and eI. They are isomorphisms because the
augmentations are quasi-isomorphisms, Q is K-flat, and the Hom targets are
K-injective. To check the square, transpose through the target tensor-Hom
adjunction and test using K-flat representatives. The evaluation condition in
a and the scalar-unit normalization in m identify both composites with the
reduction of evaluation. The signed formula for f gives the Koszul sign from
moving the coefficient factor across P; it cancels precisely the evaluation
ordering sign. The augmentation is used on both sides, so its chosen quotient
identification cancels too. Injectivity of the adjunction Hom equivalence gives
the equality. No invertibility of f is asserted or used. -/
theorem comparison_representative_square
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl)
    (P I Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P) (hI : I.IsKInjective)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L)
    (hQ : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show completedIntegralModuleSheaves l E Y D hl from
      SheafOfModules.unit (completedIntegralCoefficientSheaf l E Y D hl)))
    (eZero : Q.X 0 ≅ (show completedIntegralModuleSheaves l E Y D hl from
      SheafOfModules.unit (completedIntegralCoefficientSheaf l E Y D hl)))
    (epsilon : Q ⟶
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (scalarReductionTarget l E Y n) 0).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))))
    (hepsilon : QuasiIso epsilon)
    (f : ((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := completedIntegralCommRingSheaf l E Y D hl) P I)).obj Q ⟶
        homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := completedIntegralCommRingSheaf l E Y D hl) P
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj I).obj Q))
    (hf : IsSignedHomTensor Y (completedIntegralCommRingSheaf l E Y D hl) P I Q f) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    ∃ (s : U.obj (F.obj ((hom.{t, u} Y R).obj (op K, L))) ≅
          DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q))
        (t : U.obj ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
            (op (F.obj K), F.obj L)) ≅
          DerivedCategory.Q.obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
              (((totalTensor.{t, u} Y R).obj I).obj Q))),
      U.map (comparison l E Y D hl m K L) ≫ t.hom =
        s.hom ≫ DerivedCategory.Q.map f := by
  let R := completedIntegralCommRingSheaf l E Y D hl
  let U := scalarReductionDerivedRestriction l E Y n
  let F := integralDerivedReduction l E Y D hl n
  let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
  let H := (hom.{t, u} Y R).obj (op K, L)
  let J := ((totalTensor.{t, u} Y R).obj I).obj Q
  obtain ⟨r, s, hs⟩ := reduced_evaluation_representative l E Y D hl a n m K L
    P I Q hP hI eP eI hQ epsilon hepsilon f hf
  have hJ : J.IsKInjective :=
    twoTerm_tensor_isKInjective Y R I Q hI hzero eNeg eZero
  have : IsIso (homModelMap.{t, u} Y R P J) := homModelMap_isIso Y R P J hJ
  let j : DerivedCategory.Q.obj
      (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P J) ≅
      (hom.{t, u} Y R).obj (op K, U.obj (F.obj L)) :=
    asIso (homModelMap.{t, u} Y R P J) ≪≫
      (hom.{t, u} Y R).mapIso (Iso.prod eP.symm.op r.symm)
  let sigma := scalarHomIso l E Y D hl a n m adj K (F.obj L)
  refine ⟨s, sigma ≪≫ j.symm, ?_⟩
  apply (cancel_mono j.hom).mp
  have heq : U.map (comparison l E Y D hl m K L) ≫ sigma.hom =
      s.hom ≫ DerivedCategory.Q.map f ≫ j.hom := by
    apply ((a.adjunction K).homEquiv _ _).symm.injective
    exact (scalarHomIso_comparison l E Y D hl a n m adj K L).trans hs.symm
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using heq

end WeilConjectures.IntegralHom
