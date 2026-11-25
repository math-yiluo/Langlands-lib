/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization

/-! # Evaluation law for a normalized reindexing comparison

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0GMX, 0A8X, 08J9.
(blueprint: lem-pod-reindexing-evaluation-law).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
-- Cache the sheaf composition witness without repeatedly reconstructing the small site.
set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose {C : Type*} [Category C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C] :
    J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  exact (equivSmallModel.{u + 1} C).hasSheafCompose J
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

attribute [local instance 1000001] cachedCompose

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] podReindexingCoefficient podReindexingHomModel
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses coefficientTotalTensor
  coefficientTensorGenerator Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  SheafOfModules.monoidalCategory

private theorem uncurry_formula {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {U M N : D} (f : U ⟶ H.obj (op M, N)) :
    (S.transpose U M N).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 M)) ≫ S.evaluation M N := by
  let : MonoidalCategory D := S.monoidal
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation, Adjunction.homEquiv, Equiv.symm,
    MonoidalCategory.tensor, MonoidalCategory.tensorRight, Functor.flip,
    MonoidalCategory.curriedTensor, Functor.comp_obj, Prod.sectR_obj]
  simp only [MonoidalCategory.tensorHom_id]
  rfl

private theorem evaluation_natural {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {M M' N N' : D} (a : M' ⟶ M) (b : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 M')) ≫
      S.evaluation M' N' =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op M, N))) a) ≫
        S.evaluation M N ≫ b := by
  have hs : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M')) ≫
      S.evaluation M' N =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op M, N))) a) ≫ S.evaluation M N := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorRight,
      MonoidalCategory.tensorLeft, Functor.flip, MonoidalCategory.curriedTensor,
      Functor.comp_map, Prod.sectR_map, Prod.sectL_map] using
        S.evaluation_naturality M M' N a
  have ht : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op M')) b)) (𝟙 M')) ≫
      S.evaluation M' N' = S.evaluation M' N ≫ b := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_obj, MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorRight, Functor.flip, MonoidalCategory.curriedTensor,
      Functor.comp_obj, Functor.comp_map, Prod.sectR_obj, Prod.sectR_map,
      Functor.id_obj, Functor.id_map] using (S.adjunction M').counit.naturality b
  have hp : Prod.mkHom a.op b =
      Prod.mkHom a.op (𝟙 N) ≫ Prod.mkHom (𝟙 (op M')) b := by simp
  rw [hp, H.map_comp]
  have hsplit : Prod.mkHom
      (H.map (Prod.mkHom a.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op M')) b)) (𝟙 M') =
      Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op M')) b)) (𝟙 M') := by simp
  rw [hsplit, S.tensor.map_comp, Category.assoc, ht, ← Category.assoc, hs]
  exact Category.assoc _ _ _

private theorem uncurry_transport {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {U M M' N N' : D} (f : U ⟶ H.obj (op M, N))
    (a : M' ⟶ M) (b : N ⟶ N') :
    S.tensor.map (Prod.mkHom (f ≫ H.map (Prod.mkHom a.op b)) (𝟙 M')) ≫
      S.evaluation M' N' =
      S.tensor.map (Prod.mkHom f a) ≫ S.evaluation M N ≫ b := by
  have hp : Prod.mkHom (f ≫ H.map (Prod.mkHom a.op b)) (𝟙 M') =
      Prod.mkHom f (𝟙 M') ≫
        Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 M') := by simp
  rw [hp, S.tensor.map_comp, Category.assoc, evaluation_natural,
    ← Category.assoc, ← Category.assoc, ← S.tensor.map_comp]
  simp

private theorem evaluation_iso_natural {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {M M' N N' : D} (a : M ≅ M') (b : N ≅ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.inv.op b.hom)) a.hom) ≫
      S.evaluation M' N' = S.evaluation M N ≫ b.hom := by
  have hp : Prod.mkHom (H.map (Prod.mkHom a.inv.op b.hom)) a.hom =
      Prod.mkHom (𝟙 (H.obj (op M, N))) a.hom ≫
        Prod.mkHom (H.map (Prod.mkHom a.inv.op b.hom)) (𝟙 M') := by simp
  rw [hp, S.tensor.map_comp, Category.assoc, evaluation_natural,
    ← Category.assoc, ← Category.assoc, ← S.tensor.map_comp]
  simp

private theorem evaluation_iso {D D' : Type*} [Category D] [Category D']
    {H : Dᵒᵖ × D ⥤ D} {H' : D'ᵒᵖ × D' ⥤ D'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : D ⥤ D') (c : S.tensor ⋙ F ≅ (F.prod F) ⋙ S'.tensor)
    (h : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    {M M' N N' : D} (a : M ≅ M') (b : N ≅ N')
    (he : c.hom.app (H.obj (op M, N), M) ≫
      S'.tensor.map (Prod.mkHom (h.hom.app (op M, N)) (𝟙 (F.obj M))) ≫
        S'.evaluation (F.obj M) (F.obj N) = F.map (S.evaluation M N)) :
    c.hom.app (H.obj (op M', N'), M') ≫
      S'.tensor.map (Prod.mkHom (h.hom.app (op M', N')) (𝟙 (F.obj M'))) ≫
        S'.evaluation (F.obj M') (F.obj N') = F.map (S.evaluation M' N') := by
  let e := H.mapIso (a.symm.op.prod b)
  have : IsIso (Prod.mkHom e.hom a.hom) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (F.map (S.tensor.map (Prod.mkHom e.hom a.hom)))).1
  have ht := c.hom.naturality (Prod.mkHom e.hom a.hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  have hh := h.hom.naturality (Prod.mkHom a.inv.op b.hom)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map] at hh
  have hp : Prod.mkHom (F.map e.hom) (F.map a.hom) ≫
      Prod.mkHom (h.hom.app (op M', N')) (𝟙 (F.obj M')) =
      Prod.mkHom (F.map e.hom ≫ h.hom.app (op M', N')) (F.map a.hom) := by simp
  have hp' : Prod.mkHom (h.hom.app (op M, N)) (𝟙 (F.obj M)) ≫
      Prod.mkHom (H'.map (Prod.mkHom (F.map a.inv).op (F.map b.hom)))
        (F.map a.hom) =
      Prod.mkHom (h.hom.app (op M, N) ≫
        H'.map (Prod.mkHom (F.map a.inv).op (F.map b.hom))) (F.map a.hom) := by simp
  calc
    _ = c.hom.app (H.obj (op M, N), M) ≫
        S'.tensor.map (Prod.mkHom (F.map e.hom ≫ h.hom.app (op M', N'))
          (F.map a.hom)) ≫ S'.evaluation (F.obj M') (F.obj N') := by
      rw [← Category.assoc _ (c.hom.app _), ht]
      simp only [Category.assoc]
      rw [← S'.tensor.map_comp_assoc, hp]
    _ = c.hom.app (H.obj (op M, N), M) ≫
        S'.tensor.map (Prod.mkHom (h.hom.app (op M, N)) (𝟙 (F.obj M))) ≫
          S'.tensor.map
            (Prod.mkHom (H'.map (Prod.mkHom (F.map a.inv).op (F.map b.hom)))
              (F.map a.hom)) ≫ S'.evaluation (F.obj M') (F.obj N') := by
      simp only [Quiver.Hom.unop_op] at hh
      rw [show F.map e.hom ≫ h.hom.app (op M', N') = _ from hh]
      rw [← S'.tensor.map_comp_assoc, hp']
    _ = c.hom.app (H.obj (op M, N), M) ≫
        S'.tensor.map (Prod.mkHom (h.hom.app (op M, N)) (𝟙 (F.obj M))) ≫
          S'.evaluation (F.obj M) (F.obj N) ≫ F.map b.hom := by
      have hv := evaluation_iso_natural S' (F.mapIso a) (F.mapIso b)
      dsimp only [Functor.mapIso_hom, Functor.mapIso_inv] at hv
      rw [hv]
    _ = F.map (S.evaluation M N) ≫ F.map b.hom := by
      simpa only [Category.assoc] using congrArg (· ≫ F.map b.hom) he
    _ = _ := by
      rw [← F.map_comp, ← evaluation_iso_natural S a b, F.map_comp]
      rfl

private theorem evaluation_models {D D' : Type*} [Category D] [Category D']
    {H : Dᵒᵖ × D ⥤ D} {H' : D'ᵒᵖ × D' ⥤ D'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : D ⥤ D') (c : S.tensor ⋙ F ≅ (F.prod F) ⋙ S'.tensor)
    (h : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    {A M N Z : D} {A' M' N' Z' : D'}
    (a : A ≅ H.obj (op M, N)) (b : A' ⟶ H'.obj (op M', N'))
    (iA : F.obj A ≅ A') (iM : F.obj M ≅ M') (iN : F.obj N ≅ N')
    (t : Z ≅ S.tensor.obj (A, M)) (t' : Z' ≅ S'.tensor.obj (A', M'))
    (k : F.obj Z ≅ Z') (e : Z ⟶ N) (e' : Z' ⟶ N')
    (ht : F.map t.hom ≫ c.hom.app (A, M) ≫
      S'.tensor.map (Prod.mkHom iA.hom iM.hom) = k.hom ≫ t'.hom)
    (hh : F.map a.hom ≫ h.hom.app (op M, N) =
      iA.hom ≫ b ≫ H'.map (Prod.mkHom iM.hom.op iN.inv))
    (he : t.hom ≫ S.tensor.map (Prod.mkHom a.hom (𝟙 M)) ≫ S.evaluation M N = e)
    (he' : t'.hom ≫ S'.tensor.map (Prod.mkHom b (𝟙 M')) ≫ S'.evaluation M' N' = e')
    (hk : F.map e ≫ iN.hom = k.hom ≫ e') :
    c.hom.app (H.obj (op M, N), M) ≫
      S'.tensor.map (Prod.mkHom (h.hom.app (op M, N)) (𝟙 (F.obj M))) ≫
        S'.evaluation (F.obj M) (F.obj N) = F.map (S.evaluation M N) := by
  have : IsIso (Prod.mkHom a.hom (𝟙 M)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (F.map (t.hom ≫ S.tensor.map (Prod.mkHom a.hom (𝟙 M))))).1
  apply (cancel_mono iN.hom).1
  have hn := c.hom.naturality (Prod.mkHom a.hom (𝟙 M))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [F.map_id] at hn
  have hp : Prod.mkHom (F.map a.hom) (𝟙 (F.obj M)) ≫
      Prod.mkHom (h.hom.app (op M, N)) (𝟙 (F.obj M)) =
      Prod.mkHom (F.map a.hom ≫ h.hom.app (op M, N)) (𝟙 (F.obj M)) := by simp
  have hp' : Prod.mkHom iA.hom iM.hom ≫ Prod.mkHom b (𝟙 M') =
      Prod.mkHom (iA.hom ≫ b) iM.hom := by simp
  calc
    _ = F.map t.hom ≫ c.hom.app (A, M) ≫
        S'.tensor.map (Prod.mkHom (F.map a.hom ≫ h.hom.app (op M, N))
          (𝟙 (F.obj M))) ≫ S'.evaluation (F.obj M) (F.obj N) ≫ iN.hom := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc _ (c.hom.app _), hn]
      simp only [Category.assoc]
      rw [← S'.tensor.map_comp_assoc, hp]
    _ = F.map t.hom ≫ c.hom.app (A, M) ≫
        S'.tensor.map (Prod.mkHom (iA.hom ≫ b) iM.hom) ≫
          S'.evaluation M' N' := by
      rw [hh, ← Category.assoc iA.hom b]
      have hu := congrArg (fun z ↦ F.map t.hom ≫ c.hom.app (A, M) ≫ z ≫ iN.hom)
        (uncurry_transport S' (iA.hom ≫ b) iM.hom iN.inv)
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hu
    _ = (F.map t.hom ≫ c.hom.app (A, M) ≫
        S'.tensor.map (Prod.mkHom iA.hom iM.hom)) ≫
          S'.tensor.map (Prod.mkHom b (𝟙 M')) ≫ S'.evaluation M' N' := by
      simp only [Category.assoc]
      rw [← S'.tensor.map_comp_assoc, hp']
    _ = k.hom ≫ e' := by rw [ht, Category.assoc, he']
    _ = (F.map (t.hom ≫ S.tensor.map (Prod.mkHom a.hom (𝟙 M))) ≫
        F.map (S.evaluation M N)) ≫ iN.hom := by
      rw [← hk]
      simpa only [F.map_comp, Category.assoc] using
        congrArg (fun z ↦ F.map z ≫ iN.hom) he.symm

private theorem total_hom_ext (W : Scheme.{u}) (s : Option ℕ)
    (P L I : K l E W s) (f g : (total l E W s).obj (P, L) ⟶ I)
    (h : ∀ (p q : ℤ) (U : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (L.X q).val.obj U),
      (f.f (p + q)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (podReindexingRing l E W s) P L p q (p + q) rfl U x y) =
        (g.f (p + q)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (podReindexingRing l E W s) P L p q (p + q) rfl U x y)) : f = g := by
  exact WeilConjectures.coefficient_total_ext.{u, u + 1, u}
    (ProEt.topology W) (podReindexingRing l E W s) P L I f g h

private noncomputable def chainUncurry (W : Scheme.{u}) (s : Option ℕ)
    (A P I : K l E W s) (φ : A ⟶ hom l E W s P I) :
    (total l E W s).obj (A, P) ⟶ I :=
  (CategoryTheory.RingedDerivedNative.chainEquiv.{u + 1, u, u}
    (ProEt.topology W) (podReindexingRing l E W s) A P I).symm φ

private theorem chainUncurry_pure (W : Scheme.{u}) (s : Option ℕ)
    (A P I : K l E W s) (φ : A ⟶ hom l E W s P I) :
    IsCoefficientTensorCurry.{u, u + 1, u} (ProEt.topology W)
      (podReindexingRing l E W s) A P I (chainUncurry l E W s A P I φ) φ := by
  intro p q U x y
  exact CategoryTheory.RingedDerivedNative.chainEquiv_symm_pure.{u + 1, u, u}
    (ProEt.topology W) (podReindexingRing l E W s) A P I φ
    p q (p + q) rfl (add_comm q p) U x y

private theorem chain_evaluation {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (A P I : K l E Y s)
    (φ : A ⟶ hom l E Y s P I) :
    (podReindexingComplexFunctor l E g s).map (chainUncurry l E Y s A P I φ) =
      (c.tensorChain A P).hom ≫ chainUncurry l E X s
        ((podReindexingComplexFunctor l E g s).obj A)
        ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I)
        ((podReindexingComplexFunctor l E g s).map φ ≫ (c.chain P I).hom) := by
  let R := podReindexingComplexFunctor l E g s
  apply (cancel_epi (c.tensorChain A P).inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply total_hom_ext l E X s
  intro p q U x y
  let gy := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (podReindexingRing l E Y s) A P p q (p + q) rfl
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x y
  let gx := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
    (podReindexingRing l E X s) (R.obj A) (R.obj P) p q (p + q) rfl U x y
  have hi : ((c.tensorChain A P).inv.f (p + q)).val.app U gx = gy := by
    have hc : ((c.tensorChain A P).hom.f (p + q)).val.app U gy = gx :=
      c.tensorChain_pure A P p q (p + q) rfl U.unop x y
    have he : ((c.tensorChain A P).inv.f (p + q)).val.app U
        (((c.tensorChain A P).hom.f (p + q)).val.app U gy) = gy :=
      congrArg (fun f ↦ (f.f (p + q)).val.app U gy) (c.tensorChain A P).hom_inv_id
    exact (congrArg (fun z ↦ ((c.tensorChain A P).inv.f (p + q)).val.app U z)
      hc.symm).trans he
  change ((chainUncurry l E Y s A P I φ).f (p + q)).val.app
    (op ((proEtaleIsoPostcompose g).obj U.unop))
      (((c.tensorChain A P).inv.f (p + q)).val.app U gx) = _
  rw [hi]
  rw [chainUncurry_pure, chainUncurry_pure]
  change _ = (((proj l E X s (R.obj P) (R.obj I) p q (p + q) (add_comm q p)).val.app U
    (((c.chain P I).hom.f p).val.app U
      ((φ.f p).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x))).app
        (op (Over.mk (𝟙 U.unop)))).hom y
  have hc (k : ℤ) (hk : q + p = k) :
      (((proj l E X s (R.obj P) (R.obj I) p q k hk).val.app U
        (((c.chain P I).hom.f p).val.app U
          ((φ.f p).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x))).app
            (op (Over.mk (𝟙 U.unop)))).hom y =
      (((proj l E Y s P I p q k hk).val.app
        (op ((proEtaleIsoPostcompose g).obj U.unop))
          ((φ.f p).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x)).app
            (op (Over.mk (𝟙 ((proEtaleIsoPostcompose g).obj U.unop))))).hom y := by
    subst k
    have hc₀ := c.chain_projection P I p q U.unop U.unop
      (𝟙 U.unop) ((φ.f p).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x) y
    rw [(proEtaleIsoPostcompose g).map_id] at hc₀
    exact hc₀
  exact (hc (p + q) (add_comm q p)).symm

private theorem normalized_uncurry (W : Scheme.{u})
    [EssentiallySmall.{u + 1} W.ProEt] (s : Option ℕ)
    (S : Closed l E W s) (T : Models l E W s S)
    (A P I : K l E W s) (hI : I.IsKInjective)
    (hA : CochainComplex.IsKFlatIndependentCoefficients (R := podReindexingRing l E W s) A)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := podReindexingRing l E W s) P)
    (φ : A ⟶ hom l E W s P I) :
    (T.iso (ProEt.topology W) (podReindexingRing l E W s) S A P hA hP).hom ≫
      S.tensor.map (Prod.mkHom
        ((podReindexingQ l E W s).map φ ≫
          (@podReindexingHomModel l _ E _ _ _ W s P I hI).inv)
        (𝟙 ((podReindexingQ l E W s).obj P))) ≫
      S.evaluation ((podReindexingQ l E W s).obj P) ((podReindexingQ l E W s).obj I) =
        (podReindexingQ l E W s).map (chainUncurry l E W s A P I φ) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E W s)
  let Q := podReindexingQ l E W s
  have hj : Q.map φ ≫ (@podReindexingHomModel l _ E _ _ _ W s P I hI).inv =
      Q.map (φ ≫ ((homComplexFunctor (R := podReindexingRing l E W s)).obj (op P)).map
        ((WeilConjectures.coefficientHomAugmentation.{u, u + 1, u}
          (ProEt.topology W) (podReindexingRing l E W s)).app I)) ≫
        (coefficientHomResolutionIso.{u, u + 1, u, u + 2}
          (ProEt.topology W) (podReindexingRing l E W s) P I).inv := by
    have hj₀ : (@podReindexingHomModel l _ E _ _ _ W s P I hI).inv =
        Q.map (((podReindexingHom l E W s).obj (op P)).map
          ((WeilConjectures.coefficientHomAugmentation.{u, u + 1, u}
            (ProEt.topology W) (podReindexingRing l E W s)).app I)) ≫
          (coefficientHomResolutionIso.{u, u + 1, u, u + 2}
            (ProEt.topology W) (podReindexingRing l E W s) P I).inv := by
      unfold podReindexingHomModel WeilConjectures.coefficientHomAugmentation
        coefficientHomResolutionIso
      rfl
    rw [hj₀, Q.map_comp]
    exact (Category.assoc _ _ _).symm
  have hn := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2}
    (ProEt.topology W) (podReindexingRing l E W s) S T A P I hA hP
    (chainUncurry l E W s A P I φ) φ (chainUncurry_pure l E W s A P I φ)
  rw [← hj] at hn
  have he := congrArg
    (fun z ↦ (T.iso (ProEt.topology W) (podReindexingRing l E W s) S A P hA hP).hom ≫ z) hn
  rw [uncurry_formula] at he
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he

-- Elaborate the fixed Hom and tensor model equations across the two sites.
private theorem evaluation_representatives {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := podReindexingRing l E Y s) P)
    (hI : I.IsKInjective) :
    let F := podReindexingDerivedFunctor l E g s
    let Q := podReindexingQ l E Y s
    c.tensor.hom.app ((podReindexingDerivedHom l E Y s).obj (op (Q.obj P), Q.obj I),
      Q.obj P) ≫ SX.tensor.map (Prod.mkHom (c.derived.hom.app (op (Q.obj P), Q.obj I))
        (𝟙 (F.obj (Q.obj P)))) ≫ SX.evaluation (F.obj (Q.obj P)) (F.obj (Q.obj I)) =
      F.map (SY.evaluation (Q.obj P) (Q.obj I)) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let F := podReindexingDerivedFunctor l E g s
  let R := podReindexingComplexFunctor l E g s
  let QY := podReindexingQ l E Y s
  let QX := podReindexingQ l E X s
  let η := podReindexingDerivedFactors l E g s
  obtain ⟨A, φ, hA, _, hφ, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (hom l E Y s P I)
  have : IsIso (QY.map φ) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hφ
  obtain ⟨hRA, hRP, ht⟩ := c.tensor_model A P hA hP
  obtain ⟨hRI, hh⟩ := c.derived_model P I hI
  let jY := @podReindexingHomModel l _ E _ _ _ Y s P I hI
  let jX := @podReindexingHomModel l _ E _ _ _ X s (R.obj P) (R.obj I) hRI
  let a := asIso (QY.map φ) ≪≫ jY.symm
  let φ' := R.map φ ≫ (c.chain P I).hom
  let b := QX.map φ' ≫ jX.inv
  let tY := TY.iso (ProEt.topology Y) (podReindexingRing l E Y s) SY A P hA hP
  let tX := TX.iso (ProEt.topology X) (podReindexingRing l E X s) SX
    (R.obj A) (R.obj P) hRA hRP
  let k := η.app ((total l E Y s).obj (A, P)) ≪≫ QX.mapIso (c.tensorChain A P)
  let e := QY.map (chainUncurry l E Y s A P I φ)
  let e' := QX.map (chainUncurry l E X s (R.obj A) (R.obj P) (R.obj I) φ')
  apply evaluation_models SY SX F c.tensor c.derived a b
    (η.app A) (η.app P) (η.app I) tY tX k e e'
  · dsimp only [tY, tX, k, CoefficientTensorModels.iso, Iso.app_hom, Iso.trans_hom,
      Functor.mapIso_hom, F, QX, QY, R, η, Functor.comp_obj, Functor.prod_obj,
      coefficientKFlatInclusion, ObjectProperty.ι_obj, total] at ht ⊢
    exact ht.trans (Category.assoc _ _ _).symm
  · have hj : F.map jY.inv ≫ c.derived.hom.app (op (QY.obj P), QY.obj I) =
        η.hom.app (hom l E Y s P I) ≫ QX.map (c.chain P I).hom ≫ jX.inv ≫
          (podReindexingDerivedHom l E X s).map
            (Prod.mkHom ((η.app P).hom.op) (η.app I).inv) := by
      change c.derived.hom.app (op (QY.obj P), QY.obj I) =
        F.map jY.hom ≫ η.hom.app (hom l E Y s P I) ≫
          QX.map (c.chain P I).hom ≫ jX.inv ≫
            (podReindexingDerivedHom l E X s).map
              (Prod.mkHom ((η.app P).hom.op) (η.app I).inv) at hh
      exact (F.mapIso jY).inv_comp_eq.mpr hh
    change F.map (QY.map φ ≫ jY.inv) ≫ _ = _
    rw [F.map_comp, Category.assoc, hj]
    have hn := η.hom.naturality φ
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc (F.map (QY.map φ)) (η.hom.app _), hn]
    simp only [b, φ', Functor.map_comp, Category.assoc]
    rfl
  · exact normalized_uncurry l E Y s SY TY A P I hI hA hP φ
  · exact normalized_uncurry l E X s SX TX (R.obj A) (R.obj P) (R.obj I) hRI hRA hRP φ'
  · have hn := η.hom.naturality (chainUncurry l E Y s A P I φ)
    dsimp only [Functor.comp_map] at hn
    change F.map (QY.map _) ≫ η.hom.app I = _
    rw [hn, chain_evaluation l E g s SX SY TX TY c A P I φ, QX.map_comp]
    simp only [k, e', Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rfl

/--
Every normalized comparison satisfies the evaluation equation.  This is the
representative evaluation step, with the comparison itself supplied as input.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0GMX, 0A8X and 08J9
(blueprint: lem-pod-reindexing-evaluation-law).

Proof: choose flat-term K-flat and K-injective representatives.  The chain
transpose identifies evaluation on a pure tensor with application of the Hom
map.  The `chain_projection` and `tensorChain_pure` equations identify the two
reindexed maps on every pure generator.  Extensionality after sheafification,
then localization and naturality along resolutions, gives the displayed law for
all derived objects.
-/
theorem comparison_evaluation_law {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∀ M N : podReindexingDerived l E Y s,
      c.tensor.hom.app ((podReindexingDerivedHom l E Y s).obj (op M, N), M) ≫
          SX.tensor.map (Prod.mkHom (c.derived.hom.app (op M, N))
            (𝟙 ((podReindexingDerivedFunctor l E g s).obj M))) ≫
          SX.evaluation ((podReindexingDerivedFunctor l E g s).obj M)
            ((podReindexingDerivedFunctor l E g s).obj N) =
        (podReindexingDerivedFunctor l E g s).map (SY.evaluation M N) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (ProEt.topology Y) (podReindexingRing l E Y s)).1
  let Q := podReindexingQ l E Y s
  intro M N
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage M)
  have : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  let eM : Q.obj P ≅ M := asIso (Q.map p) ≪≫ Q.objObjPreimageIso M
  let N₀ := Q.objPreimage N
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1}
    (podReindexingModules l E Y s)).obj N₀
  let η := (CochainComplex.toKInjectiveResolution.{u + 1}
    (podReindexingModules l E Y s)).app N₀
  have hI : I.IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ N₀
  have hη : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ N₀).2
  have : IsIso (Q.map η) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hη
  let eN : Q.obj I ≅ N := (asIso (Q.map η)).symm ≪≫ Q.objObjPreimageIso N
  exact evaluation_iso SY SX (podReindexingDerivedFunctor l E g s) c.tensor c.derived eM eN
    (evaluation_representatives l E g s SX SY TX TY c P I hP hI)

end WeilConjectures.PodReindexingCoherence
