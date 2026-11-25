/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorKoszulExistence
import all WeilConjectures.SixFunctors.IntegralHom.IntegralHomRepresentativeUncurry
import all WeilConjectures.SixFunctors.IntegralHom.IntegralHomRepresentativeSquare
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

/-! # Signed representatives of the normalized left-adjoint comparison

Source: Stacks 07A4 and 08J9; the tensor-Hom normalization in the coefficient
Verdier argument
(blueprint: lem-sf-ordinary-tensor-adjoint-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
  [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

attribute [local instance 1000001] CategoryTheory.RingedDerivedNative.cachedCompose

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses
  homModelMap HasDerivedCategory.standard SheafOfModules.monoidalCategory

private theorem comparison_uncurry
    {C : Type*} [Category* C] {F G H : C ⥤ C}
    (a : F ⊣ H) (b : G ⊣ H) {N I : C} (q : N ⟶ H.obj I) :
    (a.leftAdjointUniq b).hom.app N ≫ (b.homEquiv N I).symm q =
      (a.homEquiv N I).symm q := by
  rw [Adjunction.homEquiv_counit, ← Category.assoc,
    ← (a.leftAdjointUniq b).hom.naturality q, Category.assoc,
    Adjunction.leftAdjointUniq_hom_app_counit, ← Adjunction.homEquiv_counit]

private theorem derived_map_surjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P I : CochainComplex C ℤ) [I.IsKInjective] :
    Function.Surjective (fun f : P ⟶ I ↦ DerivedCategory.Q.map f) := by
  intro f
  obtain ⟨g, hg⟩ :=
    (CategoryTheory.RingedDerivedNative.GenericDerived.qHomEquiv P I).surjective f
  obtain ⟨q, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  exact ⟨q,
    (CategoryTheory.RingedDerivedNative.GenericDerived.qHomEquiv_map P I q).symm.trans hg⟩

/-- Signed and unsigned evaluations agree after the prescribed tensor exchange. -/
private theorem signed_evaluation_comp_exchange
    (P Q I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (s : (coefficientTotalTensor.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, Q) ⟶
      (coefficientTotalTensor.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (Q, P))
    (hs : ∀ (i j k : ℤ) (h : i + j = k) (h' : j + i = k)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (s.f k).val.app U
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j k h U x y) =
          (i * j).negOnePow • coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R Q P j i k h' U y x)
    (q : Q ⟶ homComplex (R := R) P I)
    (b : (coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, Q) ⟶ I)
    (hb : ∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (b.f (i + j)).val.app U (totalPair.{t, u} Y R P Q i j U x y) =
        (i * j).negOnePow • evaluate Y R P I j i U ((q.f j).val.app U y) x)
    (v : (coefficientTotalTensor.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (Q, P) ⟶ I)
    (hv : ∀ (j i k : ℤ) (h : j + i = k) (h' : i + j = k)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (y : (Q.X j).val.obj U) (x : (P.X i).val.obj U),
      (v.f k).val.app U (coefficientTensorGenerator.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R Q P j i k h U y x) =
        (((q.f j ≫ homComplexπ P I j i k h').val.app U y).app
          (op (Over.mk (𝟙 U.unop)))) x) :
    b = s ≫ v := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  refine total_generator_ext Y R P Q I (f := b) (g := s ≫ v) ?_
  intro i j k hij U x y
  subst k
  have hpair : totalPair.{t, u} Y R P Q i j U x y =
      coefficientTensorGenerator.{u, t + 1, t} J R P Q i j (i + j) rfl U x y := by
    simp only [totalPair, pair, ordinaryTensor, coefficientTensorGenerator,
      CochainComplex.ιMapBifunctor]
    rfl
  change (b.f (i + j)).val.app U _ =
    (v.f (i + j)).val.app U ((s.f (i + j)).val.app U _)
  calc
    _ = (i * j).negOnePow • evaluate Y R P I j i U ((q.f j).val.app U y) x := by
      simpa only [hpair] using hb i j U x y
    _ = (v.f (i + j)).val.app U ((i * j).negOnePow •
        coefficientTensorGenerator.{u, t + 1, t} J R Q P j i (i + j)
          (add_comm j i) U y x) := by
      simp only [Units.smul_def, map_zsmul]
      congr 1
      simpa only [evaluate, projection, SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply] using (hv j i (i + j) (add_comm j i) rfl U y x).symm
    _ = _ := by rw [hs i j (i + j) rfl (add_comm j i) U x y]

-- Comparing the universe-polymorphic Hom and tensor models needs extra elaboration work.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] totalPair pair projection evaluate in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem representative_square_after_injective
    (a : TensorPresentation.{t, u} Y R)
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
    (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S)
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) (hQ : flat.{t, u} Y R Q)
    (s : (coefficientTotalTensor.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, Q) ⟶
      (coefficientTotalTensor.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (Q, P))
    (hs : ∀ (i j k : ℤ) (h : i + j = k) (h' : j + i = k)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (s.f k).val.app U
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j k h U x y) =
          (i * j).negOnePow • coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R Q P j i k h' U y x)
    (I : CochainComplex (Modules.{t, u} Y R) ℤ) (hI : I.IsKInjective)
    (f : S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj I) :
    (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
      ((a.adjunction (DerivedCategory.Q.obj P)).leftAdjointUniq
        (S.adjunction (DerivedCategory.Q.obj P))).hom.app (DerivedCategory.Q.obj Q)) ≫ f =
      (DerivedCategory.Q.map s ≫ T.comparison.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩)) ≫ f := by
  classical
  have : I.IsKInjective := hI
  have : (homComplex (R := R) P I).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, t + 1, t} P I hP
  have : IsIso (homModelMap.{t, u} Y R P I) := homModelMap_isIso Y R P I hI
  let ξ := S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj I) f
  have hqex := derived_map_surjective Q (homComplex (R := R) P I)
    (ξ ≫ inv (homModelMap.{t, u} Y R P I))
  let q := hqex.choose
  have hf : DerivedCategory.Q.map q = ξ ≫ inv (homModelMap.{t, u} Y R P I) :=
    hqex.choose_spec
  have hq : DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I = ξ := by
    rw [hf, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hbex := a.evaluation P I Q hP hQ hI q
  let b := hbex.choose
  have hb := hbex.choose_spec.1
  have hba := hbex.choose_spec.2
  have hvex := representative_uncurry_evaluation Y R S T Q P I hQ hP q
  let v := hvex.choose
  have hv := hvex.choose_spec.1
  have hvs := hvex.choose_spec.2
  have hbv : b = s ≫ v :=
    signed_evaluation_comp_exchange Y R P Q I s hs q b hb v hv
  have hba' : a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
      ((a.adjunction (DerivedCategory.Q.obj P)).homEquiv _ _).symm ξ =
        DerivedCategory.Q.map b := by
    rw [← hq]
    rw [Adjunction.homEquiv_counit]
    change _ ≫ (a.tensor.map _ ≫
      (a.parameterAdjunction.adj (DerivedCategory.Q.obj P)).counit.app _) = _
    rw [← hba]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rfl
  have hξ : (S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj I)).symm ξ = f :=
    (S.transpose _ _ _).symm_apply_apply f
  have hvs' : T.comparison.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) ≫ f =
      DerivedCategory.Q.map v := by
    have hun : (S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj I)).symm
        (DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I) = f :=
      (congrArg (S.transpose _ _ _).symm hq).trans hξ
    exact (congrArg
      (fun z ↦ T.comparison.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) ≫ z) hun).symm.trans hvs
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  calc
    _ = a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        ((a.adjunction (DerivedCategory.Q.obj P)).homEquiv _ _).symm ξ := by
      rw [Category.assoc]
      apply congrArg (fun z ↦ a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫ z)
      have hc := comparison_uncurry (a.adjunction (DerivedCategory.Q.obj P))
        (S.adjunction (DerivedCategory.Q.obj P)) ξ
      change _ ≫ (S.transpose _ _ _).symm ξ = _ at hc
      rw [hξ] at hc
      exact hc
    _ = DerivedCategory.Q.map b := hba'
    _ = DerivedCategory.Q.map s ≫ DerivedCategory.Q.map v :=
      (congrArg DerivedCategory.Q.map hbv).trans (DerivedCategory.Q.map_comp s v)
    _ = _ := by rw [Category.assoc, hvs']

-- Comparing the universe-polymorphic Hom and tensor models needs extra elaboration work.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] totalPair pair projection evaluate in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The normalized comparison of left adjoints is the signed total-tensor exchange
on K-flat representatives.

Source: Stacks 07A4, 08J9; blueprint theorem-verdier-biduality--3, paragraph 1.
Proof: take the existing Koszul exchange of total complexes. To identify its
localization with the comparison of adjoints, postcompose with an injective
resolution of the target. Every curried morphism into the resulting derived Hom
is represented by a chain map into the Hom complex, since Hom from a K-flat
complex into a K-injective complex is K-injective. The signed evaluation of the
left presentation and the unsigned evaluation of the right presentation then
agree after the Koszul exchange, on every homogeneous pure tensor. Pure tensors
generate the total tensor, so the chain maps agree. Uniqueness of the left-adjoint
comparison preserves uncurrying. Cancel the resolution isomorphism.
(blueprint: lem-sf-ordinary-tensor-adjoint-representative). -/
theorem tensorAdjointComparison_representative
    (a : TensorPresentation.{t, u} Y R)
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
    (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S)
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) (hQ : flat.{t, u} Y R Q) :
    ∃ s : (coefficientTotalTensor.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, Q) ⟶
      (coefficientTotalTensor.{u, t + 1, t}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (Q, P),
      (∀ (i j k : ℤ) (h : i + j = k) (h' : j + i = k)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (s.f k).val.app U
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j k h U x y) =
          (i * j).negOnePow • coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R Q P j i k h' U y x) ∧
      a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
          ((a.adjunction (DerivedCategory.Q.obj P)).leftAdjointUniq
            (S.adjunction (DerivedCategory.Q.obj P))).hom.app (DerivedCategory.Q.obj Q) =
        DerivedCategory.Q.map s ≫ T.comparison.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) := by
  classical
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  have hσex := ringedTensor_koszul_exists.{t + 1, t, u, (max u (t + 1)) + 1}
    J R S T
  let σ := hσex.choose
  have hσ := hσex.choose_spec
  have hsex := hσ P Q hP hQ
  let s := hsex.choose
  have hs := hsex.choose_spec.1
  refine ⟨s.hom, hs, ?_⟩
  have : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      J R).1
  let Z := S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P)
  let V := DerivedCategory.Q.objPreimage Z
  let I := (CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)}
    (Modules.{t, u} Y R)).obj V
  let η := (CochainComplex.toKInjectiveResolution.{max u (t + 1)} _).app V
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ V).2
  have : IsIso (DerivedCategory.Q.map η) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let e : Z ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso Z).symm ≪≫ asIso (DerivedCategory.Q.map η)
  have hI : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ V
  apply (cancel_mono e.hom).1
  exact representative_square_after_injective Y R a S T P Q hP hQ s.hom hs I hI e.hom

end WeilConjectures.IntegralHom
