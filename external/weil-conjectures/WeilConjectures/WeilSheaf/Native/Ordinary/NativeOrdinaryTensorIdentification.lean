/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory

import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.DerivedHom
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.Algebra.Homology.BifunctorHomCone
import all WeilConjectures.Algebra.Homology.BifunctorHomComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive

/-! # Identifying the native ordinary closed tensor

Source: Stacks Tags 06YS and 08J9, uniqueness of derived tensor-Hom adjoints.
(blueprint: lem-sf-native-ordinary-tensor-identification).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures

namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem nativeHomTransport_right
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasCountableProducts C] [HasCountableProducts D]
    (U : C ⥤ D) [U.Additive]
    [∀ n : ℤ, PreservesLimitsOfShape (Discrete (CochainComplex.HomComplex.Triplet n)) U]
    (HC : Cᵒᵖ ⥤ C ⥤ C) [HC.Additive] [∀ M, (HC.obj M).Additive]
    (HD : Dᵒᵖ ⥤ D ⥤ D) [HD.Additive] [∀ M, (HD.obj M).Additive]
    (e : ∀ M N, U.obj ((HC.obj (op M)).obj N) ≅
      (HD.obj (op (U.obj M))).obj (U.obj N))
    (er : ∀ M N N' (f : N ⟶ N'), U.map ((HC.obj (op M)).map f) ≫ (e M N').hom =
      (e M N).hom ≫ (HD.obj (op (U.obj M))).map (U.map f))
    (el : ∀ M M' N (f : M' ⟶ M), U.map ((HC.map f.op).app N) ≫ (e M' N).hom =
      (e M N).hom ≫ (HD.map (U.map f).op).app (U.obj N))
    {K I I' : CochainComplex C ℤ} (a : I ⟶ I') :
    (U.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.bifunctorHomMapRight (H := HC) (K := K) a) ≫
      (PrecompositionTransport.complexIso U HC HD e er el K I').hom =
    (PrecompositionTransport.complexIso U HC HD e er el K I).hom ≫
      CochainComplex.bifunctorHomMapRight (H := HD)
        (K := (U.mapHomologicalComplex (.up ℤ)).obj K)
        ((U.mapHomologicalComplex (.up ℤ)).map a) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply CochainComplex.bifunctorHomObj_hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Category.assoc]
  change U.map ((CochainComplex.bifunctorHomMapRight (H := HC) (K := K) a).f n) ≫
      (PrecompositionTransport.component U HC HD e K I' n).hom ≫ _ =
    (PrecompositionTransport.component U HC HD e K I n).hom ≫
      (CochainComplex.bifunctorHomMapRight (H := HD)
        (K := (U.mapHomologicalComplex (.up ℤ)).obj K)
        ((U.mapHomologicalComplex (.up ℤ)).map a)).f n ≫ _
  rw [PrecompositionTransport.component_π, CochainComplex.bifunctorHomMapRight_f_π,
    PrecompositionTransport.component_π_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc,
    CochainComplex.bifunctorHomMapRight_f_π, CategoryTheory.Functor.map_comp,
    Category.assoc, er]
  rfl

namespace OrdinaryModuleHom
universe a b
variable {C : Type a} [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{b} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

local instance : HasLimitsOfSize.{b, b} C := inferInstance
local instance : HasColimitsOfSize.{b, b} C := inferInstance
local instance : HasLimitsOfSize.{b, b} (Mod C R) := inferInstance
local instance : HasColimitsOfSize.{b, b} (Mod C R) := inferInstance

private noncomputable def tensorRightIso (M : Mod C R) :
    Mod.tensorLeft M ≅ MonoidalCategory.tensorRight M := PrecompositionAux.tensorIso M

omit [MonoidalPreadditive C] in
private theorem tensorRightIso_naturality {M N : Mod C R} (f : M ⟶ N) :
    Mod.tensorLeftMap f ≫ (tensorRightIso N).hom =
      (tensorRightIso M).hom ≫ (tensoringRight _).map f := by
  apply NatTrans.ext
  funext P
  apply Mod.tensorLeft_obj_hom_ext
  simp only [NatTrans.comp_app, Mod.comp_hom']
  rw [Mod.tensorπ_tensorLeftMap_assoc]
  change P.X ◁ f.hom ≫ Mod.tensorπ P N ≫ (PrecompositionAux.tensorComponent P N).hom.hom = _
  rw [PrecompositionAux.tensorComponent_π]
  change _ = Mod.tensorπ P M ≫ (PrecompositionAux.tensorComponent P M).hom.hom ≫ (P ◁ f).hom
  rw [← Category.assoc, PrecompositionAux.tensorComponent_π]
  exact (Mod.tensorObjπ_whiskerLeft f).symm

private noncomputable def tensorLeftIso (M : Mod C R) :
    MonoidalCategory.tensorLeft M ≅ Mod.tensorLeft M :=
  BraidedCategory.tensorLeftIsoTensorRight M ≪≫ (tensorRightIso M).symm

omit [MonoidalPreadditive C] in
private theorem tensorLeftIso_naturality {M N : Mod C R} (f : M ⟶ N) :
    (tensorLeftIso M).hom ≫ Mod.tensorLeftMap f =
      (tensoringLeft _).map f ≫ (tensorLeftIso N).hom := by
  apply (cancel_mono (tensorRightIso N).hom).1
  rw [Category.assoc, tensorRightIso_naturality]
  simp only [tensorLeftIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply NatTrans.ext
  funext P
  exact (BraidedCategory.braiding_naturality_left f P).symm

private noncomputable def ihomIso (M : Mod C R) :
    Mod.ihom M ≅ CategoryTheory.ihom M :=
  conjugateIsoEquiv (Mod.ihomAdjunction M) (CategoryTheory.ihom.adjunction M)
    (tensorLeftIso M)

private theorem ihomIso_naturality {M N : Mod C R} (f : M ⟶ N) :
    Mod.ihomMap f ≫ (ihomIso M).hom =
      (ihomIso N).hom ≫ MonoidalClosed.pre f := by
  change conjugateEquiv (Mod.ihomAdjunction N) (Mod.ihomAdjunction M)
      (Mod.tensorLeftMap f) ≫
      conjugateEquiv (Mod.ihomAdjunction M) (CategoryTheory.ihom.adjunction M)
        (tensorLeftIso M).hom =
    conjugateEquiv (Mod.ihomAdjunction N) (CategoryTheory.ihom.adjunction N)
      (tensorLeftIso N).hom ≫
      conjugateEquiv (CategoryTheory.ihom.adjunction N) (CategoryTheory.ihom.adjunction M)
        ((tensoringLeft _).map f)
  rw [conjugateEquiv_comp, conjugateEquiv_comp, tensorLeftIso_naturality]

end OrdinaryModuleHom

namespace TensorModelComparison

universe a b
variable {A : Type a} [Category.{b} A] [Abelian A] [IsGrothendieckAbelian.{b} A]
  [HasDerivedCategory.{b} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [SymmetricCategory A] [Abelian.HasFunctorialFlatResolution A]
  [HasColimitsOfSize.{0, 0} A]

local instance : HasLimitsOfSize.{b, b} A := inferInstance
local instance : HasColimitsOfSize.{b, b} A := inferInstance
local instance : HasCountableProducts A := inferInstance
local instance : HasCountableCoproducts A := inferInstance

private instance canonicalInternalHom_additive :
    (MonoidalClosed.internalHom (C := A)).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    change (MonoidalClosed.pre (f.unop + g.unop)).app Z =
      (MonoidalClosed.pre f.unop).app Z + (MonoidalClosed.pre g.unop).app Z
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_pre, MonoidalClosed.uncurry_add,
      MonoidalClosed.uncurry_pre, MonoidalClosed.uncurry_pre,
      MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

private instance canonicalInternalHom_obj_additive (M : Aᵒᵖ) :
    (MonoidalClosed.internalHom.obj M).Additive :=
  inferInstanceAs (CategoryTheory.ihom M.unop).Additive

variable (HC : Aᵒᵖ ⥤ A ⥤ A) [HC.Additive] [∀ M, (HC.obj M).Additive]
  (e : ∀ M : A, HC.obj (op M) ≅ MonoidalClosed.internalHom.obj (op M))
  (el : ∀ {M N : A} (f : M ⟶ N), HC.map f.op ≫ (e M).hom =
    (e N).hom ≫ MonoidalClosed.pre f)

private noncomputable def complexIso (P I : CochainComplex A ℤ) :
    CochainComplex.bifunctorHomObj HC P I ≅ CochainComplex.internalHomObj P I :=
  PrecompositionTransport.complexIso (𝟭 _) HC MonoidalClosed.internalHom
    (fun M N ↦ (e M).app N)
    (fun M _N _N' f ↦ (e M).hom.naturality f)
    (fun _M _M' N f ↦ NatTrans.congr_app (el f) N) P I

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [HasColimitsOfSize.{0, 0} A] in
private theorem canonicalHomMap (P : CochainComplex A ℤ)
    {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := MonoidalClosed.internalHom) (K := P) f =
      (CochainComplex.internalHom P).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply CochainComplex.internalHomObj_hom_ext
  intro p q hpq
  change (CochainComplex.bifunctorHomMapRight
    (H := MonoidalClosed.internalHom) (K := P) f).f n ≫
      CochainComplex.bifunctorHomπ MonoidalClosed.internalHom P I' n p q hpq = _
  rw [CochainComplex.bifunctorHomMapRight_f_π, CochainComplex.internalHom_map_f_π]
  rfl

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [HasColimitsOfSize.{0, 0} A] in
private theorem complexIso_naturality (P : CochainComplex A ℤ)
    {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := HC) (K := P) f ≫
      (complexIso HC e el P I').hom =
    (complexIso HC e el P I).hom ≫ (CochainComplex.internalHom P).map f := by
  have h := nativeHomTransport_right (𝟭 A) HC MonoidalClosed.internalHom
    (fun M N ↦ (e M).app N)
    (fun M _N _N' f ↦ (e M).hom.naturality f)
    (fun _M _M' N f ↦ NatTrans.congr_app (el f) N) (K := P) f
  change CochainComplex.bifunctorHomMapRight f ≫ (complexIso HC e el P I').hom =
    (complexIso HC e el P I).hom ≫
      CochainComplex.bifunctorHomMapRight (H := MonoidalClosed.internalHom) (K := P) f at h
  rw [canonicalHomMap] at h
  exact h

private noncomputable def homFunctor (P : CochainComplex A ℤ) :
    CochainComplex A ℤ ⥤ CochainComplex A ℤ where
  obj I := CochainComplex.bifunctorHomObj HC P I
  map f := CochainComplex.bifunctorHomMapRight f
  map_id _I := CochainComplex.bifunctorHomMapRight_id
  map_comp f g := CochainComplex.bifunctorHomMapRight_comp f g

private noncomputable def homFunctorIso (P : CochainComplex A ℤ) :
    homFunctor HC P ≅ CochainComplex.internalHom P :=
  NatIso.ofComponents (complexIso HC e el P)
    (fun f ↦ complexIso_naturality HC e el P f)

private noncomputable def homComparison (P : CochainComplex A ℤ) :
    CochainComplex.internalHom P ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ DerivedCategory.internalHomQhObj
        ((HomotopyCategory.quotient _ _).obj P) :=
  (Functor.isoWhiskerLeft (CochainComplex.internalHom P)
    (DerivedCategory.quotientCompQhIso _)).inv ≫
  (Functor.isoWhiskerRight (HomotopyCategory.quotientCompInternalHomIso
    ((HomotopyCategory.quotient _ _).obj P)).symm DerivedCategory.Qh).hom ≫
  Functor.whiskerLeft (HomotopyCategory.quotient _ _)
    (DerivedCategory.internalHomQhObjUnit ((HomotopyCategory.quotient _ _).obj P)) ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
    (DerivedCategory.internalHomQhObj ((HomotopyCategory.quotient _ _).obj P))).hom

omit [Abelian.HasFunctorialFlatResolution A] [HasColimitsOfSize.{0, 0} A] in
private theorem isIso_homComparison (P I : CochainComplex A ℤ)
    [I.IsKInjective] : IsIso ((homComparison P).app I) := by
  dsimp only [homComparison, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

include e el in
private theorem tensorRightIso
    (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives HC H) (S : CoefficientClosedStructure H)
    (P : DerivedCategory A) :
    Nonempty (@MonoidalCategory.tensorRight _ _ S.monoidal P ≅
      MonoidalCategory.tensorRight P) := by
  classical
  let K := DerivedCategory.Q.objPreimage P
  let Kh := (HomotopyCategory.quotient A (.up ℤ)).obj K
  let p : DerivedCategory.Q.obj K ≅ P := DerivedCategory.Q.objObjPreimageIso P
  let T := Prod.sectR (op (DerivedCategory.Q.obj K)) (DerivedCategory A) ⋙ H
  let G := DerivedCategory.internalHomQhObj Kh
  let i : CochainComplex.KInjectives A ⥤ CochainComplex A ℤ :=
    CochainComplex.KInjectives.ι
  let L := i ⋙ DerivedCategory.Q
  let a : L ⋙ T ≅ i ⋙ homFunctor HC K ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun I ↦ R.model K I.obj I.property) (by
      intro I I' f
      change H.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map f.hom)) ≫ _ =
        _ ≫ DerivedCategory.Q.map
          (CochainComplex.bifunctorHomMapRight (H := HC) (K := K) f.hom)
      have hn := R.naturality K K I.obj I'.obj I.property I'.property (𝟙 K) f.hom
      rw [CategoryTheory.Functor.map_id, op_id, CochainComplex.bifunctorHomMapLeft_id,
        Category.id_comp] at hn
      exact hn)
  let b : i ⋙ homFunctor HC K ⋙ DerivedCategory.Q ≅
      i ⋙ CochainComplex.internalHom K ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft i (Functor.isoWhiskerRight
      (homFunctorIso HC e el K) DerivedCategory.Q)
  have hc (I : CochainComplex.KInjectives A) :
      IsIso ((homComparison K).app I.obj) := by
    have := I.property
    exact isIso_homComparison K I.obj
  let d : i ⋙ CochainComplex.internalHom K ⋙ DerivedCategory.Q ⟶ L ⋙ G :=
    Functor.whiskerLeft i (homComparison K)
  have (I : CochainComplex.KInjectives A) : IsIso (d.app I) := hc I
  have : IsIso d := NatIso.isIso_of_isIso_app d
  let c : i ⋙ CochainComplex.internalHom K ⋙ DerivedCategory.Q ≅ L ⋙ G := asIso d
  let h : T ≅ G :=
    (Localization.fullyFaithfulWhiskeringLeft L
      (CochainComplex.KInjectives.quasiIso A) (DerivedCategory A)).preimageIso (a ≪≫ b ≪≫ c)
  let : BraidedCategory (DerivedCategory A) :=
    (DerivedCategory.nonempty_braidedCategory A).some
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft X)
      (NatIso.ofComponents (fun Z ↦ β_ X Z) (by intros; simp [curriedTensor]))
  let adj : MonoidalCategory.tensorRight (DerivedCategory.Q.obj K) ⊣ T :=
    ((DerivedCategory.tensorHomAdjunctionQhObj Kh).ofNatIsoLeft
      ((tensoringLeft _).mapIso ((DerivedCategory.quotientCompQhIso A).app K) ≪≫
        BraidedCategory.tensorLeftIsoTensorRight (DerivedCategory.Q.obj K))).ofNatIsoRight
      h.symm
  let t := (S.adjunction (DerivedCategory.Q.obj K)).leftAdjointUniq adj
  let s : @MonoidalCategory.tensorRight _ _ S.monoidal P ≅
      @MonoidalCategory.tensorRight _ _ S.monoidal (DerivedCategory.Q.obj K) := by
    letI := S.monoidal
    exact (tensoringRight _).mapIso p.symm
  exact ⟨s ≪≫ t ≪≫ (tensoringRight _).mapIso p⟩

end TensorModelComparison

/-- The representative internal Hom determines its tensor right functors.
This assertion is internal to the native module category and involves no change
of coefficients or forgetting of ambient scalars.

Source: Stacks Tags 06YS, 08J9 and 0A97; step 2 of
lem-sf-native-coefficient-tensor-comparison.
(blueprint: lem-sf-native-ordinary-tensor-identification).

Proof: For a fixed source complex, the product-total ordinary internal Hom into
K-injectives computes the right adjoint of total relative tensor. The ordinary
Mod.tensorLeft and the standard module-object tensor both represent balanced
bilinear maps, hence their right adjoints are naturally isomorphic. Apply this
comparison in each degree and take products to identify the two Hom complexes.
The naturality field of R identifies H with this derived right adjoint: first
on K-injective targets using R.model, then on all derived targets by K-injective
replacement and localization. Replacing a source by a quasi-isomorphic K-flat
complex computes the standard derived tensor and extends its adjunction to
unbounded inputs. S.adjunction has precisely the same right adjoint. Uniqueness
of left adjoints gives the asserted natural isomorphism. Zero complexes and the
empty scheme require no exception; no boundedness assumption is used. -/
theorem nativeOrdinary_tensorRight_iso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
        DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H) (P : DerivedCategory (ProEtale.AdicSheaf l Y)) :
    Nonempty (@MonoidalCategory.tensorRight _ _ S.monoidal P ≅
      MonoidalCategory.tensorRight P) := by
  exact TensorModelComparison.tensorRightIso (ordinaryIhomBifunctor l Y)
    OrdinaryModuleHom.ihomIso (fun f ↦ OrdinaryModuleHom.ihomIso_naturality f) H R S P

end AlgebraicGeometry.ProEtaleWeilSheaf
