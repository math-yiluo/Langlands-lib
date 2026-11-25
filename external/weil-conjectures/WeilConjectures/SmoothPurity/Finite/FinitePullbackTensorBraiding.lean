/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Signed total and derived braiding

Source: Stacks 06YS (K-flat resolutions), the symmetry paragraph after
06YU (definition-derived-tor), and More on Algebra 0FNG, item-flip-tensor-product.
(blueprint: def-pur-finite-pullback-tensor-braiding).
The constructions and their existing uniqueness proofs are extracted unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory
open scoped MonoidalCategory
namespace WeilConjectures

section SignedBraiding
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] Functor.map₂HomologicalComplex
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local irreducible] CochainComplex.Monoidal.braiding
  SheafOfModules.monoidalCategory PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification
universe a b
/-- The ordinary swap functor on a product category.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-braiding). -/
def pullbackTensorSwap (D : Type a) [Category.{b} D] : D × D ⥤ D × D where
  obj P := (P.2,P.1)
  map a := Prod.mkHom a.2 a.1

private theorem pullbackTensorDescend
    {B : Type a} [Category.{b} B] {D : Type (u + 2)} [Category.{u + 2} D]
    (q : B ⥤ D)
    (ff : ((Functor.whiskeringLeft (B × B) (D × D) D).obj (q.prod q)).FullyFaithful)
    (T : D × D ⥤ D) (t : B × B ⥤ D) (r : t ≅ (q.prod q) ⋙ T)
    (b : t ≅ pullbackTensorSwap B ⋙ t) :
    ∃! e : T ≅ pullbackTensorSwap D ⋙ T,
      ∀ X Y, b.hom.app (X,Y) ≫ r.hom.app (Y,X) =
        r.hom.app (X,Y) ≫ e.hom.app (q.obj X, q.obj Y) := by
  let r' : pullbackTensorSwap B ⋙ t ≅ (q.prod q) ⋙ pullbackTensorSwap D ⋙ T :=
    Functor.isoWhiskerLeft (pullbackTensorSwap B) r
  let c := r.symm ≪≫ b ≪≫ r'
  let e : T ≅ pullbackTensorSwap D ⋙ T := ff.preimageIso c
  have he : Functor.whiskerLeft (q.prod q) e.hom = c.hom := ff.map_preimage c.hom
  refine ⟨e, ?_, ?_⟩
  · intro X Y
    have hh := NatTrans.congr_app he (X,Y)
    change e.hom.app (q.obj X, q.obj Y) =
      r.inv.app (X,Y) ≫ b.hom.app (X,Y) ≫ r.hom.app (Y,X) at hh
    dsimp only [pullbackTensorSwap, Functor.comp_obj] at hh ⊢
    rw [hh]
    exact (Iso.hom_inv_id_app_assoc _ _ _).symm
  · intro a ha
    apply Iso.ext
    apply ff.map_injective
    apply NatTrans.ext
    funext X
    change a.hom.app (q.obj X.1, q.obj X.2) = e.hom.app (q.obj X.1, q.obj X.2)
    have hh := NatTrans.congr_app he X
    change e.hom.app (q.obj X.1, q.obj X.2) =
      r.inv.app X ≫ b.hom.app X ≫ r.hom.app (X.2,X.1) at hh
    dsimp only [pullbackTensorSwap, Functor.comp_obj] at hh ⊢
    rw [hh]
    apply (cancel_epi (r.hom.app X)).1
    rw [Iso.hom_inv_id_app_assoc]
    exact (ha X.1 X.2).symm

private def pullbackTensorGenericIso
    {B : Type a} [Category.{b} B] [MonoidalCategory B] [BraidedCategory B]
    (T : B × B ⥤ B) (e : ∀ X, T.obj X ≅ X.1 ⊗ X.2)
    (he : ∀ {X Y} (f : X ⟶ Y),
      T.map f ≫ (e Y).hom = (e X).hom ≫ (f.1 ⊗ₘ f.2)) :
    T ≅ pullbackTensorSwap B ⋙ T := by
  let r : T ≅ MonoidalCategory.tensor B := NatIso.ofComponents e he
  let β : MonoidalCategory.tensor B ≅
      pullbackTensorSwap B ⋙ MonoidalCategory.tensor B :=
    NatIso.ofComponents (fun X ↦ β_ X.1 X.2)
      (fun f ↦ BraidedCategory.braiding_naturality f.1 f.2)
  exact r ≪≫ β ≪≫ Functor.isoWhiskerLeft (pullbackTensorSwap B) r.symm

variable {C : Type (u + 1)} [Category.{u} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (A : Sheaf J CommRingCat.{u + 1})

private local instance pullbackTensorMonoidal : MonoidalCategory (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients A
  exact SheafOfModules.monoidalCategory A

private local instance pullbackTensorSymmetric : SymmetricCategory (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients A
  exact SheafOfModules.symmetricCategory A

private local instance pullbackTensorZero :
    (MonoidalCategory.curriedTensor (SheafOfModules.{u + 1}
      ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A

private local instance pullbackTensorZeroObj :
    ∀ M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A),
      ((MonoidalCategory.curriedTensor _).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A

private theorem pullbackTensorTotal_map
    {P P' Q Q' : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (coefficientTotalTensor.{u, u + 1, u} J A).map (Prod.mkHom f g) =
      MonoidalCategoryStruct.tensorHom f g := by
  rw [MonoidalCategory.tensorHom_def]
  rfl

private def pullbackTensorNativeIso :
    coefficientTotalTensor.{u, u + 1, u} J A ≅
      pullbackTensorSwap _ ⋙ coefficientTotalTensor.{u, u + 1, u} J A := by
  refine pullbackTensorGenericIso _ (fun _ ↦ Iso.refl _) ?_
  intro X Y f
  dsimp only [Iso.refl_hom]
  exact pullbackTensorTotal_map J A f.1 f.2

private def pullbackTensorNative
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :
    (coefficientTotalTensor.{u, u + 1, u} J A).obj (P,Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} J A).obj (Q,P) :=
  (pullbackTensorNativeIso J A).app (P,Q)

attribute [local irreducible] pullbackTensorNative pullbackTensorNativeIso

private theorem pullbackTensorSignedTotal_formula
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :
    ∀ (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      ((pullbackTensorNative J A P Q).hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} J A P Q p q k h U x y) =
      (p*q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        J A Q P q p k ((add_comm q p).trans h) U y x := by
  intro p q k h U x y
  unfold pullbackTensorNative pullbackTensorNativeIso
  dsimp only [pullbackTensorGenericIso, Iso.app, NatIso.ofComponents,
    Iso.trans, Iso.symm, Functor.isoWhiskerLeft, Iso.refl]
  exact (CategoryTheory.RingedDerivedNative.complexConstraints.{u + 1, u, u} J A).symmetry
    P Q p q k h ((add_comm q p).trans h) U x y

/-- The signed symmetry is fixed on every pure tensor by (-1)^(pq).
Source: Stacks 0FNG, section-sign-rules, item-flip-tensor-product
(blueprint: def-pur-finite-pullback-tensor-braiding).
Proof: swap the two tensor factors in each total summand and multiply by
(-1)^(pq). The two differential identities follow from the Koszul sign rule.
Swapping twice gives the identity. Tensor generators, sheafification and the
coproduct injections uniquely determine the chain map, hence the isomorphism. -/
theorem pullbackTensorSignedTotal_existsUnique
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :
    ∃! e : (coefficientTotalTensor.{u, u + 1, u} J A).obj (P,Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} J A).obj (Q,P),
      ∀ (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (e.hom.f k).val.app U (coefficientTensorGenerator.{u, u + 1, u}
          J A P Q p q k h U x y) =
        (p*q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
          J A Q P q p k ((add_comm q p).trans h) U y x := by
  let e : (coefficientTotalTensor.{u, u + 1, u} J A).obj (P,Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} J A).obj (Q,P) :=
    pullbackTensorNative J A P Q
  have he := pullbackTensorSignedTotal_formula J A P Q
  refine ⟨e, he, ?_⟩
  · intro b hb
    apply Iso.ext
    apply HomologicalComplex.Hom.ext
    funext k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (P.X p) (Q.X q)).inv).1
    apply (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).homEquiv _ _ |>.injective
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact (hb p q k hpq U x y).trans (he p q k hpq U x y).symm

/-- The chain-level Koszul braiding, including its prescribed sign.
Source: Stacks 0FNG, section-sign-rules, item-flip-tensor-product
(blueprint: def-pur-finite-pullback-tensor-braiding). -/
def pullbackTensorSignedTotal
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :=
  (pullbackTensorSignedTotal_existsUnique J A P Q).exists.choose

private theorem pullbackTensorSignedTotal_eq
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :
    pullbackTensorSignedTotal J A P Q =
      pullbackTensorNative J A P Q := by
  exact (pullbackTensorSignedTotal_existsUnique J A P Q).unique
    (pullbackTensorSignedTotal_existsUnique J A P Q).exists.choose_spec
    (pullbackTensorSignedTotal_formula J A P Q)

attribute [local irreducible] pullbackTensorSignedTotal coefficientTotalTensor

variable [EssentiallySmall.{u + 1} C]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u + 1, u, u, u + 2} J A))
  (T : CoefficientTensorModels.{u, u + 1, u, u + 2} J A S)

/-- The derived braiding is the descent of the signed total symmetry, fixed on
the full K-flat representative comparison.
Source: Stacks 06YS and 06YU (blueprint: def-pur-finite-pullback-tensor-braiding).
Proof: the generator formula is natural in both cochain inputs and preserves
quasi-isomorphisms between K-flat pairs. Localize that natural isomorphism.
The displayed representative square fixes every component by K-flat resolution
and hence gives uniqueness. -/
theorem pullbackTensorBraiding_existsUnique :
    ∃! e : S.tensor ≅ pullbackTensorSwap _ ⋙ S.tensor,
      ∀ (P Q : CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := J) (R := A) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := J) (R := A) Q),
        DerivedCategory.Q.map (pullbackTensorSignedTotal J A P Q).hom ≫
          (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} J A S T Q P hQ hP).hom =
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} J A S T P Q hP hQ).hom ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  let K := CochainComplex (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ
  let D := DerivedCategory (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
  let P : ObjectProperty K :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A)
  let H : ObjectProperty (HomotopyCategory _ (.up ℤ)) := fun X ↦ P X.as
  have hres : ∀ X : HomotopyCategory _ (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X),
        HomotopyCategory.quasiIso _ (.up ℤ) f := by
    intro X
    obtain ⟨Y, f, hY, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj Y, hY⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  have hff := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
      (K := K) (D := D) D
      (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
      (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh P H
      (fun _ ↦ Iff.rfl) hres
  let ff := Classical.choice hff
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ D).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))))
  let b : (P.ι.prod P.ι) ⋙ coefficientTotalTensor.{u, u + 1, u} J A ⋙ DerivedCategory.Q ≅
      (P.ι.prod P.ι) ⋙ pullbackTensorSwap K ⋙
        coefficientTotalTensor.{u, u + 1, u} J A ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (P.ι.prod P.ι)
      (Functor.isoWhiskerRight (pullbackTensorNativeIso J A) DerivedCategory.Q)
  obtain ⟨e, he, hu⟩ := pullbackTensorDescend (P.ι ⋙ DerivedCategory.Q) ff'
    S.tensor _ T.comparison b
  refine ⟨e, ?_, ?_⟩
  · intro U V hU hV
    rw [pullbackTensorSignedTotal_eq]
    unfold pullbackTensorNative
    exact he ⟨U, hU⟩ ⟨V, hV⟩
  · intro a ha
    apply hu a
    intro U V
    have h := ha U.obj V.obj U.property V.property
    rw [pullbackTensorSignedTotal_eq] at h
    unfold pullbackTensorNative at h
    exact h

/-- The signed derived braiding prescribed by the recorded tensor models.
Source: Stacks 06YS and 06YU (blueprint: def-pur-finite-pullback-tensor-braiding). -/
def pullbackTensorBraiding :=
  (pullbackTensorBraiding_existsUnique J A S T).exists.choose
end SignedBraiding

attribute [local irreducible] pullbackTensorBraiding pullbackTensorSignedTotal
  coefficientTotalTensor

end WeilConjectures
