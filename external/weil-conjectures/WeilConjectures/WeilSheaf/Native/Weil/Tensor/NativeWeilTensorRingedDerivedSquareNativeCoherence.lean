/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorRepresentatives
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnitSymmetryRepresentatives
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelNaturality
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Coherence component of the native ringed derived square

Source: Stacks 06YU, 0FPT; blueprint step 3 of
`lem-sf-native-weil-tensor-ringed-derived-square-native-data`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
section Transport

variable {B : Type*} [Category B] {A : Type*} [Category A]
  (mB : MonoidalCategory B) (mA : MonoidalCategory A)
  (F : B ⥤ A) (μ : @MonoidalCategory.tensor B _ mB ⋙ F ≅
    (F.prod F) ⋙ @MonoidalCategory.tensor A _ mA)

private def rho (X Y : B) :
    F.obj ((@MonoidalCategory.tensor B _ mB).obj (X, Y)) ≅
      (@MonoidalCategory.tensor A _ mA).obj (F.obj X, F.obj Y) :=
  μ.app (X, Y)

private theorem rho_naturality (X Y X' Y' : B) (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map ((@MonoidalCategory.tensor B _ mB).map (f, g)) ≫ (rho mB mA F μ X' Y').hom =
      (rho mB mA F μ X Y).hom ≫ (@MonoidalCategory.tensor A _ mA).map (F.map f, F.map g) :=
  μ.hom.naturality (X := (X, Y)) (Y := (X', Y')) (f, g)

private theorem associator_of_iso
    {P Q N L M V : B} (e : P ≅ L) (e' : Q ≅ M) (e'' : N ≅ V)
    (h : F.map (mB.associator P Q N).hom ≫
      (rho mB mA F μ P ((@MonoidalCategory.tensor B _ mB).obj (Q, N))).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj P, F.obj ((@MonoidalCategory.tensor B _ mB).obj (Q, N))))
        (Y := (F.obj P, (@MonoidalCategory.tensor A _ mA).obj (F.obj Q, F.obj N)))
        (𝟙 (F.obj P), (rho mB mA F μ Q N).hom) =
      (rho mB mA F μ ((@MonoidalCategory.tensor B _ mB).obj (P, Q)) N).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj ((@MonoidalCategory.tensor B _ mB).obj (P, Q)), F.obj N))
        (Y := ((@MonoidalCategory.tensor A _ mA).obj (F.obj P, F.obj Q), F.obj N))
        ((rho mB mA F μ P Q).hom, 𝟙 (F.obj N)) ≫
      (mA.associator (F.obj P) (F.obj Q) (F.obj N)).hom) :
    F.map (mB.associator L M V).hom ≫
      (rho mB mA F μ L ((@MonoidalCategory.tensor B _ mB).obj (M, V))).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj L, F.obj ((@MonoidalCategory.tensor B _ mB).obj (M, V))))
        (Y := (F.obj L, (@MonoidalCategory.tensor A _ mA).obj (F.obj M, F.obj V)))
        (𝟙 (F.obj L), (rho mB mA F μ M V).hom) =
      (rho mB mA F μ ((@MonoidalCategory.tensor B _ mB).obj (L, M)) V).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj ((@MonoidalCategory.tensor B _ mB).obj (L, M)), F.obj V))
        (Y := ((@MonoidalCategory.tensor A _ mA).obj (F.obj L, F.obj M), F.obj V))
        ((rho mB mA F μ L M).hom, 𝟙 (F.obj V)) ≫
      (mA.associator (F.obj L) (F.obj M) (F.obj V)).hom := by
  let := mB
  let := mA
  let F₁ := (leftAssocTensor B) ⋙ F
  let F₂ := (rightAssocTensor B) ⋙ F
  let G₁ := (F.prod (F.prod F)) ⋙ leftAssocTensor A
  let G₂ := (F.prod (F.prod F)) ⋙ rightAssocTensor A
  let α : F₁ ⟶ F₂ := Functor.whiskerRight (associatorNatIso B).hom F
  let β : G₁ ⟶ G₂ := Functor.whiskerLeft (F.prod (F.prod F)) (associatorNatIso A).hom
  let c₁ : F₁ ⟶ G₁ :=
    { app := fun X ↦ (rho mB mA F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
        (rho mB mA F μ X.1 X.2.1).hom ▷ F.obj X.2.2
      naturality := by
        intro X Y f
        have h₁ := rho_naturality mB mA F μ (X.1 ⊗ X.2.1) X.2.2
          (Y.1 ⊗ Y.2.1) Y.2.2 (f.1 ⊗ₘ f.2.1) f.2.2
        have h₂ := rho_naturality mB mA F μ X.1 X.2.1 Y.1 Y.2.1 f.1 f.2.1
        simp only [tensor_map] at h₁ h₂
        change F.map ((f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2) ≫ _ = _
        rw [reassoc_of% h₁]
        change (rho mB mA F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
            (F.map (f.1 ⊗ₘ f.2.1) ⊗ₘ F.map f.2.2) ≫
              (rho mB mA F μ Y.1 Y.2.1).hom ▷ F.obj Y.2.2 = _
        simp only [← tensorHom_id, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₁, Functor.comp_map, Functor.prod_map,
          leftAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let c₂ : F₂ ⟶ G₂ :=
    { app := fun X ↦ (rho mB mA F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
        F.obj X.1 ◁ (rho mB mA F μ X.2.1 X.2.2).hom
      naturality := by
        intro X Y f
        have h₁ := rho_naturality mB mA F μ X.1 (X.2.1 ⊗ X.2.2)
          Y.1 (Y.2.1 ⊗ Y.2.2) f.1 (f.2.1 ⊗ₘ f.2.2)
        have h₂ := rho_naturality mB mA F μ X.2.1 X.2.2 Y.2.1 Y.2.2 f.2.1 f.2.2
        simp only [tensor_map] at h₁ h₂
        change F.map (f.1 ⊗ₘ (f.2.1 ⊗ₘ f.2.2)) ≫ _ = _
        rw [reassoc_of% h₁]
        change (rho mB mA F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
            (F.map f.1 ⊗ₘ F.map (f.2.1 ⊗ₘ f.2.2)) ≫
              F.obj Y.1 ◁ (rho mB mA F μ Y.2.1 Y.2.2).hom = _
        simp only [← id_tensorHom, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₂, Functor.comp_map, Functor.prod_map,
          rightAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let z : (P, Q, N) ≅ (L, M, V) := e.prod (e'.prod e'')
  have hz : IsIso (F₁.map z.hom) := inferInstance
  apply (cancel_epi (F₁.map z.hom)).mp
  have hh : (α ≫ c₂).app (P, Q, N) = (c₁ ≫ β).app (P, Q, N) := by
    simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      tensor_map,
      id_tensorHom, tensorHom_id, Category.assoc] using h
  have hh' := congrArg (fun f ↦ f ≫ G₂.map z.hom) hh
  rw [← (α ≫ c₂).naturality, ← (c₁ ≫ β).naturality] at hh'
  simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      tensor_map,
    id_tensorHom, tensorHom_id, Category.assoc] using hh'

private theorem left_unit_of_iso
    (η : F.obj mB.tensorUnit ≅ mA.tensorUnit)
    {X Y : B} (e : X ≅ Y)
    (h : μ.hom.app (mB.tensorUnit, X) ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj mB.tensorUnit, F.obj X))
        (Y := (mA.tensorUnit, F.obj X)) (η.hom, 𝟙 _) ≫
          (mA.leftUnitor (F.obj X)).hom =
        F.map (mB.leftUnitor X).hom) :
    μ.hom.app (mB.tensorUnit, Y) ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj mB.tensorUnit, F.obj Y))
        (Y := (mA.tensorUnit, F.obj Y)) (η.hom, 𝟙 _) ≫
          (mA.leftUnitor (F.obj Y)).hom =
        F.map (mB.leftUnitor Y).hom := by
  let := mB
  let := mA
  apply (cancel_epi (F.map (𝟙_ B ◁ e.hom))).mp
  have hn := rho_naturality mB mA F μ (𝟙_ B) X (𝟙_ B) Y (𝟙 _) e.hom
  simp only [rho, tensor_map,
    id_tensorHom] at hn
  simp only [tensor_map, tensorHom_id]
  change F.map (𝟙_ B ◁ e.hom) ≫ μ.hom.app (𝟙_ B, Y) ≫
    η.hom ▷ F.obj Y ≫ (λ_ (F.obj Y)).hom =
      F.map (𝟙_ B ◁ e.hom) ≫ F.map (λ_ Y).hom
  erw [reassoc_of% hn]
  simp only [F.map_id, id_tensorHom]
  have ht : F.obj (𝟙_ B) ◁ F.map e.hom ≫ η.hom ▷ F.obj Y =
      η.hom ▷ F.obj X ≫ 𝟙_ A ◁ F.map e.hom := by
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  rw [reassoc_of% ht, MonoidalCategory.leftUnitor_naturality]
  have hh : μ.hom.app (𝟙_ B, X) ≫ η.hom ▷ F.obj X ≫ (λ_ (F.obj X)).hom =
      F.map (λ_ X).hom := by
    simpa only [tensor_map, tensorHom_id] using h
  rw [← F.map_comp, MonoidalCategory.leftUnitor_naturality, F.map_comp]
  simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj,
    tensor_obj] using
      congrArg (fun f ↦ f ≫ F.map e.hom) hh

private theorem right_unit_of_iso
    (η : F.obj mB.tensorUnit ≅ mA.tensorUnit)
    {X Y : B} (e : X ≅ Y)
    (h : μ.hom.app (X, mB.tensorUnit) ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj X, F.obj mB.tensorUnit))
        (Y := (F.obj X, mA.tensorUnit)) (𝟙 _, η.hom) ≫
          (mA.rightUnitor (F.obj X)).hom =
        F.map (mB.rightUnitor X).hom) :
    μ.hom.app (Y, mB.tensorUnit) ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj Y, F.obj mB.tensorUnit))
        (Y := (F.obj Y, mA.tensorUnit)) (𝟙 _, η.hom) ≫
          (mA.rightUnitor (F.obj Y)).hom =
        F.map (mB.rightUnitor Y).hom := by
  let := mB
  let := mA
  apply (cancel_epi (F.map (e.hom ▷ 𝟙_ B))).mp
  have hn := rho_naturality mB mA F μ X (𝟙_ B) Y (𝟙_ B) e.hom (𝟙 _)
  simp only [rho, tensor_map,
    tensorHom_id] at hn
  simp only [tensor_map, id_tensorHom]
  change F.map (e.hom ▷ 𝟙_ B) ≫ μ.hom.app (Y, 𝟙_ B) ≫
    F.obj Y ◁ η.hom ≫ (ρ_ (F.obj Y)).hom =
      F.map (e.hom ▷ 𝟙_ B) ≫ F.map (ρ_ Y).hom
  erw [reassoc_of% hn]
  simp only [F.map_id, tensorHom_id]
  have ht : F.map e.hom ▷ F.obj (𝟙_ B) ≫ F.obj Y ◁ η.hom =
      F.obj X ◁ η.hom ≫ F.map e.hom ▷ 𝟙_ A := by
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  rw [reassoc_of% ht, MonoidalCategory.rightUnitor_naturality]
  have hh : μ.hom.app (X, 𝟙_ B) ≫ F.obj X ◁ η.hom ≫ (ρ_ (F.obj X)).hom =
      F.map (ρ_ X).hom := by
    simpa only [tensor_map, id_tensorHom] using h
  rw [← F.map_comp, MonoidalCategory.rightUnitor_naturality, F.map_comp]
  simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj,
    tensor_obj] using
      congrArg (fun f ↦ f ≫ F.map e.hom) hh

private theorem symmetry_of_iso
    (β : @SymmetricCategory B _ mB)
    (β' : @SymmetricCategory A _ mA)
    {X Y X' Y' : B} (e : X ≅ X') (e' : Y ≅ Y')
    (h : F.map (β.toBraidedCategory.braiding X Y).hom ≫ μ.hom.app (Y, X) =
      μ.hom.app (X, Y) ≫ (β'.toBraidedCategory.braiding (F.obj X) (F.obj Y)).hom) :
    F.map (β.toBraidedCategory.braiding X' Y').hom ≫ μ.hom.app (Y', X') =
      μ.hom.app (X', Y') ≫
        (β'.toBraidedCategory.braiding (F.obj X') (F.obj Y')).hom := by
  let := mB
  let := mA
  let : SymmetricCategory B := β
  let : SymmetricCategory A := β'
  apply (cancel_epi (F.map (e.hom ⊗ₘ e'.hom))).mp
  change F.map (e.hom ⊗ₘ e'.hom) ≫ F.map (β_ X' Y').hom ≫ _ =
    F.map (e.hom ⊗ₘ e'.hom) ≫ μ.hom.app (X', Y') ≫ (β_ _ _).hom
  rw [← Functor.map_comp_assoc, BraidedCategory.braiding_naturality,
    Functor.map_comp, Category.assoc]
  have hn := rho_naturality mB mA F μ Y X Y' X' e'.hom e.hom
  have hn' := rho_naturality mB mA F μ X Y X' Y' e.hom e'.hom
  simp only [rho, tensor_map] at hn hn'
  simp only [Functor.prod_obj]
  erw [hn, reassoc_of% hn', ← Category.assoc, h, Category.assoc,
    BraidedCategory.braiding_naturality]
  rfl

/-- Coherence equations descend along an essentially surjective functor. -/
private theorem coherence_of_representatives
    {C : Type*} [Category C] (q : C ⥤ B) [q.EssSurj]
    (βB : @SymmetricCategory B _ mB) (βA : @SymmetricCategory A _ mA)
    (η : F.obj mB.tensorUnit ≅ mA.tensorUnit)
    (ha : ∀ P Q N : C,
      F.map (mB.associator (q.obj P) (q.obj Q) (q.obj N)).hom ≫
      (rho mB mA F μ (q.obj P)
        ((@MonoidalCategory.tensor B _ mB).obj (q.obj Q, q.obj N))).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj (q.obj P),
          F.obj ((@MonoidalCategory.tensor B _ mB).obj (q.obj Q, q.obj N))))
        (Y := (F.obj (q.obj P),
          (@MonoidalCategory.tensor A _ mA).obj (F.obj (q.obj Q), F.obj (q.obj N))))
        (𝟙 (F.obj (q.obj P)), (rho mB mA F μ (q.obj Q) (q.obj N)).hom) =
      (rho mB mA F μ ((@MonoidalCategory.tensor B _ mB).obj ((q.obj P), (q.obj Q))) (q.obj N)).hom ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj ((@MonoidalCategory.tensor B _ mB).obj (q.obj P, q.obj Q)),
          F.obj (q.obj N)))
        (Y := ((@MonoidalCategory.tensor A _ mA).obj (F.obj (q.obj P), F.obj (q.obj Q)),
          F.obj (q.obj N)))
        ((rho mB mA F μ (q.obj P) (q.obj Q)).hom, 𝟙 (F.obj (q.obj N))) ≫
      (mA.associator (F.obj (q.obj P)) (F.obj (q.obj Q)) (F.obj (q.obj N))).hom)
    (hu : ∀ P : C,
      (μ.hom.app (mB.tensorUnit, (q.obj P)) ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj mB.tensorUnit, F.obj (q.obj P)))
        (Y := (mA.tensorUnit, F.obj (q.obj P))) (η.hom, 𝟙 _) ≫
          (mA.leftUnitor (F.obj (q.obj P))).hom =
        F.map (mB.leftUnitor (q.obj P)).hom) ∧
      (μ.hom.app ((q.obj P), mB.tensorUnit) ≫
      (@MonoidalCategory.tensor A _ mA).map
        (X := (F.obj (q.obj P), F.obj mB.tensorUnit))
        (Y := (F.obj (q.obj P), mA.tensorUnit)) (𝟙 _, η.hom) ≫
          (mA.rightUnitor (F.obj (q.obj P))).hom =
        F.map (mB.rightUnitor (q.obj P)).hom))
    (hs : ∀ P Q : C,
      F.map (βB.toBraidedCategory.braiding (q.obj P) (q.obj Q)).hom ≫
        μ.hom.app (q.obj Q, q.obj P) =
      μ.hom.app (q.obj P, q.obj Q) ≫
        (βA.toBraidedCategory.braiding (F.obj (q.obj P)) (F.obj (q.obj Q))).hom) :
    Nonempty (RingedForgetTensorTransposition.TensorCoherence mB mA βB βA F μ) := by
  refine ⟨{
    unit := η
    associativity := ?_
    left_unit := ?_
    right_unit := ?_
    symmetry := ?_ }⟩
  · intro X Y Z
    exact associator_of_iso mB mA F μ (q.objObjPreimageIso X)
      (q.objObjPreimageIso Y) (q.objObjPreimageIso Z)
      (ha (q.objPreimage X) (q.objPreimage Y) (q.objPreimage Z))
  · intro X
    exact left_unit_of_iso mB mA F μ η (q.objObjPreimageIso X)
      (hu (q.objPreimage X)).1
  · intro X
    exact right_unit_of_iso mB mA F μ η (q.objObjPreimageIso X)
      (hu (q.objPreimage X)).2
  · intro X Y
    exact symmetry_of_iso mB mA F μ βB βA
      (q.objObjPreimageIso X) (q.objObjPreimageIso Y)
      (hs (q.objPreimage X) (q.objPreimage Y))

end Transport

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Two tensor models for the same closed adjunction and Hom representatives coincide.

Source: Stacks 0A96, tensor-Hom currying, and 079P, K-injective resolutions.
(blueprint: lem-sf-native-ordinary-model-uniqueness)

Proof: resolve the ordinary tensor total by a K-injective complex I. Currying
its resolution map gives the same transpose for both model maps, by their
normalizations and coproduct extensionality. Thus the two model maps agree after
composition with the localized resolution map. This last map is invertible,
so cancellation proves equality of the model isomorphisms. Both flatness
hypotheses are used by normalization; no equality for nonflat Q is asserted. -/
private theorem normalized_model_unique
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (model model' : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (hn : NativeAdjunctionNormalization
      (ordinaryIhomBifunctor l Y) (ordinaryTensorBifunctor l Y)
      (fun P ↦ Mod.ihomAdjunction P) H R S (NativeOrdinaryKFlat l Y) model)
    (hn' : NativeAdjunctionNormalization
      (ordinaryIhomBifunctor l Y) (ordinaryTensorBifunctor l Y)
      (fun P ↦ Mod.ihomAdjunction P) H R S (NativeOrdinaryKFlat l Y) model')
    (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
    (hP : NativeOrdinaryKFlat l Y P) (hQ : NativeOrdinaryKFlat l Y Q) :
    model P Q hP = model' P Q hP := by
  classical
  let : Abelian.HasKInjectiveResolutions (ProEtale.AdicSheaf l Y) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  obtain ⟨I, hI, a, _, ha⟩ :=
    Abelian.HasKInjectiveResolutions.exists_isKInjective (ordinaryTensorTotal l Y P Q)
  let := ha
  have : IsIso (DerivedCategory.Q.map a) := inferInstance
  apply Iso.ext
  apply (cancel_mono (DerivedCategory.Q.map a)).1
  exact (tensor_model_normalized_map l Y H R S model hn P Q I hP hQ hI a).trans
    (tensor_model_normalized_map l Y H R S model' hn' P Q I hP hQ hI a).symm

attribute [local irreducible] Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedMonoidal
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedSymmetric
  DerivedCategory DerivedCategory.Q instCategoryDerivedCategory
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedTensorModel
  Functor.mapDerivedCategoryFactors HomologicalComplex.mapBifunctorMap
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeOrdinaryKFlat
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeTensorKFlat

-- The dependent ringed and ordinary tensor models require extra elaboration during descent.
/-- Extend the normalized representative coherence equations to all derived objects.

Source: Stacks 06YU, 0FPT; native tensor transport, final descent in step 3.
(blueprint: lem-sf-native-weil-tensor-ringed-derived-square-native-coherence).

Proof: the two representative lemmas give associativity on three native K-flat
complexes, and one common unit comparison with both unit equations and symmetry
on K-flat complexes. The localization A.localization is essentially surjective,
so every native derived object is isomorphic to such a representative. Naturality
of t, the associator, unitors and braidings transfers the equations along these
isomorphisms; the private calculations above carry this out for raw monoidal
structures. Assemble the five fields of TensorCoherence with that common unit.
The canonical localization clause in hS supplies the ordinary normalization
missing from the earlier proposed proof. -/
theorem native_weil_tensor_ringed_derived_square_native_coherence
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (he : ∀ (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I),
      e.inv.app (P, Q) ≫
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
            (((adj.adj P).homEquiv Q I).symm f) =
        ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f)
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
            (chain P Q).hom.f n =
        e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n h)
    (b : NativeWeilTensorRingedBridge k₀ l X)
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.K b.Q)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (SA : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.K b.Q))
    (TA : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.K b.Q SA)
    (βA : @SymmetricCategory _ _ SA.monoidal)
    (cA : RingedDerivedTensorCoherence b.K b.Q SA TA βA)
    (d : RingedForgetTensorTransposition.TensorComparison
      b.J b.R b.K b.Q b.forget b.underived SB TB βB cB SA TA βA cA)
    (ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q))
    (_hordinary : NativeAdjunctionNormalization
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (fun P ↦ Mod.ihomAdjunction P) M.ordinaryHom M.ordinaryRepresentatives S
        (NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ordinaryModel)
    (_hnaturality : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
          (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
          (hP' : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P')
          (f : P ⟶ P') (g : Q ⟶ Q'),
        S.tensor.map
            (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
            (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
            (ordinaryModel P' Q' hP').hom =
          (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ)))
    (t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (hforget : (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P),
    (nativeForget k₀ l X).map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q T)) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        S.tensor.map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom)) :
    Nonempty (RingedForgetTensorTransposition.TensorCoherence
        (nativeWeilRingedMonoidal b SB) S.monoidal
        (nativeWeilRingedSymmetric b SB βB) β (nativeForget k₀ l X) t) := by
  classical
  let K : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
    NativeTensorKFlat k₀ l X T
  let q := K.ι ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage K.ι
  let : q.IsLocalization W := A.localization
  let : q.EssSurj := Localization.essSurj q W
  have hS' := hS
  obtain ⟨model, _swap, hn, _hswap, _hβ, κ, hκ, hmodel⟩ := hS'
  have hcanonical_model (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
      (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
      (hQ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q) :
      HEq (ordinaryModel P Q hP).hom
        (Functor.LaxMonoidal.μ DerivedCategory.Q Q P ≫
          DerivedCategory.Q.map (κ P Q).inv) := by
    rw [normalized_model_unique l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S ordinaryModel model _hordinary hn P Q hP hQ]
    exact hmodel P Q hP hQ
  have ha := native_weil_tensor_ringed_associator_representatives
    k₀ l X T adj e he chain hchain b A M S β hmonoidal hS
    SB TB βB cB SA TA βA cA d ordinaryModel ⟨κ, hκ, hcanonical_model⟩
    _hnaturality t hforget
  obtain ⟨ε, hu, hs⟩ := native_weil_tensor_ringed_unit_symmetry_representatives
    k₀ l X T adj e he chain hchain b A M S β hmonoidal hS
    SB TB βB cB SA TA βA cA d ordinaryModel ⟨κ, hκ, hcanonical_model⟩
    _hnaturality t hforget
  apply coherence_of_representatives (nativeWeilRingedMonoidal b SB) S.monoidal
    (nativeForget k₀ l X) t q (nativeWeilRingedSymmetric b SB βB) β ε
  · intro P Q N
    exact ha P.obj Q.obj N.obj P.property Q.property N.property
  · intro P
    exact hu P.obj P.property
  · intro P Q
    exact hs P.obj Q.obj P.property Q.property

end AlgebraicGeometry.ProEtaleWeilSheaf
