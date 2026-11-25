/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionRoof
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Transport part of ordinary tensor resolution data

Source: Stacks 06YS, 06YU; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`.
(blueprint: lem-sf-native-weil-tensor-resolution-model-transport)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- The argument uses the functor APIs, without unfolding the tensor implementations.
attribute [local irreducible] CoefficientClosedStructure.tensor ordinaryTensorBifunctor

private theorem tensorMap_comp (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {P P' P'' Q Q' Q'' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    HomologicalComplex.mapBifunctorMap f g (ordinaryTensorBifunctor l Y) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap f' g' (ordinaryTensorBifunctor l Y) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (f ≫ f') (g ≫ g')
        (ordinaryTensorBifunctor l Y) (.up ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
    Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]

private theorem tensorMap_id (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 P) (𝟙 Q)
      (ordinaryTensorBifunctor l Y) (.up ℤ) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp

private noncomputable def tensorLocalized (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) :
    CochainComplex (ProEtale.AdicSheaf l Y) ℤ ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y) where
  obj Q := DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q)
  map g := DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (𝟙 P) g (ordinaryTensorBifunctor l Y) (.up ℤ))
  map_id Q := by
    rw [tensorMap_id]
    exact DerivedCategory.Q.map_id _
  map_comp g g' := by
    rw [← Functor.map_comp, tensorMap_comp, Category.id_comp]

private noncomputable def tensorHomotopy (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) :
    HomotopyCategory (ProEtale.AdicSheaf l Y) (.up ℤ) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y) :=
  CategoryTheory.Quotient.lift _ (tensorLocalized l Y P) (by
    rintro Q Q' g g' ⟨h⟩
    exact DerivedCategory.Q_map_eq_of_homotopy _
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 P) h
        (ordinaryTensorBifunctor l Y) (.up ℤ)))

private noncomputable def tensorSource (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y)}
    (S : CoefficientClosedStructure H)
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) :
    HomotopyCategory (ProEtale.AdicSheaf l Y) (.up ℤ) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y) :=
  DerivedCategory.Qh ⋙
    (𝟭 (DerivedCategory (ProEtale.AdicSheaf l Y))).prod'
      ((Functor.const (DerivedCategory (ProEtale.AdicSheaf l Y))).obj
        (DerivedCategory.Q.obj P)) ⋙ S.tensor

private theorem tensorMap_quasiIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (hP : NativeOrdinaryKFlat l Y P)
    {Q Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ}
    (q : Q ⟶ Q') (hq : QuasiIso q) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 P) q
      (ordinaryTensorBifunctor l Y) (.up ℤ)) := by
  have ht := hP _ ((CochainComplex.mappingCone.quasiIso_iff_acyclic q).mp hq)
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).mpr
  intro n
  exact (ht n).of_iso
    (CochainComplex.mapBifunctorMappingCone₂Iso P q (ordinaryTensorBifunctor l Y))

private theorem resolving_iso {C D : Type*} [Category C] [Category D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : C → Prop)
    (hres : ∀ X : C, ∃ (R : C) (s : R ⟶ X), P R ∧ W s)
    (A B : C ⥤ D) (hA : W.IsInvertedBy A) (hB : W.IsInvertedBy B)
    (α : ∀ X : C, P X → (A.obj X ≅ B.obj X))
    (hα : ∀ (X Y : C) (hX : P X) (hY : P Y) (s : X ⟶ Y),
      A.map s ≫ (α Y hY).hom = (α X hX).hom ≫ B.map s) :
    ∃ e : A ≅ B, ∀ (X : C) (hX : P X), e.app X = α X hX := by
  classical
  obtain ⟨β, hβ⟩ := exists_natTrans_from_resolvingClass W P hres A B hA
    (fun X hX ↦ (α X hX).hom) hα
  have hiso (X : C) : IsIso (β.app X) := by
    obtain ⟨R, s, hR, hs⟩ := hres X
    have := hA _ hs
    have := hB _ hs
    have : IsIso (β.app R) := by rw [hβ R hR]; infer_instance
    have : IsIso (A.map s ≫ β.app X) := by rw [β.naturality]; infer_instance
    exact IsIso.of_isIso_comp_left (A.map s) (β.app X)
  let e : A ≅ B := NatIso.ofComponents (fun X ↦ asIso (β.app X))
    (fun {X Y} f ↦ β.naturality f)
  refine ⟨e, ?_⟩
  intro X hX
  apply Iso.ext
  change β.app X = (α X hX).hom
  exact hβ X hX

/--
The K-flat resolution construction supplies an ordinary tensor model on every
second complex, together with its restriction to K-flat inputs and its
augmentation transport identity.  The common-roof assertion is separated into
`native_ordinary_tensor_model_resolution_roof`.

Source: Stacks Tags 06YS and 06YU, K-flat replacement and resolution-comparison
paragraph in the ordinary tensor construction.  Choose a degreewise-epimorphic
K-flat resolution of the second input, tensor its augmentation with the K-flat
first input, and invert the resulting localized quasi-isomorphism.  Independence
of two such resolutions gives the restriction equation.  The localization
square gives the transport equation.
(blueprint: lem-sf-native-weil-tensor-resolution-model-transport)
-/
theorem native_ordinary_tensor_model_resolution_transport
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (hkflat : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hP' : NativeOrdinaryKFlat l Y P')
      (hQ : NativeOrdinaryKFlat l Y Q)
      (hQ' : NativeOrdinaryKFlat l Y Q')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      S.tensor.map
          (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
          (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
          (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g
            (ordinaryTensorBifunctor l Y) (.up ℤ))) :
    ∃ extendedModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q),
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P)
        (hQ : NativeOrdinaryKFlat l Y Q),
        extendedModel P Q hP = model P Q hP) ∧
      (∀ (P Q K : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P)
        (hK : NativeOrdinaryKFlat l Y K)
        (q : K ⟶ Q) (hq : QuasiIso q),
        S.tensor.map
            (X := (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 _)) ≫
            (extendedModel P Q hP).hom =
          (model P K hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) q
              (ordinaryTensorBifunctor l Y) (.up ℤ))) := by
  classical
  let C := ProEtale.AdicSheaf l Y
  let Qh := HomotopyCategory.quotient C (.up ℤ)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have hres (X : HomotopyCategory C (.up ℤ)) :
      ∃ (K : HomotopyCategory C (.up ℤ)) (s : K ⟶ X),
        NativeOrdinaryKFlat l Y K.as ∧ W s := by
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, K', hK, hK', q, q', a, hq, hq', ha⟩ :=
      native_ordinary_tensor_model_resolution_roof l Y Q Q (𝟙 Q)
    exact ⟨Qh.obj K, Qh.map q, hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff q).mpr hq⟩
  have hext (P : CochainComplex C ℤ) (hP : NativeOrdinaryKFlat l Y P) :
      ∃ e : tensorSource l Y S P ≅ tensorHomotopy l Y P,
        ∀ (Q : CochainComplex C ℤ) (hQ : NativeOrdinaryKFlat l Y Q),
          e.app (Qh.obj Q) = model P Q hP := by
    let A := tensorSource l Y S P
    let B := tensorHomotopy l Y P
    have hA : W.IsInvertedBy A := by
      intro X X' s hs
      have := Localization.inverts DerivedCategory.Qh W s hs
      change IsIso (S.tensor.map
        (Prod.mkHom (DerivedCategory.Qh.map s) (𝟙 (DerivedCategory.Q.obj P))))
      have : IsIso
          (Prod.mkHom (DerivedCategory.Qh.map s) (𝟙 (DerivedCategory.Q.obj P))) :=
        (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      infer_instance
    have hB : W.IsInvertedBy B := by
      intro X X' s hs
      obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      obtain ⟨Q', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
      obtain ⟨s, rfl⟩ := Qh.map_surjective s
      have hs' := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mp hs
      have := tensorMap_quasiIso l Y P hP s hs'
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr this
    obtain ⟨e, he⟩ := resolving_iso W (fun X ↦ NativeOrdinaryKFlat l Y X.as)
      hres A B hA hB (fun X hX ↦ model P X.as hP) (by
        intro X X' hX hX' s
        obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
        obtain ⟨Q', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
        obtain ⟨s, rfl⟩ := Qh.map_surjective s
        change S.tensor.map
            (Prod.mkHom (DerivedCategory.Q.map s) (𝟙 (DerivedCategory.Q.obj P))) ≫
            (model P Q' hP).hom =
          (model P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) s
              (ordinaryTensorBifunctor l Y) (.up ℤ))
        simpa only [CategoryTheory.Functor.map_id] using
          hkflat P Q P Q' hP hP hX hX' (𝟙 P) s)
    exact ⟨e, fun Q hQ ↦ he (Qh.obj Q) hQ⟩
  choose e he using hext
  refine ⟨fun P Q hP ↦ (e P hP).app (Qh.obj Q), ?_, ?_⟩
  · exact fun P Q hP hQ ↦ he P hP Q hQ
  · intro P Q K hP hK q hq
    have hn := (e P hP).hom.naturality (Qh.map q)
    change S.tensor.map (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 _)) ≫
        ((e P hP).app (Qh.obj Q)).hom =
      ((e P hP).app (Qh.obj K)).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 P) q
          (ordinaryTensorBifunctor l Y) (.up ℤ)) at hn
    rw [he P hP K hK] at hn
    exact hn

end AlgebraicGeometry.ProEtaleWeilSheaf
