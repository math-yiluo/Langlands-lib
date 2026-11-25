/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import Mathlib.Algebra.Homology.BifunctorHomotopy

/-! # Naturality from ordinary tensor resolution transport

Source: Stacks 06YU and 0FPT; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`.
(blueprint: lem-sf-native-weil-tensor-resolution-model-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem ordinaryTensorMap_comp (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
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

private theorem naturality_of_transport {D : Type v} [Category.{w} D]
    {A A' B B' X X' Z Z' : D} (q : A ⟶ B) [Epi q]
    {q' : A' ⟶ B'} {a : A ⟶ A'} {g : B ⟶ B'}
    {m : A ⟶ X} {m' : A' ⟶ X'} {e : B ⟶ Z} {e' : B' ⟶ Z'}
    {tq : X ⟶ Z} {tq' : X' ⟶ Z'} {ta : X ⟶ X'} {tg : Z ⟶ Z'}
    (hsquare : q ≫ g = a ≫ q') (hsource : q ≫ e = m ≫ tq)
    (htarget : q' ≫ e' = m' ≫ tq') (hnat : a ≫ m' = m ≫ ta)
    (htotal : ta ≫ tq' = tq ≫ tg) : g ≫ e' = e ≫ tg := by
  apply (cancel_epi q).mp
  calc
    q ≫ (g ≫ e') = a ≫ (q' ≫ e') := by rw [← Category.assoc, hsquare, Category.assoc]
    _ = a ≫ (m' ≫ tq') := by rw [htarget]
    _ = m ≫ (ta ≫ tq') := by rw [← Category.assoc, hnat, Category.assoc]
    _ = m ≫ (tq ≫ tg) := by rw [htotal]
    _ = q ≫ (e ≫ tg) := by rw [← Category.assoc, ← hsource, Category.assoc]

-- Preserve the supplied names of hypotheses that only constrain the proof.
set_option linter.unusedVariables false in
/-- Resolution transport data imply naturality of the extended ordinary model.

Source: Stacks Tags 06YU and 0FPT, the common-roof comparison argument
(blueprint: lem-sf-native-weil-tensor-resolution-model-naturality).

Proof plan: for a map of arbitrary second complexes, choose the K-flat roof
provided by the resolution-lift clause.  Expand both sides with the transport
identity, use the K-flat naturality square for the roof map, and cancel the
localized quasi-isomorphism maps.  Homotopy invariance of `DerivedCategory.Q`
identifies the two composites over the augmentation homotopy. -/
theorem native_ordinary_tensor_model_resolution_naturality
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (extendedModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (htransport : ∀ (P Q K : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
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
            (ordinaryTensorBifunctor l Y) (.up ℤ)))
    (hresolution : ∀ (Q Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (g : Q ⟶ Q'),
      ∃ (K K' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hK : NativeOrdinaryKFlat l Y K)
        (hK' : NativeOrdinaryKFlat l Y K')
        (q : K ⟶ Q) (q' : K' ⟶ Q') (u : K ⟶ K'),
        QuasiIso q ∧ QuasiIso q' ∧ Nonempty (Homotopy (u ≫ q') (q ≫ g)))
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
    ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hP' : NativeOrdinaryKFlat l Y P')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      S.tensor.map
          (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
          (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
          (extendedModel P' Q' hP').hom =
        (extendedModel P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g
            (ordinaryTensorBifunctor l Y) (.up ℤ)) := by
  intro P Q P' Q' hP hP' f g
  obtain ⟨K, K', hK, hK', q, q', a, hq, hq', ⟨h⟩⟩ := hresolution Q Q' g
  have hroof : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map q' =
      DerivedCategory.Q.map q ≫ DerivedCategory.Q.map g := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy _ h
  have htotal :
      DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f a (ordinaryTensorBifunctor l Y) (.up ℤ)) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P') q'
            (ordinaryTensorBifunctor l Y) (.up ℤ)) =
      DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) q
            (ordinaryTensorBifunctor l Y) (.up ℤ)) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g (ordinaryTensorBifunctor l Y) (.up ℤ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ordinaryTensorMap_comp,
      ordinaryTensorMap_comp, Category.comp_id, Category.id_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy _
      (HomologicalComplex.mapBifunctorMapHomotopy₂ f h (ordinaryTensorBifunctor l Y) (.up ℤ))
  have hprod :
      Prod.mkHom (DerivedCategory.Q.map q) (𝟙 (DerivedCategory.Q.obj P)) ≫
          Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f) =
        Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map f) ≫
          Prod.mkHom (DerivedCategory.Q.map q') (𝟙 (DerivedCategory.Q.obj P')) := by
    apply Prod.hom_ext
    · exact hroof.symm
    · simp
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).mpr hq
  have : IsIso
      (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 (DerivedCategory.Q.obj P))) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have hsquare := congrArg (fun t ↦ S.tensor.map t) hprod
  simp only [Functor.map_comp] at hsquare
  exact naturality_of_transport
    (S.tensor.map (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 (DerivedCategory.Q.obj P))))
    hsquare (htransport P Q K hP hK q hq) (htransport P' Q' K' hP' hK' q' hq')
    (hkflat P K P' K' hP hP' hK hK' f a) htotal

end AlgebraicGeometry.ProEtaleWeilSheaf
