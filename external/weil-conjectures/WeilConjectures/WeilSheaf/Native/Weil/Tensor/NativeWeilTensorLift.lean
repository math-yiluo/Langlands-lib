/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTransposition
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorAdjoints
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorCoherence

/-! # Equivariant lift of a fixed normalized ordinary tensor

Source: native tensor transport, action-site part of steps 1--2; Stacks 06YS and 08J9
(blueprint: lem-sf-native-weil-tensor-lift).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
private def tensorSliceIso {C : Type*} [Category C] (m : MonoidalCategory C) (K : C) :
    Prod.sectL C K ⋙ @MonoidalCategory.tensor C _ m ≅
      @MonoidalCategory.tensorRight C _ m K := by
  let := m
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A B f
    change (f ⊗ₘ 𝟙 K) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ K)
    simp only [tensorHom_id, Category.comp_id, Category.id_comp])

private theorem uncurry_of_tensor_unit
    {C D : Type*} [Category C] [Category D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (W : CoefficientClosedStructure H) (S : CoefficientClosedStructure H')
    (F : C ⥤ D) (η : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    (τ : W.tensor ⋙ F ≅ (F.prod F) ⋙ S.tensor)
    (hu : ∀ A K : C,
      τ.inv.app (A, K) =
        (S.transpose (F.obj A) (F.obj K) (F.obj (W.tensor.obj (A, K)))).symm
          (F.map ((W.adjunction K).unit.app A) ≫
            η.hom.app (op K, W.tensor.obj (A, K))))
    (A K L : C) (f : A ⟶ H.obj (op K, L)) :
    (S.transpose (F.obj A) (F.obj K) (F.obj L)).symm
        (F.map f ≫ η.hom.app (op K, L)) =
      τ.inv.app (A, K) ≫ F.map ((W.transpose A K L).symm f) := by
  let g := (W.transpose A K L).symm f
  have hf : (W.adjunction K).unit.app A ≫
      H.map (X := (op K, W.tensor.obj (A, K))) (Y := (op K, L)) (𝟙 (op K), g) = f := by
    change (W.transpose A K L) ((W.transpose A K L).symm f) = f
    exact (W.transpose A K L).apply_symm_apply f
  have hn : F.map (H.map (𝟙 (op K), g)) ≫ η.hom.app (op K, L) =
      η.hom.app (op K, W.tensor.obj (A, K)) ≫
        H'.map (X := (op (F.obj K), F.obj (W.tensor.obj (A, K))))
          (Y := (op (F.obj K), F.obj L)) (𝟙 (op (F.obj K)), F.map g) := by
    simpa using η.hom.naturality (Prod.mkHom (𝟙 (op K)) g)
  have he : F.map f ≫ η.hom.app (op K, L) =
      (F.map ((W.adjunction K).unit.app A) ≫
        η.hom.app (op K, W.tensor.obj (A, K))) ≫
          H'.map (X := (op (F.obj K), F.obj (W.tensor.obj (A, K))))
            (Y := (op (F.obj K), F.obj L)) (𝟙 (op (F.obj K)), F.map g) := by
    rw [Category.assoc, ← hn, ← Category.assoc, ← F.map_comp, hf]
  calc
    _ = (S.transpose (F.obj A) (F.obj K) (F.obj L)).symm
        ((F.map ((W.adjunction K).unit.app A) ≫
          η.hom.app (op K, W.tensor.obj (A, K))) ≫
            H'.map (X := (op (F.obj K), F.obj (W.tensor.obj (A, K))))
              (Y := (op (F.obj K), F.obj L)) (𝟙 (op (F.obj K)), F.map g)) :=
      congrArg (S.transpose (F.obj A) (F.obj K) (F.obj L)).symm he
    _ = (S.transpose (F.obj A) (F.obj K) (F.obj (W.tensor.obj (A, K)))).symm
        (F.map ((W.adjunction K).unit.app A) ≫
          η.hom.app (op K, W.tensor.obj (A, K))) ≫ F.map g :=
      (S.adjunction (F.obj K)).homEquiv_naturality_right_symm
        (X := F.obj A) (Y := F.obj (W.tensor.obj (A, K))) (Y' := F.obj L)
        (F.map ((W.adjunction K).unit.app A) ≫
          η.hom.app (op K, W.tensor.obj (A, K))) (F.map g)
    _ = _ := by rw [hu]

private theorem lift_of_tensor_adjoints
    {C D : Type*} [Category C] [Category D]
    (H : Cᵒᵖ × C ⥤ C) (H' : Dᵒᵖ × D ⥤ D)
    (F : C ⥤ D) (η : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    (S : CoefficientClosedStructure H') (β : @SymmetricCategory _ _ S.monoidal)
    (U : C) (V : D) (ζ : F.obj U ≅ V)
    (hadj : ∃ T : C × C ⥤ C,
      ∃ a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H,
        (∀ (K K' L : C) (f : K' ⟶ K),
          T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
              (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
                (a K').counit.app L =
            T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
              (𝟙 (H.obj (op K, L)), f) ≫ (a K).counit.app L) ∧
        ∃ τ : T ⋙ F ≅ (F.prod F) ⋙ S.tensor,
          ∀ A K : C, τ.inv.app (A, K) =
            (S.transpose (F.obj A) (F.obj K) (F.obj (T.obj (A, K)))).symm
              (F.map ((a K).unit.app A) ≫ η.hom.app (op K, T.obj (A, K))))
    (hcoh : ∀ (T : C × C ⥤ C)
      (a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
      (_ha : ∀ (K K' L : C) (f : K' ⟶ K),
        T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
            (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
              (a K').counit.app L =
          T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
            (𝟙 (H.obj (op K, L)), f) ≫ (a K).counit.app L)
      (τ : T ⋙ F ≅ (F.prod F) ⋙ S.tensor)
      (_hτ : ∀ A K : C, τ.inv.app (A, K) =
        (S.transpose (F.obj A) (F.obj K) (F.obj (T.obj (A, K)))).symm
          (F.map ((a K).unit.app A) ≫ η.hom.app (op K, T.obj (A, K)))),
      ∃ m : MonoidalCategory C, ∃ hT : @MonoidalCategory.tensor _ _ m = T,
      ∃ γ : @SymmetricCategory _ _ m,
      ∃ δ : m.tensorUnit ≅ U, ∃ ε : S.monoidal.tensorUnit ≅ V,
      ∃ c : RingedForgetTensorTransposition.TensorCoherence m S.monoidal γ β F
          (eqToIso (congrArg (fun T' ↦ T' ⋙ F) hT) ≪≫ τ),
        c.unit = F.mapIso δ ≪≫ ζ ≪≫ ε.symm) :
    ∃ W : CoefficientClosedStructure H,
    ∃ γ : @SymmetricCategory _ _ W.monoidal,
    ∃ δ : W.monoidal.tensorUnit ≅ U, ∃ ε : S.monoidal.tensorUnit ≅ V,
    ∃ τ : W.tensor ⋙ F ≅ (F.prod F) ⋙ S.tensor,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence
        W.monoidal S.monoidal γ β F τ,
      c.unit = F.mapIso δ ≪≫ ζ ≪≫ ε.symm ∧
      ∀ (A K L : C) (f : A ⟶ H.obj (op K, L)),
        (S.transpose (F.obj A) (F.obj K) (F.obj L)).symm
            (F.map f ≫ η.hom.app (op K, L)) =
          τ.inv.app (A, K) ≫ F.map ((W.transpose A K L).symm f) := by
  obtain ⟨T, a, ha, τ, hτ⟩ := hadj
  obtain ⟨m, hT, γ, δ, ε, hc⟩ := hcoh T a ha τ hτ
  subst T
  have hcomp : Iso.refl (@MonoidalCategory.tensor C _ m ⋙ F) ≪≫ τ = τ :=
    Iso.refl_trans τ
  simp only [eqToIso_refl] at hc
  rw [hcomp] at hc
  obtain ⟨c, hc⟩ := hc
  have hcu (K L : C) :
      ((a K).ofNatIsoLeft (tensorSliceIso m K)).counit.app L = (a K).counit.app L := by
    change 𝟙 _ ≫ (a K).counit.app L = _
    exact Category.id_comp _
  have huu (A K : C) :
      ((a K).ofNatIsoLeft (tensorSliceIso m K)).unit.app A = (a K).unit.app A := by
    change (a K).unit.app A ≫ (Prod.sectR (op K) C ⋙ H).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id ((a K).unit.app A)
  let W : CoefficientClosedStructure H :=
    { monoidal := m
      adjunction := fun K ↦ (a K).ofNatIsoLeft (tensorSliceIso m K)
      evaluation_naturality := by
        intro K K' L f
        rw [hcu K' L, hcu K L]
        simpa [MonoidalCategory.tensor, MonoidalCategory.tensorRight,
          MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor, Functor.flip]
          using ha K K' L f }
  refine ⟨W, γ, δ, ε, τ, c, hc, ?_⟩
  refine uncurry_of_tensor_unit W S F η τ ?_
  intro A K
  change τ.inv.app (A, K) =
    (S.transpose (F.obj A) (F.obj K)
      (F.obj ((@MonoidalCategory.tensor C _ m).obj (A, K)))).symm
        (F.map (((a K).ofNatIsoLeft (tensorSliceIso m K)).unit.app A) ≫
          η.hom.app (op K, (@MonoidalCategory.tensor C _ m).obj (A, K)))
  rw [huu A K]
  exact hτ A K

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Lift a specified ordinary normalized tensor to native Weil complexes.
The canonical ordinary monoidal structure and its adjunction normalization are
inputs. The conclusion supplies the equivariant lift, coefficient-unit
identifications and uncurrying law; it does not construct an ordinary tensor.

Source: native tensor transport, action-site part of steps 1--2; Stacks 06YS,
08J9 and 0A97 (blueprint: lem-sf-native-weil-tensor-lift).

Proof: native_weil_tensor_adjoints supplies a tensor bifunctor T, its
adjunctions to M.weilHom, counit naturality in the tensor parameter, and an
invertible comparison tau. Its inverse is the ordinary transpose inverse of
the image of the native adjunction unit followed by eta. The construction of
associators, unitors and symmetry is isolated in native_weil_tensor_coherence;
it keeps exactly T and tau and gives the required coefficient-unit equation.
Assemble W from that monoidal structure and the supplied adjunctions.
For an arbitrary f:A -> M.weilHom(K,L), put g = uncurry_W(f). The adjunction
identity is unit_A followed by Hom(K,g) = f. Naturality of eta at (id_K,g),
then naturality of ordinary uncurrying, turns the unit-mate formula into
uncurry_S(F(f) followed by eta) = tau inverse followed by F(g).
The private lemma uncurry_of_tensor_unit proves this argument for arbitrary
categories. Thus no uncurrying statement for arbitrary arrows is left as a
hole, and the comparison used throughout is the supplied eta. -/
theorem native_weil_tensor_lift
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (_hη : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (_hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (_hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β) :
    ∃ W : CoefficientClosedStructure M.weilHom,
    ∃ γ : @SymmetricCategory _ _ W.monoidal,
    ∃ δ : W.monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ τ : W.tensor ⋙ nativeForget k₀ l X ≅
        (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence
        W.monoidal S.monoidal γ β (nativeForget k₀ l X) τ,
      c.unit =
        ((nativeForget k₀ l X).mapIso δ ≪≫
          (Functor.mapDerivedCategorySingleFunctor
            (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
              (adicConstant k₀ l X) ≪≫ ε.symm) ∧
      ∀ (A K L : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
        (f : A ⟶ M.weilHom.obj (op K, L)),
        (S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
            ((nativeForget k₀ l X).obj L)).symm
              ((nativeForget k₀ l X).map f ≫ (η.app (op K, L)).hom) =
          (τ.app (A, K)).inv ≫
            (nativeForget k₀ l X).map ((W.transpose A K L).symm f) := by
  exact lift_of_tensor_adjoints M.weilHom M.ordinaryHom (nativeForget k₀ l X) η S β
    ((DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X))
    ((DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    ((Functor.mapDerivedCategorySingleFunctor
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
        (adicConstant k₀ l X))
    (native_weil_tensor_adjoints k₀ l X M η _hη S β _hmonoidal _hS)
    (native_weil_tensor_coherence k₀ l X M η _hη S β _hmonoidal _hS)

end AlgebraicGeometry.ProEtaleWeilSheaf
