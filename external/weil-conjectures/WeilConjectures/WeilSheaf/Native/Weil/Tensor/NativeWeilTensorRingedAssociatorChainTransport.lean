/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainData
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBinaryChainSquare
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorChainAssociativity

/-! Homogeneous transport for the explicit associator chain. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem tensor_square_pasting
    {C B A O : Type*} [Category C] [Category B] [Category A] [Category O]
    [MonoidalCategory B] [MonoidalCategory A] [MonoidalCategory O]
    (E : C ⥤ B) (U : C ⥤ O) (F : B ⥤ A) (G : O ⥤ A) [G.Faithful]
    (μ : MonoidalCategory.tensor B ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor A)
    (ν : MonoidalCategory.tensor O ⋙ G ≅ G.prod G ⋙ MonoidalCategory.tensor A)
    (τ : E ⋙ F ≅ U ⋙ G) (t : C → C → C)
    (d : ∀ P Q, E.obj (t P Q) ≅ E.obj P ⊗ E.obj Q)
    (c : ∀ P Q, U.obj (t P Q) ≅ U.obj P ⊗ U.obj Q)
    (hb : ∀ P Q,
      F.map (d P Q).hom ≫ μ.hom.app (E.obj P, E.obj Q) ≫
          (τ.hom.app P ⊗ₘ τ.hom.app Q) =
        τ.hom.app (t P Q) ≫ G.map (c P Q).hom ≫
          ν.hom.app (U.obj P, U.obj Q))
    (hμ : ∀ X Y Z,
      F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
          (F.obj X ◁ μ.hom.app (Y, Z)) =
        μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom)
    (hν : ∀ X Y Z,
      G.map (α_ X Y Z).hom ≫ ν.hom.app (X, Y ⊗ Z) ≫
          (G.obj X ◁ ν.hom.app (Y, Z)) =
        ν.hom.app (X ⊗ Y, Z) ≫ (ν.hom.app (X, Y) ▷ G.obj Z) ≫
          (α_ (G.obj X) (G.obj Y) (G.obj Z)).hom)
    (P Q N : C) (a : t (t P Q) N ⟶ t P (t Q N))
    (ha : E.map a ≫ (d P (t Q N)).hom ≫ (E.obj P ◁ (d Q N).hom) =
      (d (t P Q) N).hom ≫ ((d P Q).hom ▷ E.obj N) ≫
        (α_ (E.obj P) (E.obj Q) (E.obj N)).hom) :
    U.map a ≫ (c P (t Q N)).hom ≫ (U.obj P ◁ (c Q N).hom) =
      (c (t P Q) N).hom ≫ ((c P Q).hom ▷ U.obj N) ≫
        (α_ (U.obj P) (U.obj Q) (U.obj N)).hom := by
  have hnl (X Y Z : O) (f : X ⟶ Y) :
      G.map (f ▷ Z) ≫ ν.hom.app (Y, Z) =
        ν.hom.app (X, Z) ≫ (G.map f ▷ G.obj Z) := by
    have hn := ν.hom.naturality (X := (X, Z)) (Y := (Y, Z)) (f, 𝟙 Z)
    change G.map (f ⊗ₘ 𝟙 Z) ≫ ν.hom.app (Y, Z) =
      ν.hom.app (X, Z) ≫ (G.map f ⊗ₘ G.map (𝟙 Z)) at hn
    simp only [G.map_id] at hn
    erw [tensorHom_id, tensorHom_id] at hn
    exact hn
  have hnr (X Y Z : O) (f : Y ⟶ Z) :
      G.map (X ◁ f) ≫ ν.hom.app (X, Z) =
        ν.hom.app (X, Y) ≫ (G.obj X ◁ G.map f) := by
    have hn := ν.hom.naturality (X := (X, Y)) (Y := (X, Z)) (𝟙 X, f)
    change G.map (𝟙 X ⊗ₘ f) ≫ ν.hom.app (X, Z) =
      ν.hom.app (X, Y) ≫ (G.map (𝟙 X) ⊗ₘ G.map f) at hn
    simp only [G.map_id] at hn
    erw [id_tensorHom, id_tensorHom] at hn
    exact hn
  have hL := tensorModel_left_square F G μ
    (d P Q).hom (d (t P Q) N).hom
    (τ.hom.app P) (τ.hom.app Q) (τ.hom.app N)
    (τ.hom.app (t P Q)) (τ.hom.app (t (t P Q) N))
    (c P Q).hom (c (t P Q) N).hom
    (ν.hom.app (U.obj P, U.obj Q))
    (ν.hom.app (U.obj (t P Q), U.obj N))
    (ν.hom.app (U.obj P ⊗ U.obj Q, U.obj N))
    (hb P Q) (hb (t P Q) N)
    (hnl _ _ _ (c P Q).hom)
  have hR := tensorModel_right_square F G μ
    (d Q N).hom (d P (t Q N)).hom
    (τ.hom.app P) (τ.hom.app Q) (τ.hom.app N)
    (τ.hom.app (t Q N)) (τ.hom.app (t P (t Q N)))
    (c Q N).hom (c P (t Q N)).hom
    (ν.hom.app (U.obj Q, U.obj N))
    (ν.hom.app (U.obj P, U.obj (t Q N)))
    (ν.hom.app (U.obj P, U.obj Q ⊗ U.obj N))
    (hb Q N) (hb P (t Q N))
    (hnr _ _ _ (c Q N).hom)
  apply G.map_injective
  apply (cancel_epi (τ.hom.app (t (t P Q) N))).1
  apply (cancel_mono (ν.hom.app (U.obj P, U.obj Q ⊗ U.obj N) ≫
    (G.obj (U.obj P) ◁ ν.hom.app (U.obj Q, U.obj N)))).1
  have ht := τ.hom.naturality a
  dsimp only [Functor.comp_map] at ht
  simp only [Functor.map_comp, Category.assoc] at *
  rw [← reassoc_of% ht, ← hR]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, ha]
  simp only [F.map_comp, Category.assoc]
  rw [reassoc_of% hμ]
  rw [← associator_naturality]
  rw [reassoc_of% hL]
  rw [hν]

-- Normalize the total tensor map before specializing to the native comparison maps.
private theorem coefficientTotalTensor_map_tensorHom
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    {P P' Q Q' : CochainComplex (RingedTensorModules.{u, u, u} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (coefficientTotalTensor.{u, u, u} J R).map (X := (P, Q)) (Y := (P', Q')) (f, g) =
      f ⊗ₘ g := by
  exact RingedForgetTensorTransposition.tensor_map₂_eq f g

private theorem nativeRingedAssociatorComponent_normalize
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (a : nativeTensorComplex T (nativeTensorComplex T P Q) N ⟶
      nativeTensorComplex T P (nativeTensorComplex T Q N)) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
    letI := SheafOfModules.monoidalCategory D.b.R
    let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
    (∀ n, (E.map a ≫ (nativeRingedTripleRight D.b T D.adj D.A P Q N).hom).f n =
      ((nativeRingedTripleLeft D.b T D.adj D.A P Q N).hom ≫
        (α_ (E.obj P) (E.obj Q) (E.obj N)).hom).f n) →
    E.map a ≫ (D.A.chain (nativeTensorComplex T Q N) P).hom ≫
        (E.obj P ◁ (D.A.chain N Q).hom) =
      (D.A.chain N (nativeTensorComplex T P Q)).hom ≫
        ((D.A.chain Q P).hom ▷ E.obj N) ≫
          (α_ (E.obj P) (E.obj Q) (E.obj N)).hom := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
  let := SheafOfModules.monoidalCategory D.b.R
  let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
  dsimp only
  intro hsquare
  have hs : E.map a ≫ (nativeRingedTripleRight D.b T D.adj D.A P Q N).hom =
      (nativeRingedTripleLeft D.b T D.adj D.A P Q N).hom ≫
        (α_ (E.obj P) (E.obj Q) (E.obj N)).hom :=
    HomologicalComplex.hom_ext _ _ hsquare
  simpa only [nativeRingedTripleLeft, nativeRingedTripleRight, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, coefficientTotalTensor_map_tensorHom,
    id_tensorHom, tensorHom_id, Category.assoc] using hs

-- Keep the chain map abstract while pasting the comparison squares.
private theorem nativeChainForget_transport_map
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (a : nativeTensorComplex T (nativeTensorComplex T P Q) N ⟶
      nativeTensorComplex T P (nativeTensorComplex T Q N)) :
    letI : MonoidalCategory (CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
      Mod.monoidalCategoryCochainComplex
    let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
    let U := nativeChainForgetU (T := T)
    (∀ n, (E.map a ≫ (nativeRingedTripleRight D.b T D.adj D.A P Q N).hom).f n =
      ((nativeRingedTripleLeft D.b T D.adj D.A P Q N).hom ≫
        (α_ (E.obj P) (E.obj Q) (E.obj N)).hom).f n) →
    U.map a ≫ (nativeChainForgetC D P (nativeTensorComplex T Q N)).hom ≫
        (U.obj P ◁ (nativeChainForgetC D Q N).hom) =
      (nativeChainForgetC D (nativeTensorComplex T P Q) N).hom ≫
        ((nativeChainForgetC D P Q).hom ▷ U.obj N) ≫
          (α_ (U.obj P) (U.obj Q) (U.obj N)).hom := by
  classical
  let mO : MonoidalCategory (CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :=
    Mod.monoidalCategoryCochainComplex
  let := mO.toMonoidalCategoryStruct
  let mB : MonoidalCategory (CochainComplex
      (RingedTensorModules.{u + 1, u + 1, u + 1} D.b.J D.b.R) ℤ) := inferInstance
  let := mB.toMonoidalCategoryStruct
  let mA : MonoidalCategory (CochainComplex
      (RingedTensorModules.{u + 1, u + 1, u + 1} D.b.K D.b.Q) ℤ) := inferInstance
  let := mA.toMonoidalCategoryStruct
  let d := Classical.choice (native_ordinary_ringed_tensor_underived_data D.b)
  let o := Classical.choice (native_ordinary_ringed_tensor_chain_comparison D.b D.κ D.hκ d)
  let r := Classical.choice (native_ringed_forget_tensor_chain_comparison D.b)
  let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
  let F := D.b.forget.mapHomologicalComplex (.up ℤ)
  let G := D.b.ordinary.functor.mapHomologicalComplex (.up ℤ)
  let U := nativeChainForgetU (T := T)
  dsimp only
  intro hsquare
  have ha := nativeRingedAssociatorComponent_normalize D P Q N a hsquare
  refine tensor_square_pasting
    (C := CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (B := CochainComplex
      (RingedTensorModules.{u + 1, u + 1, u + 1} D.b.J D.b.R) ℤ)
    (A := CochainComplex
      (RingedTensorModules.{u + 1, u + 1, u + 1} D.b.K D.b.Q) ℤ)
    (O := CochainComplex
      (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
    E U F G r.tensor o.tensor
    (nativeRingedChainBridgeSquare D) (nativeTensorComplex T)
    (fun P Q ↦ D.A.chain Q P) (nativeChainForgetC D)
    (hb := ?_) (hμ := ?_) (hν := ?_) P Q N a ?_
  · intro P Q
    exact native_weil_tensor_ringed_binary_chain_square D d o r P Q
  · exact r.associativity
  · intro X Y Z
    exact o.associativity X Y Z
  · exact ha

/-- The ringed associator square, after one outer homogeneous inclusion, transports
through the ordinary comparison and the signed balanced tensor quotient.
Source: Stacks 0FPQ, 0FNG, 06YU, 0FPT.
(blueprint: new-sf-native-weil-ringed-associator-chain-component).

Proof: first promote the supplied component squares to the full ringed chain
map equality. The binary chain square identifies each normalized native tensor
comparison across the bridge. Paste its four instances with the restriction and
ordinary tensorator associativity laws, using naturality of the bridge and
faithfulness of the ordinary equivalence. This gives the full ordinary chain
equality. Take its degree component and precompose the specified outer inclusion.
The binary chain calculation and ordinary normalization are separate dependencies. -/
theorem nativeChainForgetComponent_transport
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X}
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)
    (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hsquare : ∀ n : ℤ, nativeRingedAssociatorComponent D P Q N n)
    (n p q : ℤ) (h : p + q = n) :
    nativeChainForgetComponent D P Q N n p q h := by
  have hc := nativeChainForget_transport_map D P Q N
    (nativeRingedAssociatorComplex D.b T D.adj D.A P Q N).hom hsquare
  have hn := congrArg (fun f ↦ f.f n) hc
  dsimp only [nativeChainForgetComponent]
  exact congrArg (fun f ↦
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
      (HomologicalComplex.ιMapBifunctor N (Q.mapBifunctor P T) T
        (.up ℤ) p q n h) ≫ f) hn

end AlgebraicGeometry.ProEtaleWeilSheaf
