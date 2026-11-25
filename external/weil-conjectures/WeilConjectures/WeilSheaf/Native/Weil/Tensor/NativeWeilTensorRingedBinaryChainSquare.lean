/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRingedTensorChainComparison
public import WeilConjectures.WeilSheaf.Native.NativeRingedForgetTensorChainComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedBinarySquare
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp

/-! # The binary square for normalized native tensor complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] Mod.monoidalCategoryCochainComplex

/-- Compare the two normalized paths through a summand using only additive functor laws. -/
private theorem binaryChainSquare_of_summands
    {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Preadditive C₁] [Preadditive C₃]
    (F : C₁ ⥤ C₃) [F.Additive] (G : C₂ ⥤ C₃)
    {S S' T T' : C₁} {A A' B B' B'' : C₂} {R R' Z Z' : C₃}
    {i : S ⟶ S'} {f : S' ⟶ T'} {a : S ⟶ T} {j : T ⟶ T'}
    {r : F.obj T' ⟶ R'} {b : F.obj T ⟶ R} {j' : R ⟶ R'}
    {z : R' ⟶ Z'} {t : R ⟶ Z} {k : Z ⟶ Z'}
    {g : A ⟶ A'} {h : A' ⟶ B'} {e : A ⟶ B} {l : B ⟶ B'}
    {κ : B' ⟶ B''} {o : G.obj B'' ⟶ Z'} {d : G.obj B ⟶ Z}
    {τ₀ : F.obj S ⟶ G.obj A} {τ₁ : F.obj S' ⟶ G.obj A'} (s : ℤ)
    (hs : i ≫ f = s • (a ≫ j)) (hr : F.map j ≫ r = b ≫ j')
    (hc : g ≫ h = e ≫ l) (ho : G.map l ≫ G.map κ ≫ o = s • (d ≫ k))
    (ht : F.map i ≫ τ₁ = τ₀ ≫ G.map g) (hi : j' ≫ z = t ≫ k)
    (hb : F.map a ≫ b ≫ t = τ₀ ≫ G.map e ≫ d) :
    F.map i ≫ F.map f ≫ r ≫ z = F.map i ≫ τ₁ ≫ G.map (h ≫ κ) ≫ o := by
  rw [← F.map_comp_assoc, hs]
  simp only [Functor.map_zsmul, Functor.map_comp, Preadditive.zsmul_comp,
    Category.assoc]
  rw [reassoc_of% hr, hi, reassoc_of% ht, ← G.map_comp_assoc, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [ho]
  simp only [Preadditive.comp_zsmul]
  exact congrArg (fun f ↦ s • f) ((reassoc_of% hb) k)

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X}
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)

/-- Apply the bridge square termwise. All components are the specified underived
square components, so no comparison data are selected by this construction.
Source: Stacks 06YN (blueprint: new-sf-native-weil-tensor-ringed-binary-chain-square). -/
def nativeRingedChainBridgeSquare :
    D.b.native.functor.mapHomologicalComplex (.up ℤ) ⋙
        D.b.forget.mapHomologicalComplex (.up ℤ) ≅
      nativeChainForgetU (T := T) ⋙ D.b.ordinary.functor.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex D.b.square (.up ℤ)

-- Both normalized site tensors occur in this square.
-- The degreewise comparison crosses three concrete total constructions.
/-- The normalized comparisons commute for a single pair of native complexes.
Source: Stacks 06YS, 06YU and 0FPT
(blueprint: new-sf-native-weil-tensor-ringed-binary-chain-square).

Proof: first compare underived inverses by their tensor--Hom mates. The native
uncurrying equation, the equation `he` for ordinary forgetting, and the Hom square
of the bridge give the same mate after applying the ordinary adjunction. Cancel
the sheaf tensor braidings using symmetry of the restriction tensorator. This
proves the underived binary square. Next use coproduct extensionality after the
native equivalence. The equations `hchain`, the native summand equation, the
ordinary normalized summand equation and the restriction summand equation reduce
the two sides to this underived square. Naturality of the termwise bridge square
moves each summand inclusion through it. Both exchanges contribute the same
scalar (-1)^(pq), and additivity moves that scalar through the comparisons.
This calculation uses only two factors and no associator. -/
theorem native_weil_tensor_ringed_binary_chain_square
    (d : NativeOrdinaryRingedTensorUnderivedData D.b)
    (o : NativeOrdinaryRingedTensorChainComparison D.b D.κ d)
    (r : NativeRingedForgetTensorChainComparison D.b)
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
    let F := D.b.forget.mapHomologicalComplex (.up ℤ)
    let G := D.b.ordinary.functor.mapHomologicalComplex (.up ℤ)
    let U := nativeChainForgetU (T := T)
    let τ := nativeRingedChainBridgeSquare D
    F.map (D.A.chain Q P).hom ≫ r.tensor.hom.app (E.obj P, E.obj Q) ≫
        (τ.hom.app P ⊗ₘ τ.hom.app Q) =
      τ.hom.app (nativeTensorComplex T P Q) ≫
        G.map (nativeChainForgetC D P Q).hom ≫ o.tensor.hom.app (U.obj P, U.obj Q) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
  let := SheafOfModules.monoidalCategory D.b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.Q
  let := SheafOfModules.monoidalCategory D.b.Q
  let V := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let E := D.b.native.functor.mapHomologicalComplex (.up ℤ)
  let F := D.b.forget.mapHomologicalComplex (.up ℤ)
  let G := D.b.ordinary.functor.mapHomologicalComplex (.up ℤ)
  let U := nativeChainForgetU (T := T)
  let τ := nativeRingedChainBridgeSquare D
  have (I : Type) : PreservesColimitsOfShape (Discrete I) D.b.forget :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift.{u + 1, 0} : ULift.{u + 1} I ≃ I)) D.b.forget
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (D.b.native.functor ⋙ D.b.forget)
  intro p q hpq
  have hpq : p + q = n := hpq
  have hqp : q + p = n := by omega
  have hs := D.A.summand Q P p q n hpq hqp
  have hr := r.summand (E.obj P) (E.obj Q) q p n hqp
  have ho := o.summand (U.obj Q) (U.obj P) p q n hpq hqp
  have hc := D.hchain Q P p q n hpq
  have hb := native_weil_tensor_ringed_underived_binary_square D d (Q.X p) (P.X q)
  have ht := D.b.square.hom.naturality
    (HomologicalComplex.ιMapBifunctor Q P T (.up ℤ) p q n hpq)
  dsimp only [Functor.comp_map] at ht
  have hi := CochainComplex.ιTensorObj_tensorHom_f
    (τ.hom.app P) (τ.hom.app Q) q p n hqp
  exact binaryChainSquare_of_summands D.b.forget D.b.ordinary.functor
    ((p * q).negOnePow : ℤ) hs hr hc ho ht hi hb

end AlgebraicGeometry.ProEtaleWeilSheaf
