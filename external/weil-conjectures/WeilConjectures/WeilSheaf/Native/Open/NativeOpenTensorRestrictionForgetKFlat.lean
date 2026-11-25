/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTensor
import WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel

/-! # Representative restriction/forgetting square

Source: Stacks 0E8I, 0GL1 and 015F.
(blueprint: lem-sf-native-open-tensor-restriction-forget-kflat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem cancel_total_model_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z : C} {A B E W V K : D} (mZ : X ≅ Z) (mU : W ≅ V)
    {t : X ⟶ Y} {z : Y ⟶ Z} {u : W ⟶ V}
    {a : A ⟶ B} {b : B ⟶ E} {c : E ⟶ W}
    {d : A ⟶ F.obj X} {q : F.obj Z ⟶ K} {r : K ⟶ V} {ord : F.obj Y ⟶ W}
    (hmZ : mZ.hom = t ≫ z) (hmU : mU.hom = u)
    (hr : a ≫ b ≫ c ≫ mU.hom = d ≫ F.map mZ.hom ≫ q ≫ r)
    (ho : ord ≫ u = F.map z ≫ q ≫ r) :
    a ≫ b ≫ c = d ≫ F.map t ≫ ord := by
  apply (cancel_mono mU.hom).1
  simp only [Category.assoc]
  rw [hr, hmZ, F.map_comp]
  simp only [Category.assoc]
  rw [← ho, ← hmU]

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The restriction/forgetting square on two actual K-flat complexes, for the
ordinary comparison already constructed by normalized tensor--Hom adjunctions.

Source: Stacks 0GL1 (lemma-j-shriek-and-tensor), 0E8I and 015F;
steps 1--3 of the restriction-forgetting node.
(blueprint: lem-sf-native-open-tensor-restriction-forget-kflat).

Proof: use the ordinary total tensor models in dU.models and dZ.models. Their
adjunction normalization fixes the identifications with the standard localization
tensorator. Forget the actual native total tensors: on each (p,q) summand the
comparison is the underlying balanced tensor map, with the signed exchange
needed when reversing the right-parameter-first ordinary total convention.
Compatibility of nativeDerivedClosedComparison identifies its tensorComparison
with this total comparison: transpose into a K-injective ordinary target and
use the product-total Hom representative square; the ordinary normalized
uncurrying formula and injectivity of transposition give the equality.
Forgetting preserves the K-flat tests: induce an ordinary acyclic test complex
by the exact Frobenius orbit-sum left adjoint, apply native K-flatness, and
forget. The ordinary tensor test is the degree-zero orbit summand, a retract
of this acyclic direct sum. Repeat in the other tensor variable. Exact open
restriction preserves K-flatness by its projection formula and extension by zero.
On every summand, s.restriction_forget identifies the forgotten sheaf map with
the balanced restriction map. Hence c.restriction_summands identifies the two
total-complex composites, by the coproduct universal property. Apply Q and
its exact-functor factorization isomorphisms. The c.restriction_model equation
then replaces the native localized total map by rho, while the ordinary
tensorator normalization replaces the other map by
nativeOrdinaryRestrictionTensor. Naturality of the factorization maps gives
exactly the displayed equality. Zero complexes, empty opens and unbounded
diagonals use the same coproduct and localization identities. This statement
asserts no equality at arbitrary derived objects; that extension is proved
separately from the existence of K-flat models.

As formalized: the native part of this route (the K-flat forgetting, the binary
models and the summand comparison) is native_restriction_forget_total_model,
which gives the normalized total models mZ, mU and the native square followed by
mU. The ordinary part (the tensorator normalization) is
native_ordinary_restriction_total_model, applied to the forgotten complexes with
the exact forgetting factor isomorphisms as inputs; it rewrites the right-hand
side followed by mU into the same expression. Cancel the isomorphism mU. -/
theorem native_open_tensor_restriction_forget_kflat (s : NativeOpenTensorData k₀ l j)
    (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
      (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho)
    (dU : NativeOrdinaryTensorIdentification k₀ l U)
    (dZ : NativeOrdinaryTensorIdentification k₀ l Z) :
    ∀ (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ),
      NativeIsKFlat k₀ l Z P → NativeIsKFlat k₀ l Z T →
      let M := DerivedCategory.Q.obj P;
      let N := DerivedCategory.Q.obj T;
        (nativeForget k₀ l U).map (rho.hom.app (M, N)) ≫
          (nativeDerivedClosedComparison k₀ l U).tensorComparison.hom.app
            ((nativeOpenPull k₀ l j).obj M, (nativeOpenPull k₀ l j).obj N) ≫
          (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.map
            (Prod.mkHom ((nativeOpenForgetPull k₀ l j).hom.app M)
              ((nativeOpenForgetPull k₀ l j).hom.app N)) =
        (nativeOpenForgetPull k₀ l j).hom.app ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≫
          (ProEtale.adicUpperStar l
            (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory.map
              ((nativeDerivedClosedComparison k₀ l Z).tensorComparison.hom.app (M, N)) ≫
          (nativeOrdinaryRestrictionTensor k₀ l j dU dZ).hom.app
            ((nativeForget k₀ l Z).obj M, (nativeForget k₀ l Z).obj N) := by
  intro P T hP hT
  dsimp only
  let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  let R := ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P
  let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T
  obtain ⟨mZ, mU, hmZ, hmU, hr⟩ :=
    native_restriction_forget_total_model k₀ l j s rho c _hc dU dZ P T hP hT
  have ho := native_ordinary_restriction_total_model k₀ l j dU dZ P₀ T₀
    ((nativeForget k₀ l Z).obj (DerivedCategory.Q.obj P))
    ((nativeForget k₀ l Z).obj (DerivedCategory.Q.obj T))
    (F.mapDerivedCategoryFactors.app P) (F.mapDerivedCategoryFactors.app T)
  dsimp only [F, P₀, T₀, Iso.app_hom] at ho
  exact cancel_total_model_square R.mapDerivedCategory mZ mU hmZ hmU hr ho

end AlgebraicGeometry.ProEtaleWeilSheaf
