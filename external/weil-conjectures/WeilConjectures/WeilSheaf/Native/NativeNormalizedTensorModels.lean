/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Normalized.NormalizedKFlatTensorModels
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations

/-! # Evaluation-normalized native tensor models

Source: Stacks 0A96, 08J9 and 06YN.
(blueprint: lem-sf-native-normalized-tensor-models).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
attribute [local irreducible] nativeDerivedClosedComparison

/-- The native tensor models retain their evaluation normalization.

Source: Stacks 0A96, 08J9 and 06YN; the K-flat tensor--Hom argument.
(blueprint: lem-sf-native-normalized-tensor-models).

Proof: the underived adjunction is parametrized by inverse mates. Apply the
normalized generic K-flat tensor--Hom construction to this adjunction and the
fixed Hom representatives of nativeDerivedClosedComparison. NativeIsKFlat's
second test is exactly the required preservation of quasi-isomorphisms. The
resulting isomorphisms are natural in both complexes and their evaluation maps
have the signed summand formula. Thus their choice is fixed by the adjunction,
rather than by naturality alone. -/
theorem native_normalized_tensor_models :
    ∃ e : ∀ (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeIsKFlat k₀ l X P → NativeIsKFlat k₀ l X T →
      ((nativeDerivedTensor k₀ l X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj (((nativeTensorTotal k₀ l X).obj P).obj T)),
    (∀ (P P' T T' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeIsKFlat k₀ l X P) (hP' : NativeIsKFlat k₀ l X P')
      (hT : NativeIsKFlat k₀ l X T) (hT' : NativeIsKFlat k₀ l X T')
      (f : P ⟶ P') (g : T ⟶ T'),
      (nativeDerivedTensor k₀ l X).map
          (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (e P' T' hP' hT').hom =
        (e P T hP hT).hom ≫ DerivedCategory.Q.map
          (((nativeTensorTotal k₀ l X).map f).app T ≫
            ((nativeTensorTotal k₀ l X).obj P').map g)) ∧
    KFlatTensorModelNormalization (nativeTensorBifunctor k₀ l X)
      (ihomBifunctor k₀ l X) (tensorIhomAdjunction k₀ l X)
      (nativeDerivedClosedComparison k₀ l X).homModels.weilHom
      (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives
      (nativeDerivedClosedComparison k₀ l X).weilClosed (NativeIsKFlat k₀ l X) e := by
  let adj : nativeTensorBifunctor k₀ l X ⊣₂ ihomBifunctor k₀ l X :=
    { adj := tensorIhomAdjunction k₀ l X
      unit_whiskerRight_map := by
        intro A B f
        apply NatTrans.ext
        funext P
        exact (unit_conjugateEquiv_symm
          (tensorIhomAdjunction k₀ l X B)
          (tensorIhomAdjunction k₀ l X A) ((ihomBifunctor k₀ l X).map f.op) P).symm }
  exact normalizedKFlatTensorModels (nativeTensorBifunctor k₀ l X)
    (ihomBifunctor k₀ l X)
    (nativeDerivedClosedComparison k₀ l X).homModels.weilHom
    (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives
    (nativeDerivedClosedComparison k₀ l X).weilClosed (NativeIsKFlat k₀ l X)
    adj (fun T hT _ _ f hf ↦ hT.2 f hf)

end AlgebraicGeometry.ProEtaleWeilSheaf
