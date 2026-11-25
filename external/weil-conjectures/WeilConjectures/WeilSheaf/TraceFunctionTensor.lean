/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.StalkInternalHom
public import WeilConjectures.WeilSheaf.TraceFunctionOps

/-!
# Trace functions and the tensor product with a lisse Weil sheaf

The trace function of a Weil complex is multiplicative under the tensor product with a lisse
Weil sheaf.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_tensorLisse`: `t_{G ⊗ K} = t_G t_K`.

## Blueprint

These are the properties of the trace function (blueprint `definition-trace-function`,
`definition-trace-function`) used in the proof of the Fourier trace formula
(sketch blueprint `sec-The-Plancherel-formula`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- The underlying object of `G ⊗ K` is the right derived functor of `[G^∨, -]` applied to the
underlying object of `K`. -/
noncomputable def tensorLisseObjIso [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l X) (hG : G.IsLisse) (K : WeilComplex k₀ l X) :
    ((tensorLisse G hG).obj K).obj ≅
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X (G.dual hG).obj).rightDerivedFunctor.obj K.obj :=
  Iso.refl _

/-- The underlying pro-étale Weil sheaf of `[D, F]`. -/
noncomputable def _root_.AlgebraicGeometry.WeilSheaf.ihomObjIso (D : WeilSheaf k₀ l X)
    (hD : D.IsLisse) (F : WeilSheaf k₀ l X) :
    (D.ihom hD F).obj ≅ (ProEtaleWeilSheaf.ihomFunctor k₀ l X D.obj).obj F.obj :=
  Iso.refl _

/-- The cohomology sheaves of the tensor product with a lisse Weil sheaf:
`𝓗ʲ(G ⊗ K) ≅ [G^∨, 𝓗ʲ(K)] = G ⊗ 𝓗ʲ(K)`, the internal hom out of the lisse `G^∨` being exact
(`AlgebraicGeometry.ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor`). -/
noncomputable def homologySheafTensorLisseIso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X)
    (hG : G.IsLisse) (K : WeilComplex k₀ l X) (j : ℤ) :
    (homologySheaf j).obj ((tensorLisse G hG).obj K) ≅
      (G.dual hG).ihom hG.dual ((homologySheaf j).obj K) :=
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (G.dual hG).obj hG.dual
  ObjectProperty.isoMk _ (homologySheafObjIso j _ ≪≫
    (_root_.DerivedCategory.homologyFunctor _ j).mapIso (tensorLisseObjIso G hG K) ≪≫
    ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
      (G.dual hG).obj).rightDerivedFunctorHomologyFunctorIso j).symm.app K.obj ≪≫
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X (G.dual hG).obj).mapIso
      (homologySheafObjIso j K).symm ≪≫
    (WeilSheaf.ihomObjIso _ hG.dual _).symm)

/-- The trace function is multiplicative under the tensor product with a lisse Weil sheaf:
`t_{G ⊗ K} = t_G · t_K`, the local Frobenius on `(G ⊗ K)_x̄ = G_x̄ ⊗ K_x̄` being the tensor
product of the local Frobenius operators. -/
theorem traceFunction_tensorLisse [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l X) (hG : G.IsLisse)
    (K : WeilComplex k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((tensorLisse G hG).obj K).traceFunction n x = G.traceFunction n x * K.traceFunction n x := by
  refine (finsum_congr fun j ↦ ?_).trans (mul_finsum _ _).symm
  rw [WeilSheaf.traceFunction_congr (homologySheafTensorLisseIso G hG K j),
    WeilSheaf.traceFunction_ihom_dual, mul_smul_comm]

end WeilComplex

end AlgebraicGeometry
