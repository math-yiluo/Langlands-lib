/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarGeometricPullComposition

set_option linter.privateModule false

/-! Pullback-compositor transport for the open projection coefficient square.
(blueprint: lem-sf-open-projection-factor-compositor-transport).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  reductionDerivedChange completedAdicDerivedChange presheafToSheaf
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] scalarTensor scalarPull openComparison
  proEtaleCanonicalTensorComparison geometricPullComposition

private theorem openProjectionInverse_naturality (R : Coefficients.{u})
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    {M M' : DerivedCategory (pbcModules U (R.ring U))}
    {N N' : DerivedCategory (pbcModules V (R.ring V))} (f : M ⟶ M') (g : N ⟶ N') :
    (openExtension R j).mapDerivedCategory.map
        (a.tensor.map (Prod.mkHom f ((pull R j).map g))) ≫
      openProjectionInverse R j a b M' N' =
    openProjectionInverse R j a b M N ≫
      b.tensor.map (Prod.mkHom ((openExtension R j).mapDerivedCategory.map f) g) := by
  let J := (openExtension R j).mapDerivedCategory
  let P := pull R j
  let adj := openDerivedAdjunction R j
  let e := proEtaleCanonicalTensorComparison j (R.ring V) (R.ring U) (R.pull j) b a
  apply adj.homEquiv_naturality_right_square
  change a.tensor.map (Prod.mkHom f (P.map g)) ≫
      (a.tensor.map (Prod.mkHom (adj.unit.app M') (𝟙 _)) ≫ e.inv.app (J.obj M', N')) =
    (a.tensor.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ e.inv.app (J.obj M, N)) ≫
      P.map (b.tensor.map (Prod.mkHom (J.map f) g))
  have hn : Prod.mkHom f (P.map g) ≫ Prod.mkHom (adj.unit.app M') (𝟙 _) =
      Prod.mkHom (adj.unit.app M) (𝟙 _) ≫ (P.prod P).map (Prod.mkHom (J.map f) g) := by
    ext
    · exact adj.unit.naturality f
    · simp
  rw [← Category.assoc, ← a.tensor.map_comp, hn, a.tensor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact e.inv.naturality (Prod.mkHom (J.map f) g)

end WeilConjectures.PurCompactSupport
