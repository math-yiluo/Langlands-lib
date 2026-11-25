/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionTowerComponents
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Internal Hom comparison of the augmented reduction towers

Source: blueprint order 2478, proof steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-augmented-tower-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

attribute [local implicit_reducible] completedIntegralCoefficientSheaf
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingSheaf CategoryTheory.sheafCompose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- Hom identifies the actual augmented towers, before imposing any completeness
condition or taking any product. The isomorphism includes every transition map,
and its displayed equation includes each canonical augmentation.

Source: blueprint order 2478, steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-augmented-tower-comparison).

Proof: Choose a complex G' representing Hom(K,Q(G)) and a flat-term K-flat
resolution q' of G'. For each positive exponent use models_exist and
comparison_isIso. The coefficient extension/restriction adjunction identifies
restricted finite Hom with Hom(K,Res(N)); its Hom bijections are tensor-Hom
adjunction followed by the normalized coefficient tensor comparison. Composing
with the finite comparison and the canonical resolution computations gives an
isomorphism Hom(K,F_n) to F'_n. The finite signed chain comparison is natural
in the two-term quotient complex. Its naturality with the quotient maps gives
commutation with consecutive transitions, hence with every arrow of the tower.
Naturality with the degree-zero quotient unit, using the scalar unit x maps to
1 tensor x and the evaluation normalization, gives exactly the augmentation
equation below. Assemble the components by NatIso.ofComponents. Independence
of resolutions transports the equations from the chosen K-flat and K-injective
models to q and q'. This argument uses neither products nor completeness. -/
theorem augmentedTower_comparison
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
    let H := (Functor.curry.obj
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)
    ∃ (P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
      (q' : P' ⟶ G')
      (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
        (R := completedIntegralCommRingSheaf l E Y D hl) q')
      (e : DerivedCategory.Q.obj G' ≅ H.obj (DerivedCategory.Q.obj G))
      (τ : integralReductionTower l E Y D hl P ⋙ H ≅
        integralReductionTower l E Y D hl P'),
      ∀ n : ℕ, e.inv ≫ (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) =
        H.map ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
          τ.hom.app (op n) := by
  classical
  let H := (Functor.curry.obj
    (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)
  let G' := DerivedCategory.Q.objPreimage (H.obj (DerivedCategory.Q.obj G))
  let e : DerivedCategory.Q.obj G' ≅ H.obj (DerivedCategory.Q.obj G) :=
    DerivedCategory.Q.objObjPreimageIso _
  obtain ⟨P', q', hflat, _, hqi, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G'
  have hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q' := ⟨hqi, hflat⟩
  obtain ⟨θ, hθ, hunit⟩ := reductionTower_components l E Y D hl K P G P' G' q q' hq hq' e
  let τ₀ : integralReductionTower l E Y D hl P ⋙ H ⟶
      integralReductionTower l E Y D hl P' :=
    NatTrans.ofOpSequence (fun n ↦ (θ n).hom) hθ
  have : ∀ X, IsIso (τ₀.app X) := fun X ↦ by
    change IsIso (θ X.unop).hom
    infer_instance
  have : IsIso τ₀ := NatIso.isIso_of_isIso_app τ₀
  exact ⟨P', G', q', hq', e, asIso τ₀, hunit⟩

end WeilConjectures.IntegralHom
