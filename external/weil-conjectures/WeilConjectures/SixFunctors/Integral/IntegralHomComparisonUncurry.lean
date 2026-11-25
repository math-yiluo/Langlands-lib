/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralHomReductionComparison
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorExchangeNaturality
import WeilConjectures.SixFunctors.IntegralHom.Scalar.IntegralHomScalarTensorExchangeRepresentatives
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

/-! # Uncurried normalization of integral Hom comparison

The equality of uncurried maps is the representative-level normalization step in the
independence proof for integral Hom comparison maps.
(blueprint: lem-sfb-integral-hom-comparison-uncurry)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe d u
open CategoryTheory Opposite
namespace WeilConjectures

private theorem exchange_naturality
    {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) (b : HomReductionTensorModel R)
    (K K' A A' : IntegralHom.Derived.{u, u} X R) (f : K ⟶ K') (g : A ⟶ A') :
    a.tensor.map (Prod.mkHom (f) (g)) ≫ IntegralHom.tensorAdjunctionExchange.{u} R a b K' A' =
      IntegralHom.tensorAdjunctionExchange.{u} R a b K A ≫ b.tensor.map (Prod.mkHom (g) (f)) := by
  have ha : a.tensor.map (Prod.mkHom (f) (g)) =
      a.tensor.map (Prod.mkHom (f) (𝟙 A)) ≫ a.tensor.map (Prod.mkHom (𝟙 K') (g)) := by
    rw [← Functor.map_comp]
    simp
  have hb : b.tensor.map (Prod.mkHom (g) (f)) =
      b.tensor.map (Prod.mkHom (𝟙 A) (f)) ≫ b.tensor.map (Prod.mkHom (g) (𝟙 K')) := by
    rw [← Functor.map_comp]
    simp
  rw [ha, Category.assoc,
    IntegralHom.tensorAdjunctionExchange_naturality_second,
    ← Category.assoc, IntegralHom.tensorAdjunctionExchange_naturality_first,
    Category.assoc, ← hb]

attribute [-instance] IntegralHom.derivedCategory in
private theorem flat_representative
    {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (K : IntegralHom.Derived.{u, u} X R) :
    ∃ P : CochainComplex (homReductionModules R) ℤ,
      IntegralHom.flat.{u, u} X R P ∧
        Nonempty
          ((DerivedCategory.Q.{u + 2, u + 1, u + 2}
            (C := homReductionModules R)).obj P ≅ K) := by
  classical
  let : HasDerivedCategory.{u + 2} (homReductionModules R) :=
    HasDerivedCategory.standard _
  let Q : CochainComplex (homReductionModules R) ℤ ⥤
      IntegralHom.Derived.{u, u} X R := DerivedCategory.Q
  let G := Q.objPreimage K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (J := AlgebraicGeometry.Scheme.ProEt.topology X) (R := R) G
  have : IsIso (Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso.{u + 2, u + 1, u + 2}
      (homReductionModules R) p).2 hp
  exact ⟨P, hP, ⟨asIso (Q.map p) ≪≫
    Q.objObjPreimageIso K⟩⟩

attribute [-instance] IntegralHom.derivedCategory in
private theorem scalar_exchange
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (b : IntegralHomReductionTensorData D l hl E X n)
    (K A : completedIntegralDerivedCategory l E X D hl) :
    IntegralHom.tensorAdjunctionExchange.{u} (integralCoefficientCommRingSheaf l E X n)
        m.target b.target
        ((integralDerivedReduction l E X D hl n).obj K)
        ((integralDerivedReduction l E X D hl n).obj A) ≫
      b.tensor.inv.app (A, K) =
    m.mu.inv.app (K, A) ≫ (integralDerivedReduction l E X D hl n).map
      (IntegralHom.tensorAdjunctionExchange.{u} (completedIntegralCommRingSheaf l E X D hl)
        a b.source K A) := by
  let F := integralDerivedReduction l E X D hl n
  let R := completedIntegralCommRingSheaf l E X D hl
  let S := integralCoefficientCommRingSheaf l E X n
  let loc : CochainComplex (homReductionModules R) ℤ ⥤
      IntegralHom.Derived.{u, u} X R := DerivedCategory.Q
  obtain ⟨P, hP, ⟨eP⟩⟩ := flat_representative R K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := flat_representative R A
  have hn := exchange_naturality S m.target b.target
    (F.obj (loc.obj P)) (F.obj K)
    (F.obj (loc.obj Q)) (F.obj A) (F.map eP.hom) (F.map eQ.hom)
  have hs := exchange_naturality R a b.source
    (loc.obj P) K (loc.obj Q) A eP.hom eQ.hom
  have ht := b.tensor.inv.naturality (Prod.mkHom (eQ.hom) (eP.hom))
  have hm := m.mu.inv.naturality (Prod.mkHom (eP.hom) (eQ.hom))
  change b.target.tensor.map (Prod.mkHom (F.map eQ.hom) (F.map eP.hom)) ≫ b.tensor.inv.app (A, K) =
    b.tensor.inv.app (loc.obj Q, loc.obj P) ≫
      F.map (b.source.tensor.map (Prod.mkHom (eQ.hom) (eP.hom))) at ht
  change m.target.tensor.map (Prod.mkHom (F.map eP.hom) (F.map eQ.hom)) ≫ m.mu.inv.app (K, A) =
    m.mu.inv.app (loc.obj P, loc.obj Q) ≫
      F.map (a.tensor.map (Prod.mkHom (eP.hom) (eQ.hom))) at hm
  have hrep := IntegralHom.scalarTensorExchange_representatives
    D l hl E X n a m b P Q hP hQ
  have htail :
      m.mu.inv.app (loc.obj P, loc.obj Q) ≫
          F.map (IntegralHom.tensorAdjunctionExchange R a b.source (loc.obj P) (loc.obj Q)) ≫
          F.map (b.source.tensor.map (Prod.mkHom eQ.hom eP.hom)) =
        m.target.tensor.map (Prod.mkHom (F.map eP.hom) (F.map eQ.hom)) ≫
          m.mu.inv.app (K, A) ≫ F.map (IntegralHom.tensorAdjunctionExchange R a b.source K A) := by
    with_unfolding_all
      erw [← F.map_comp, ← hs, F.map_comp, ← Category.assoc, ← hm, Category.assoc]
  have : IsIso (Prod.mkHom (F.map eP.hom) (F.map eQ.hom)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (m.target.tensor.map (Prod.mkHom (F.map eP.hom) (F.map eQ.hom)))).1
  simp only [← Category.assoc]
  rw [hn]
  simp only [Category.assoc]
  rw [ht]
  simp only [← Category.assoc]
  rw [hrep]
  with_unfolding_all
    simpa only [Category.assoc] using htail

/-- The canonical comparison has the normalized uncurried map prescribed by any
`ReductionPresentation`.  This is the representative normalization part of the
comparison-independence argument; it is proved by comparing the two tensor models on
K-flat representatives, using the signed total tensor and the normalized evaluation.
Source: Stacks Tags 06YY and 08J7; the normalization paragraphs of the integral Hom
reduction construction (blueprint: lem-sfb-integral-hom-comparison-uncurry).
-/
theorem integralHomComparison_uncurry_eq
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (K L : completedIntegralDerivedCategory l E X D hl) :
    ((m.target.adjunction
      ((integralDerivedReduction l E X D hl n).obj K)).homEquiv _ _).symm
      (integralHomReductionComparison D l hl E X n K L) =
      m.mu.inv.app
          (K,
            (homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)) ≫
        (integralDerivedReduction l E X D hl n).map
          ((a.adjunction K).counit.app L) := by
  let b := (integralHomReductionTensorData_exists D l hl E X n).some
  let F := integralDerivedReduction l E X D hl n
  let H := (homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)
  change ((m.target.adjunction (F.obj K)).homEquiv (F.obj H) (F.obj L)).symm
    ((b.target.curry (F.obj H) (F.obj K) (F.obj L)).symm
      (b.tensor.inv.app (H, K) ≫ F.map (b.source.curry H K L (𝟙 _)))) = _
  rw [IntegralHom.tensorAdjunctionExchange_uncurry,
    Equiv.apply_symm_apply, ← Category.assoc, scalar_exchange D l hl E X n a m b]
  rw [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun f : a.tensor.obj (K, H) ⟶ L => m.mu.inv.app (K, H) ≫ F.map f)
    (IntegralHom.tensorAdjunctionExchange_evaluation.{u}
      (completedIntegralCommRingSheaf l E X D hl) a b.source K L)

end WeilConjectures
