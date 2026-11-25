/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # The actual chain comparison for native tensor forgetting

Source: total tensor sums and the signed differential, Stacks 06YN and 06YU.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u a va b vb
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

private def curryTensorComparison
    {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
    (T : B ⥤ B ⥤ B) (W : A ⥤ A ⥤ A) (F : B ⥤ A)
    (e : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj W) :
    (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ A).obj F).obj F).obj W :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun Q ↦ e.app (P, Q)) (by
    intro Q Q' g
    simpa using e.hom.naturality (X := (P, Q)) (Y := (P, Q')) (𝟙 P, g))) (by
    intro P P' f
    apply NatTrans.ext
    funext Q
    simpa using e.hom.naturality (X := (P, Q)) (Y := (P', Q)) (f, 𝟙 Q))

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The underived comparison extends to the sum-total tensor, with its prescribed summands.

Source: Stacks 06YN, 06YU; native tensor geometry, step 3.
(blueprint: lem-sf-native-weil-tensor-chain).

Proof: curry the underived natural isomorphism in its two variables. Apply the existing
mapBifunctorComparison to complexes. Forgetting preserves the coproduct in every total degree,
and the component comparisons are isomorphisms, so this chain map is an isomorphism. The defining
coproduct equation gives the displayed summand formula. Its differential equation incorporates
both signed tensor differentials, including the Koszul sign. No flatness or boundedness is needed.
The zero complex and empty sums are covered by the same coproduct universal property. -/
theorem native_weil_tensor_chain
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
    ∃ chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
    ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
            (chain P Q).hom.f n =
        e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n h := by
  let c := curryTensorComparison T
    (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) e
  refine ⟨fun P Q ↦ asIso
    (HomologicalComplex.mapBifunctorComparison c.hom (.up ℤ) P Q), ?_⟩
  intro P Q p q n h
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    c.hom (.up ℤ) P Q p q n h

end AlgebraicGeometry.ProEtaleWeilSheaf
