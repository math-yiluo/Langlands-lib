/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.SixFunctors.Sf.SfClopenScalarQuotientComparison
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Exact open restriction of the strict finite pullback tower

Source: Stacks Project, sites-modules.tex, Tags 03D2 and 03D8.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

set_option backward.defeqAttrib.useBackward true
set_option allowUnsafeReducibility true
attribute [local reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.finite
  IntegralOnSlice.projection
  integralCoefficientCommRingSheaf integralCoefficientSheaf CategoryTheory.constantSheaf
  CategoryTheory.Functor.sheafPushforwardContinuous

private theorem reduction_map_tensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (n : ℕ) {M N : integralTowerModules l E V} (a : M ⟶ N)
    (W : V.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E V n).obj.obj W)
    (x : M.val.obj W) :
    ((unrestrictedIntegralReductionFunctor l E V n).map a).val.app W
        (unrestrictedIntegralTensorSection l E V n M W s x) =
      unrestrictedIntegralTensorSection l E V n N W s (a.val.app W x) := by
  exact IntegralOnSlice.generator_map.{u, u} l E V none n a W s x

/-- The clopen scalar quotient comparisons form a natural strict tower isomorphism.

Source: Stacks Project, sites-modules.tex, Tags 03D8 and 03EL.
(blueprint: lem-sf-clopen-scalar-quotient-tower).

Proof: use the existing finite quotient comparison and its pure tensor formula.
After composing with its inverse, equality of maps can be checked on local pure
tensors. The quotient transition formula and the finite coefficient transition
compatibility give the transition square. The scalar extension map formula gives
naturality in the input complex. NatTrans.ofOpSequence assembles the transition
squares, and componentwise invertibility gives the natural tower isomorphism.
These generator calculations apply also to empty clopens and zero complexes. -/
theorem clopenScalarQuotientTower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (U : T.Opens) (hU : IsClosed (U : Set T))
    (d : SfClopenCoefficientRestriction l E T U) :
    Nonempty ((Functor.ofOpSequence (unrestrictedIntegralTransition l E T)).flip ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfClopenComplexRestriction d) ≅
      sfClopenComplexRestriction d ⋙
        (Functor.ofOpSequence (unrestrictedIntegralTransition l E U.toScheme)).flip) := by
  obtain ⟨_, _, quotient, _, _, hquotient⟩ :=
    sf_clopen_scalar_quotient_comparison l E T U hU d
  have hinv (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) (q : ℤ)
      (V : U.toScheme.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj V)
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V.unop))) :
      ((quotient P n).inv.f q).val.app V
          (unrestrictedTowerTensorSection l E U.toScheme n
            (((sfClopenComplexRestriction d).obj P).X q) V s x) =
        unrestrictedTowerTensorSection l E T n (P.X q)
          (op ((sfClopenSiteInclusion U).obj V.unop))
          ((d.finite n).hom.hom.app V s) x := by
    have h := congrArg (((quotient P n).inv.f q).val.app V)
      (hquotient P n q V.unop s x)
    have hid := congrArg
      (fun f ↦ ((f.f q).val.app V)
        (unrestrictedTowerTensorSection l E T n (P.X q)
          (op ((sfClopenSiteInclusion U).obj V.unop))
          ((d.finite n).hom.hom.app V s) x)) (quotient P n).hom_inv_id
    exact h.symm.trans hid
  have step (W : Scheme.{u})
      (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (q : ℤ)
      (V : W.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf l E W (n + 1)).obj.obj V)
      (x : (P.X q).val.obj V) :
      ((unrestrictedTowerTransition l E W P n).f q).val.app V
          (unrestrictedTowerTensorSection l E W (n + 1) (P.X q) V s x) =
        unrestrictedTowerTensorSection l E W n (P.X q) V
          ((integralCoefficientSheafTransition l E W n).hom.app V s) x :=
    (unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec P q V s x
  have htransition (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenComplexRestriction d).map (unrestrictedTowerTransition l E T P n) ≫
          (quotient P n).hom =
        (quotient P (n + 1)).hom ≫
          unrestrictedTowerTransition l E U.toScheme ((sfClopenComplexRestriction d).obj P) n := by
    apply (cancel_epi (quotient P (n + 1)).inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply HomologicalComplex.hom_ext
    intro q
    apply unrestrictedReduction_hom_ext l E U.toScheme (n + 1)
    intro V s x
    change ((quotient P n).hom.f q).val.app V
        (((unrestrictedTowerTransition l E T P n).f q).val.app
          (op ((sfClopenSiteInclusion U).obj V.unop))
          (((quotient P (n + 1)).inv.f q).val.app V
            (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
              (((sfClopenComplexRestriction d).obj P).X q) V s x))) =
      ((unrestrictedTowerTransition l E U.toScheme
        ((sfClopenComplexRestriction d).obj P) n).f q).val.app V
          (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
            (((sfClopenComplexRestriction d).obj P).X q) V s x)
    rw [hinv, step, step]
    have hcoeff :
        (integralCoefficientSheafTransition l E T n).hom.app
            (op ((sfClopenSiteInclusion U).obj V.unop))
            ((d.finite (n + 1)).hom.hom.app V s) =
          (d.finite n).hom.hom.app V
            ((integralCoefficientSheafTransition l E U.toScheme n).hom.app V s) :=
      congrArg (fun f ↦ (f.hom.app V).hom s) (d.transition n)
    rw [hcoeff]
    exact hquotient P n q V.unop
      ((integralCoefficientSheafTransition l E U.toScheme n).hom.app V s) x
  have hnatural {P Q : CochainComplex (scalarReductionSource l E T) ℤ}
      (f : P ⟶ Q) (n : ℕ) :
      (sfClopenComplexRestriction d).map ((unrestrictedIntegralComplexFunctor l E T n).map f) ≫
          (quotient Q n).hom =
        (quotient P n).hom ≫ (unrestrictedIntegralComplexFunctor l E U.toScheme n).map
          ((sfClopenComplexRestriction d).map f) := by
    apply (cancel_epi (quotient P n).inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply HomologicalComplex.hom_ext
    intro q
    apply unrestrictedReduction_hom_ext l E U.toScheme n
    intro V s x
    change ((quotient Q n).hom.f q).val.app V
        (((unrestrictedIntegralReductionFunctor l E T n).map (f.f q)).val.app
          (op ((sfClopenSiteInclusion U).obj V.unop))
          (((quotient P n).inv.f q).val.app V
            (unrestrictedTowerTensorSection l E U.toScheme n
              (((sfClopenComplexRestriction d).obj P).X q) V s x))) =
      ((unrestrictedIntegralReductionFunctor l E U.toScheme n).map
        (((sfClopenComplexRestriction d).map f).f q)).val.app V
          (unrestrictedTowerTensorSection l E U.toScheme n
            (((sfClopenComplexRestriction d).obj P).X q) V s x)
    rw [hinv]
    dsimp only [unrestrictedTowerTensorSection]
    rw [reduction_map_tensor, reduction_map_tensor]
    exact hquotient Q n q V.unop s ((f.f q).val.app
      (op ((sfClopenSiteInclusion U).obj V.unop)) x)
  let T₁ := (Functor.ofOpSequence (unrestrictedIntegralTransition l E T)).flip
  let T₂ := (Functor.ofOpSequence (unrestrictedIntegralTransition l E U.toScheme)).flip
  let a (P : CochainComplex (scalarReductionSource l E T) ℤ) :
      T₁.obj P ⋙ sfClopenComplexRestriction d ⟶
        T₂.obj ((sfClopenComplexRestriction d).obj P) :=
    NatTrans.ofOpSequence (fun n ↦ (quotient P n).hom) (by
      intro n
      simpa only [T₁, T₂, Functor.comp_map, Functor.flip_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ, unrestrictedTowerTransition] using htransition P n)
  let e (P : CochainComplex (scalarReductionSource l E T) ℤ) :
      T₁.obj P ⋙ sfClopenComplexRestriction d ≅
        T₂.obj ((sfClopenComplexRestriction d).obj P) :=
    NatIso.ofComponents (fun n ↦ quotient P n.unop) (by
      intro i j f
      exact (a P).naturality f)
  exact ⟨NatIso.ofComponents e (by
    intro P Q f
    apply NatTrans.ext
    funext n
    exact hnatural f n.unop)⟩

end WeilConjectures
