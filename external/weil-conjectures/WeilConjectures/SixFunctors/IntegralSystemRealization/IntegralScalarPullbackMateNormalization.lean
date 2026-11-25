/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Scalar restriction and the derived pullback mate

Source: Stacks Tags 0D6E and 0D6J, with the exact-pullback adjunction normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
attribute [local instance] normalizedDVRModuleRes_limits normalizedDVRModuleRes_colimits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section ExactAdjunction
variable {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [Abelian.HasKInjectiveResolutions B]
  {L : A ⥤ B} {G : B ⥤ A} [L.Additive] [G.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private theorem scalar_unit_model (adj : L ⊣ G) (P : CochainComplex A ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        G.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient A (.up ℤ)).obj P)
  change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    G.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app _) = _ at h
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient,
    quotient_hom_id, quotient_inv_id, homotopyFactors_inv_id,
    Functor.map_comp] at h
  erw [L.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    G.rightDerivedFunctor.map_id, G.rightDerivedFunctor.map_id] at h
  simp only [Category.id_comp, Category.comp_id] at h
  unfold Functor.rightDerivedFunctorUnitQ
  rw [quotient_hom_id, quotient_inv_id]
  erw [G.rightDerivedFunctor.map_id]
  erw [Category.id_comp, Category.comp_id]
  convert h using 1 <;> rfl

private theorem scalar_hom_model (adj : L ⊣ G)
    (P : CochainComplex A ℤ) (K : CochainComplex B ℤ)
    (t : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (L.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _ t) ≫
        G.rightDerivedFunctorUnitQ K := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, scalar_unit_model]
  rw [Category.assoc, ← G.rightDerivedFunctorUnitQ_naturality t,
    ← DerivedCategory.Q.map_comp_assoc]
  rfl

end ExactAdjunction

section MateModel
variable {A B C D : Type a}
  [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
  {L : A ⥤ B} {G : B ⥤ A} {L' : C ⥤ D} {G' : D ⥤ C}
  {S : A ⥤ C} {T : B ⥤ D}
  [L.Additive] [G.Additive] [L'.Additive] [G'.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

private theorem inverse_mate_model (adj : L ⊣ G) (adj' : L' ⊣ G')
    (c : G ⋙ S ⟶ T ⋙ G')
    (b : G.rightDerivedFunctor ⋙ S.mapDerivedCategory ⟶
      T.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (hb : ∀ K : CochainComplex B ℤ,
      S.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ K) ≫
          b.app (DerivedCategory.Q.obj K) ≫
          G'.rightDerivedFunctor.map (T.mapDerivedCategoryFactors.hom.app K) =
        S.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app K) ≫
          G'.rightDerivedFunctorUnitQ ((T.mapHomologicalComplex (.up ℤ)).obj K))
    (P : CochainComplex A ℤ) :
    ((mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction).symm
        (TwoSquare.mk _ _ _ _ b)).app (DerivedCategory.Q.obj P) ≫
        T.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
        T.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      L'.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app P) ≫
        L'.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ c))
            (.up ℤ)).app P) := by
  let δ := ((mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction).symm
    (TwoSquare.mk _ _ _ _ b))
  let δ₀ := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ c))
  let Pc := (L.mapHomologicalComplex (.up ℤ)).obj P
  let t := (NatTrans.mapHomologicalComplex δ₀ (.up ℤ)).app P
  have ho : (adj'.mapHomologicalComplex (.up ℤ)).homEquiv
      ((S.mapHomologicalComplex (.up ℤ)).obj P)
      ((T.mapHomologicalComplex (.up ℤ)).obj Pc) t =
      (S.mapHomologicalComplex (.up ℤ)).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        (NatTrans.mapHomologicalComplex c (.up ℤ)).app Pc := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ c) (P.X i)).symm
  change δ.app (DerivedCategory.Q.obj P) ≫
      T.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      T.mapDerivedCategoryFactors.hom.app Pc =
    L'.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app P) ≫
      L'.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map t
  apply (adj'.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).injective
  have hhom := scalar_hom_model adj'
    ((S.mapHomologicalComplex (.up ℤ)).obj P)
    ((T.mapHomologicalComplex (.up ℤ)).obj Pc) t
  rw [Adjunction.homEquiv_naturality_left]
  erw [hhom]
  rw [ho]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hu := unit_mateEquiv_symm adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ b)
    (DerivedCategory.Q.obj P)
  change S.mapDerivedCategory.map
        (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P)) ≫
      b.app (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
    adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
        (S.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      G'.rightDerivedFunctor.map (δ.app (DerivedCategory.Q.obj P)) at hu
  rw [← reassoc_of% hu]
  have hn := b.naturality (L.mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← S.mapDerivedCategory.map_comp_assoc, scalar_unit_model]
  rw [S.mapDerivedCategory.map_comp, Category.assoc, hb Pc]
  have hs := S.mapDerivedCategoryFactors.hom.naturality
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)
  dsimp only [Functor.comp_map] at hs
  rw [reassoc_of% hs]

private theorem transport_unit
    {S₀ : A ⥤ C} {T₀ : B ⥤ D}
    [S₀.Additive] [T₀.Additive]
    [PreservesFiniteLimits S₀] [PreservesFiniteColimits S₀]
    [PreservesFiniteLimits T₀] [PreservesFiniteColimits T₀]
    (c₀ : T₀ ⋙ G' ≅ G ⋙ S₀)
    (b₀ : T₀.mapDerivedCategory ⋙ G'.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ S₀.mapDerivedCategory)
    (h₀ : ∀ K : CochainComplex B ℤ,
      S₀.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ K) ≫
          b₀.inv.app (DerivedCategory.Q.obj K) ≫
          G'.rightDerivedFunctor.map (T₀.mapDerivedCategoryFactors.hom.app K) =
        S₀.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.inv (.up ℤ)).app K) ≫
          G'.rightDerivedFunctorUnitQ ((T₀.mapHomologicalComplex (.up ℤ)).obj K))
    (hS : S = S₀) (hT : T = T₀)
    (c : T ⋙ G' ≅ G ⋙ S) (hc : HEq c c₀)
    (b : T.mapDerivedCategory ⋙ G'.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ S.mapDerivedCategory) (hb : HEq b b₀) :
    ∀ K : CochainComplex B ℤ,
      S.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ K) ≫
          b.inv.app (DerivedCategory.Q.obj K) ≫
          G'.rightDerivedFunctor.map (T.mapDerivedCategoryFactors.hom.app K) =
        S.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.inv (.up ℤ)).app K) ≫
          G'.rightDerivedFunctorUnitQ ((T.mapHomologicalComplex (.up ℤ)).obj K) := by
  subst S
  subst T
  cases eq_of_heq hc
  cases eq_of_heq hb
  exact h₀

end MateModel

/-- The inverse mate of the fixed derived scalar comparison is the localization
of the ordinary inverse mate. This assertion involves one finite coefficient
module complex, and no coefficient system or evaluation transition.
Source: Stacks 0D6E and 0D6J; Zheng Lemma 4.10
(blueprint: lem-sf-integral-scalar-pullback-mate-normalization).

Proof: apply the derived adjunction Hom bijection to the desired equation.
The exact-localization factor and the right-derived unit express the transpose
of a cochain map as the localization of its ordinary transpose followed by
that unit. This follows from derivedη_fac_app at the homotopy quotient.
The ordinary inverse-mate unit identity computes its transpose. The derived
inverse-mate unit identity and naturality move the low-level localization
factor past the specified derived direct-image comparison. Its all-complex
unit equation is compactSupportScalarDirectNormalization, which was proved
using K-injective resolutions without asserting that scalar restriction
preserves K-injectivity. Finally, naturality of the restriction localization
factor identifies the two transposes. Injectivity gives the result. The
hypotheses hr₀ and hr transport the equal quotient-restriction presentations.
Zero complexes and n = 0 require no separate hypotheses. -/
theorem integralScalarPullback_mateNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr₀ : HEq r₀ (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm)
    (r : normalizedDVRRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRRes l E Y (Nat.le_succ n))
    (hr : HEq r
      (sfDerivedImageRestriction f (Padic.coefficientExtensionTransition l E (n + 1))))
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    ((mateEquiv (finiteAdj l E f n) (finiteAdj l E f (n + 1))).symm
        (TwoSquare.mk _ _ _ _ r.inv)).app (DerivedCategory.Q.obj P) ≫
      (normalizedDVRRes l E X (Nat.le_succ n)).map
        ((Functor.mapDerivedCategoryFactors
          (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)).hom.app P) ≫
      (normalizedDVRModuleRes l E X (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app
        (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
          (.up ℤ)).obj P) =
    (finiteDerivedPullback l E (n + 1) f).map
        ((normalizedDVRModuleRes l E Y (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app P) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 2)) f).mapDerivedCategoryFactors.hom.app
        (((normalizedDVRModuleRes l E Y (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          ((mateEquiv
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
            (sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (n + 2)))).symm
          (TwoSquare.mk _ _ _ _ r₀.inv)) (.up ℤ)).app P) := by
  let := normalizedDVRModuleRes_limits l E X (Nat.le_succ n)
  let := normalizedDVRModuleRes_colimits l E X (Nat.le_succ n)
  let := normalizedDVRModuleRes_limits l E Y (Nat.le_succ n)
  let := normalizedDVRModuleRes_colimits l E Y (Nat.le_succ n)
  apply inverse_mate_model
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2))) r₀.inv r.inv
  have h := compactSupportScalarDirectNormalization f
    (Padic.coefficientExtensionTransition l E (n + 1))
  unfold CategoryTheory.ExactDerivedSquare.unitNormalized at h
  exact transport_unit
    (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm
    (sfDerivedImageRestriction f (Padic.coefficientExtensionTransition l E (n + 1))) h
    (originRestrictionEquality l E Y n).symm (originRestrictionEquality l E X n).symm
    r₀ hr₀ r hr

end WeilConjectures.IntegralSystemRealization
