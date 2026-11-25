/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.WeilEquivariance
public import WeilConjectures.WeilSheaf.SmoothPurityReductionFaithful
public import WeilConjectures.WeilSheaf.SmoothPurityReductionFunctor

/-! # Detecting an integral Weil equation after finite reduction

The finite equations use the Weil data transported by the actual pullback/reduction
comparison. Equality detection retains the shifted-Hom finiteness hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The transported Weil equation is precisely the image of the original equation. -/
lemma purity_map_weil_equation_iff
    {C D : Type*} [Category C] [Category D] {G : C ⥤ C} {G' : D ⥤ D}
    (T : C ⥤ D) (c : G ⋙ T ≅ T ⋙ G') {K L : C}
    (φK : G.obj K ⟶ K) (φL : G.obj L ⟶ L) (f : K ⟶ L) :
    T.map (G.map f ≫ φL) = T.map (φK ≫ f) ↔
      IsWeilEquivariant G' (transportWeilDatum T c φK) (transportWeilDatum T c φL)
        (T.map f) := by
  have hn := c.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  simp only [IsWeilEquivariant, transportWeilDatum, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  exact (cancel_epi (c.inv.app K)).symm

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- Finite equivariance detects integral equivariance when the Milnor obstruction vanishes.
This applies to semilinear scheme automorphisms as well as to morphisms over the base field. -/
theorem isWeilEquivariant_of_purityIntegralReduction
    (G : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (Gn : ∀ n : ℕ, DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) X)))
    (c : ∀ n : ℕ, G ⋙ purityIntegralReduction X ℓ E (n + 1) ≅
      purityIntegralReduction X ℓ E (n + 1) ⋙ Gn n)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    [hfin : ∀ n : ℕ, Finite ((G.obj K) ⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((purityIntegralReduction X ℓ E (n + 1)).obj L))]
    (φK : G.obj K ⟶ K) (φL : G.obj L ⟶ L) (f : K ⟶ L)
    (hf : ∀ n : ℕ, IsWeilEquivariant (Gn n)
      (transportWeilDatum (purityIntegralReduction X ℓ E (n + 1)) (c n) φK)
      (transportWeilDatum (purityIntegralReduction X ℓ E (n + 1)) (c n) φL)
      ((purityIntegralReduction X ℓ E (n + 1)).map f)) :
    IsWeilEquivariant G φK φL f := by
  apply @eq_of_derivedReduction_map_eq X ℓ _ E _ _ (G.obj K) L hL hfin
  intro n
  exact (purity_map_weil_equation_iff (purityIntegralReduction X ℓ E (n + 1))
    (c n) φK φL f).mpr (hf n)

end AlgebraicGeometry.ProEtale
