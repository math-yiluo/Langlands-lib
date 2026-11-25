/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityConstrainedLift
public import WeilConjectures.WeilSheaf.SmoothPurityEquivarianceDetection

/-! # Reconstruction from finite equivariant isomorphisms

Only existence of an equivariant isomorphism at each finite level is needed. The transition
hypothesis says that ordinary coefficient reduction preserves the Weil equation; it does not
prescribe a canonical orientation at every level.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

set_option hygiene false in
local notation "𝐃₀" => DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
  (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
set_option hygiene false in
local notation "𝐃ₙ(" n ")" => DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
  (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) X))

variable (G : 𝐃₀ ⥤ 𝐃₀) (Gn : ∀ n : ℕ, 𝐃ₙ(n) ⥤ 𝐃ₙ(n))
  (c : ∀ n : ℕ, G ⋙ purityIntegralReduction X ℓ E (n + 1) ≅
    purityIntegralReduction X ℓ E (n + 1) ⋙ Gn n)
  {K L : 𝐃₀} (φK : G.obj K ⟶ K) (φL : G.obj L ⟶ L)

/-- The finite Weil equation with both data transported by the reduction comparison. -/
def PurityReductionWeilCondition (n : ℕ)
    (s : (purityIntegralReduction X ℓ E (n + 1)).obj K ⟶
      (purityIntegralReduction X ℓ E (n + 1)).obj L) : Prop :=
  IsWeilEquivariant (Gn n)
    (transportWeilDatum (purityIntegralReduction X ℓ E (n + 1)) (c n) φK)
    (transportWeilDatum (purityIntegralReduction X ℓ E (n + 1)) (c n) φL) s

/-- Compatible finite equivariant isomorphisms reconstruct an integral equivariant morphism
whose reductions are all isomorphisms. Derived Nakayama can then be applied to the lift. -/
theorem exists_equivariant_forall_isIso_derivedReduction_map
    (hL : derivedCompleteIntegers ℓ E X L)
    [∀ n : ℕ, Finite ((G.obj K) ⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((purityIntegralReduction X ℓ E (n + 1)).obj L))]
    (hfin : ∀ n : ℕ, Finite
      ((purityIntegralReduction X ℓ E (n + 1)).obj K ⟶
        (purityIntegralReduction X ℓ E (n + 1)).obj L))
    (hne : ∀ n : ℕ, ∃ e :
      (purityIntegralReduction X ℓ E (n + 1)).obj K ≅
        (purityIntegralReduction X ℓ E (n + 1)).obj L,
      PurityReductionWeilCondition G Gn c φK φL n e.hom)
    (hstep : ∀ n s, PurityReductionWeilCondition G Gn c φK φL (n + 1) s →
      PurityReductionWeilCondition G Gn c φK φL n (derivedReductionStep (n + 1) s)) :
    ∃ f : K ⟶ L, IsWeilEquivariant G φK φL f ∧
      ∀ n : ℕ, IsIso ((purityIntegralReduction X ℓ E (n + 1)).map f) := by
  have h := exists_forall_isIso_property_derivedReduction_map hL
    (PurityReductionWeilCondition G Gn c φK φL) hfin hne hstep
  obtain ⟨f, hf⟩ := h
  exact ⟨f, isWeilEquivariant_of_purityIntegralReduction G Gn c hL φK φL f
    (fun n ↦ (hf n).2), fun n ↦ (hf n).1⟩

end AlgebraicGeometry.ProEtale
